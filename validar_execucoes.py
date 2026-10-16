import argparse
import ast
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import tempfile

ROOT = Path(__file__).resolve().parent
DATA = frozenset()
CHECK_FIELDS = {'checks', 'kernel_checks', 'adversarial_checks', 'results', 'resultados'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_name(path, root=ROOT):
    return os.path.relpath(path.resolve(), root.resolve())


def reports(text):
    decoder = json.JSONDecoder()
    result = []
    position = 0
    while position < len(text):
        start = text.find('{', position)
        if start < 0:
            break
        try:
            value, end = decoder.raw_decode(text[start:])
            if isinstance(value, dict):
                result.append(value)
            position = start + end
        except json.JSONDecodeError:
            position = start + 1
    return result


def failures(value, context=None):
    if isinstance(value, dict):
        for key, item in value.items():
            if key in {'passed', 'aprovado'} and item is not True:
                return True
            if key in {'error', 'erro', 'errors', 'erros', 'failed', 'failure'} and item:
                return True
            if key.startswith('general_') and key.endswith('_complete') and item is not True:
                return True
            if failures(item, key if key in CHECK_FIELDS else context):
                return True
    elif isinstance(value, list):
        return any(failures(item, context) for item in value)
    elif context in CHECK_FIELDS and value is False:
        return True
    return False


def check_count(value):
    if isinstance(value, bool):
        return 1 if value else 0
    if isinstance(value, int):
        return max(value, 0)
    if isinstance(value, list):
        return sum(1 for item in value if isinstance(item, str) and bool(item) or
                   isinstance(item, dict) and item.get('passed') is True)
    if isinstance(value, dict):
        return sum(1 for item in value.values() if item is True or
                   isinstance(item, dict) and item.get('passed') is True)
    return 0


def execution_errors(suffix, status, text):
    errors = []
    parsed = reports(text)
    if status != 0:
        errors.append('codigo_saida_nao_zero')
    if re.search(r'\b(?:sorryAx|admit|unsafeCast)\b|declaration uses .sorry.|\berror:', text, re.I):
        errors.append('diagnostico_de_prova_invalida')
    if suffix == '.lean':
        return errors, parsed
    if failures(parsed):
        errors.append('relatorio_contem_falha')
    if not parsed:
        errors.append('relatorio_final_ausente')
        return errors, parsed
    final = parsed[-1]
    count = max((check_count(final.get(key)) for key in CHECK_FIELDS), default=0)
    explicit = final.get('passed') is True or final.get('aprovado') is True
    structured = any(check_count(final.get(key)) > 0 and isinstance(final.get(key), (list, dict))
                     for key in CHECK_FIELDS)
    if count == 0 or not (explicit or structured):
        errors.append('relatorio_final_sem_verificacoes_positivas')
    for key in CHECK_FIELDS:
        values = final.get(key)
        if isinstance(values, list) and (not values or check_count(values) != len(values)):
            errors.append('lista_de_verificacoes_incompleta')
        if isinstance(values, dict) and (not values or check_count(values) != len(values)):
            errors.append('mapa_de_verificacoes_incompleto')
    if isinstance(final.get('checks'), int) and not isinstance(final['checks'], bool):
        if final['checks'] <= 0:
            errors.append('nenhuma_verificacao_executada')
        if isinstance(final.get('results'), list) and len(final['results']) > final['checks']:
            errors.append('contagem_de_verificacoes_inconsistente')
    return sorted(set(errors)), parsed


def lean_admissions(path):
    text = path.read_text()
    return bool(re.search(r'\b(?:sorry|admit|axiom|unsafe|unsafeCast)\b', text))


def module_file(module, path, root, suffix='.py', level=0, search_paths=None):
    relative = Path(*module.split('.')) if module else Path()
    if level:
        base = path.parent
        for _ in range(level - 1):
            base = base.parent
        bases = [base]
    elif search_paths is not None:
        bases = search_paths
    else:
        bases = [root, path.parent] if module.startswith('capitulo_') else [path.parent, root]
    for base in bases:
        for candidate in (base / relative / '__init__.py', base / relative.with_suffix(suffix)):
            if candidate.is_file():
                return candidate.resolve()
    if module.startswith('capitulo_') or level:
        raise ValueError('Import local ausente: ' + module)
    return None



def python_path_value(node, path, values):
    if isinstance(node, ast.Constant) and isinstance(node.value, (str, int)):
        return node.value
    if isinstance(node, ast.Name):
        if node.id == '__file__':
            return str(path.resolve())
        if node.id in values:
            return values[node.id]
    if isinstance(node, ast.Call) and not node.keywords:
        if isinstance(node.func, ast.Name) and node.func.id in {'Path', 'str'} and len(node.args) == 1:
            value = python_path_value(node.args[0], path, values)
            return Path(value) if node.func.id == 'Path' else str(value)
        if isinstance(node.func, ast.Attribute) and node.func.attr == 'resolve' and not node.args:
            value = python_path_value(node.func.value, path, values)
            if isinstance(value, Path) and value.is_absolute():
                return value.resolve()
    if isinstance(node, ast.Attribute):
        value = python_path_value(node.value, path, values)
        if isinstance(value, Path) and node.attr in {'parent', 'parents'}:
            return value.parent if node.attr == 'parent' else tuple(value.parents)
    if isinstance(node, ast.Subscript):
        value = python_path_value(node.value, path, values)
        index = python_path_value(node.slice, path, values)
        if isinstance(value, tuple) and isinstance(index, int):
            return value[index]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
        left = python_path_value(node.left, path, values)
        right = python_path_value(node.right, path, values)
        if isinstance(left, Path) and isinstance(right, str):
            return left / right
    raise ValueError('Caminho Python não resolvido estaticamente: ' + ast.unparse(node))


def python_dependencies(source, path, root):
    result = set()
    tree = ast.parse(source)
    parents = {child: node for node in ast.walk(tree) for child in ast.iter_child_nodes(node)}
    sys_names = {'sys'}
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            sys_names.update(alias.asname or alias.name for alias in node.names if alias.name == 'sys')
        if isinstance(node, ast.ImportFrom) and node.module == 'sys' and any(alias.name == 'path' for alias in node.names):
            raise ValueError('Alias de sys.path não suportado: ' + ast.unparse(node))
    for node in ast.walk(tree):
        if isinstance(node, ast.Attribute) and node.attr == 'path' and isinstance(node.value, ast.Name) and node.value.id in sys_names:
            parent = parents.get(node)
            call = parents.get(parent)
            insertion = isinstance(parent, ast.Attribute) and parent.attr == 'insert' and node.value.id == 'sys' and isinstance(call, ast.Call) and call.func is parent
            membership = isinstance(parent, ast.Compare) and node in parent.comparators and all(isinstance(op, (ast.In, ast.NotIn)) for op in parent.ops)
            if not insertion and not membership:
                raise ValueError('Uso de sys.path não suportado: ' + ast.unparse(parent or node))

    def record(resolved):
        result.add(resolved)
        parent = resolved.parent
        while parent != root.resolve() and parent.is_relative_to(root.resolve()):
            initializer = parent / '__init__.py'
            if initializer.is_file():
                result.add(initializer.resolve())
            parent = parent.parent

    def resolve_import(node, bases):
        names, level = [], 0
        if isinstance(node, ast.Import):
            names = [alias.name for alias in node.names]
        elif isinstance(node, ast.ImportFrom):
            level = node.level
            if node.module:
                names.append(node.module)
            for alias in node.names:
                if alias.name != '*':
                    candidate = '.'.join(filter(None, [node.module, alias.name]))
                    try:
                        resolved = module_file(candidate, path, root, level=level, search_paths=bases)
                    except ValueError:
                        resolved = None
                    if resolved:
                        record(resolved)
        elif isinstance(node, ast.Call):
            dynamic = isinstance(node.func, ast.Name) and node.func.id == '__import__' or \
                isinstance(node.func, ast.Attribute) and node.func.attr == 'import_module'
            if dynamic:
                if not node.args or not isinstance(node.args[0], ast.Constant) or not isinstance(node.args[0].value, str):
                    raise ValueError('Import dinâmico não resolvido: ' + str(path))
                names = [node.args[0].value]
        for name in names:
            if re.fullmatch(r'capitulo_\d+', name):
                try:
                    resolved = module_file(name, path, root, level=level, search_paths=bases)
                except ValueError:
                    if any((base / name).is_dir() for base in bases):
                        continue
                    raise
                if resolved:
                    record(resolved)
                continue
            resolved = module_file(name, path, root, level=level, search_paths=bases)
            if resolved:
                record(resolved)

    def scan(body, values, bases):
        states = [(dict(values), list(bases))]
        for node in body:
            following = []
            for values, bases in states:
                if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                    scan(node.body, values, bases)
                    following.append((values, bases))
                    continue
                if isinstance(node, ast.If):
                    following.extend(scan(node.body, values, bases))
                    following.extend(scan(node.orelse, values, bases))
                    continue
                if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
                    following.extend(scan(node.body, values, bases))
                    following.extend(scan(node.orelse, values, bases))
                    continue
                if isinstance(node, (ast.With, ast.AsyncWith)):
                    following.extend(scan(node.body, values, bases))
                    continue
                if isinstance(node, ast.Try):
                    branches = scan(node.body + node.orelse, values, bases)
                    for handler in node.handlers:
                        branches.extend(scan(handler.body, values, bases))
                    for branch_values, branch_bases in branches:
                        following.extend(scan(node.finalbody, branch_values, branch_bases))
                    continue
                if isinstance(node, (ast.Assign, ast.AnnAssign)) and node.value is not None:
                    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                    for target in targets:
                        if isinstance(target, ast.Name):
                            try:
                                values[target.id] = python_path_value(node.value, path, values)
                            except (ValueError, TypeError, IndexError):
                                values.pop(target.id, None)
                for child in ast.walk(node):
                    if isinstance(child, ast.Call) and isinstance(child.func, ast.Attribute) and \
                            ast.dump(child.func.value) == ast.dump(ast.parse('sys.path', mode='eval').body):
                        if child.func.attr != 'insert' or len(child.args) != 2 or child.keywords:
                            raise ValueError('Alteração de sys.path não suportada: ' + ast.unparse(child))
                        index = python_path_value(child.args[0], path, values)
                        candidate = Path(python_path_value(child.args[1], path, values))
                        if not isinstance(index, int) or not candidate.is_absolute():
                            raise ValueError('Inserção em sys.path não resolvida: ' + ast.unparse(child))
                        candidate = candidate.resolve()
                        if not candidate.is_relative_to(root.resolve()):
                            raise ValueError('Dependência local fora da raiz do projeto: ' + str(candidate))
                        if not candidate.is_dir():
                            raise ValueError('Diretório de import ausente: ' + str(candidate))
                        bases.insert(index, candidate)
                    resolve_import(child, bases)
                following.append((values, bases))
            unique = {}
            for state_values, state_bases in following:
                key = (tuple(sorted(state_values.items())), tuple(state_bases))
                unique[key] = (state_values, state_bases)
            states = list(unique.values())
        return states

    scan(tree.body, {}, [path.parent.resolve(), root.resolve()])
    return result

def wl_get_arguments(source):
    for match in re.finditer(r'\bGet\[', source):
        start = match.end()
        depth, quoted, escaped, index = 1, False, False, start
        while depth and index < len(source):
            char = source[index]
            if quoted:
                if escaped:
                    escaped = False
                elif char == '\\':
                    escaped = True
                elif char == '"':
                    quoted = False
            elif char == '"':
                quoted = True
            elif char == '[':
                depth += 1
            elif char == ']':
                depth -= 1
            index += 1
        if depth:
            raise ValueError('Get Wolfram incompleto')
        yield source[start:index - 1].strip()


def direct_dependencies(path, root=ROOT):
    source = path.read_text()
    result = set()
    if path.suffix == '.py':
        result.update(python_dependencies(source, path, root))
    elif path.suffix == '.lean':
        for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)', source, re.M):
            for name in line.split():
                resolved = module_file(name, path, root, '.lean')
                if resolved:
                    result.add(resolved)
    elif path.suffix == '.wl':
        anchors = set(re.findall(r'\b([A-Za-z$][A-Za-z0-9$]*)\s*=\s*DirectoryName\[\$InputFileName\]', source))
        for expression in wl_get_arguments(source):
            simple = re.fullmatch(r'"([^"\\]+)"', expression)
            joined = re.fullmatch(r'FileNameJoin\[\s*\{\s*(DirectoryName\[\$InputFileName\]|[A-Za-z$][A-Za-z0-9$]*)\s*((?:,\s*"[^"\\]*")+)\s*\}\s*\]', expression)
            if simple:
                candidate = path.parent / simple.group(1)
            elif joined and (joined.group(1) in anchors or joined.group(1) == 'DirectoryName[$InputFileName]'):
                candidate = path.parent.joinpath(*re.findall(r'"([^"\\]*)"', joined.group(2)))
            else:
                raise ValueError('Get dinâmico não resolvido: ' + expression)
            if not candidate.is_file():
                raise ValueError('Dependência Wolfram ausente: ' + str(candidate))
            result.add(candidate.resolve())
    return result


def dependency_closure(path, root=ROOT):
    pending, result = [path.resolve()], set()
    while pending:
        current = pending.pop()
        if not current.is_relative_to(root.resolve()):
            raise ValueError('Dependência local fora da raiz do projeto: ' + str(current))
        if current in result:
            continue
        if not current.is_file():
            raise ValueError('Fonte ausente: ' + str(current))
        result.add(current)
        if current.suffix in {'.py', '.lean', '.wl'}:
            pending.extend(direct_dependencies(current, root))
    return result


def snapshot(paths, root=ROOT):
    return {source_name(path, root): sha(path) for path in sorted(paths)}


def expected_lean_artifacts(path, closure, command, root):
    if not isinstance(command, list):
        raise ValueError('comando_lean_sem_saida_univoca')
    positions = [index for index, argument in enumerate(command) if argument == '-o']
    if len(positions) != 1 or positions[0] + 1 >= len(command):
        raise ValueError('comando_lean_sem_saida_univoca')
    location = command[positions[0] + 1]
    if not isinstance(location, str) or not Path(location).is_absolute():
        raise ValueError('saida_lean_nao_absoluta')
    target = Path(location).resolve()
    relative = path.relative_to(root.resolve()).with_suffix('.olean')
    if target.parts[-len(relative.parts):] != relative.parts:
        raise ValueError('saida_lean_nao_corresponde_ao_programa')
    compiled = target.parents[len(relative.parts) - 1]
    return {(compiled / source.relative_to(root.resolve()).with_suffix('.olean')).resolve()
            for source in closure if source.suffix == '.lean'}


def validate_record(record, root=ROOT):
    errors, limitations = [], []
    name = record.get('arquivo', '')
    path = (root / name).resolve()
    if not name or not path.is_relative_to(root.resolve()) or not path.is_file():
        return {'arquivo': name, 'valido': False, 'erros': ['programa_ausente_ou_fora_do_pacote']}
    try:
        closure = dependency_closure(path, root)
    except ValueError as exc:
        return {'arquivo': name, 'valido': False, 'erros': [str(exc)]}
    current = snapshot(closure, root)
    before = record.get('fontes_antes', record.get('dependencias', {}))
    command = record.get('comando', [])
    if not isinstance(command, list) or not any(isinstance(value, str) and Path(value).is_absolute()
                                               and Path(value).resolve() == path for value in command):
        errors.append('comando_nao_identifica_programa_verificado')
    if sha(path) != record.get('sha256'):
        errors.append('programa_alterado')
    changed = [key for key, value in current.items() if before.get(key) != value]
    if changed:
        errors.append('fontes_ou_entradas_sem_snapshot_compativel')
    after = record.get('fontes_depois')
    stability = 'documentada'
    if after is not None:
        if any(before.get(key) != after.get(key) for key in current) or set(after) != set(current):
            errors.append('dependencia_alterada_durante_execucao')
    elif record.get('fontes_inalteradas_durante_execucao') is not True:
        stability = 'nao_documentada_no_registro_historico'
        limitations.append('Snapshot posterior ausente; alterações fora da dependência transitiva não invalidam os hashes atuais, mas o registro não documenta estabilidade durante a execução.')
    log = Path(record.get('log', ''))
    if not log.is_file() or sha(log) != record.get('log_sha256'):
        errors.append('log_ausente_ou_alterado')
    else:
        execution, parsed = execution_errors(path.suffix, record.get('codigo_saida'), log.read_text(errors='replace'))
        errors.extend(execution)
        if parsed != record.get('relatorios', []):
            errors.append('relatorios_divergem_do_log')
    if record.get('timeout'):
        errors.append('timeout')
    if path.suffix == '.lean':
        if any(lean_admissions(item) for item in closure if item.suffix == '.lean'):
            errors.append('admissao_ou_axioma_local_lean')
        artifacts = record.get('artefatos_lean', {})
        if not isinstance(artifacts, dict):
            errors.append('registro_de_objetos_lean_invalido')
        elif not artifacts:
            limitations.append('Registro histórico não sela o objeto Lean do programa e seus imports; reexecução em fechamento topológico documenta todos os objetos utilizados.')
        else:
            listed = set()
            for location, digest in artifacts.items():
                if not isinstance(location, str) or not Path(location).is_absolute():
                    errors.append('caminho_de_objeto_lean_invalido')
                    continue
                artifact = Path(location).resolve()
                listed.add(artifact)
                if not artifact.is_file() or sha(artifact) != digest:
                    errors.append('objeto_lean_ausente_ou_alterado')
            try:
                expected = expected_lean_artifacts(path, closure, command, root)
            except ValueError as exc:
                errors.append(str(exc))
            else:
                if listed != expected or len(listed) != len(artifacts):
                    errors.append('objetos_lean_nao_correspondem_ao_fechamento')
    valid = not errors
    return {'arquivo': name, 'valido': valid, 'compativel_com_fontes_atuais': not errors,
            'estabilidade': stability, 'erros': sorted(set(errors)), 'limitacoes': limitations,
            'documentacao_completa': not errors and not limitations,
            'fontes_divergentes': changed, 'dependencias_transitivas': sorted(current)}


def expected_files(root=ROOT):
    return sorted(path for path in root.glob('capitulo_*/*')
                  if path.suffix in {'.py', '.wl', '.lean'} and path.name not in DATA)


def aggregate(directories, root=ROOT):
    records = {}
    for directory in directories:
        for path in directory.rglob('*.json'):
            try:
                value = json.loads(path.read_text())
            except (OSError, ValueError):
                continue
            if isinstance(value, dict) and isinstance(value.get('arquivo'), str) and 'codigo_saida' in value:
                records.setdefault(value['arquivo'], []).append((path, value))
    result = []
    for path in expected_files(root):
        name = source_name(path, root)
        options = []
        for location, record in records.get(name, []):
            checked = validate_record(record, root)
            checked['registro'] = str(location)
            checked['registro_modificado_em'] = location.stat().st_mtime
            options.append(checked)
        if options:
            options.sort(key=lambda item: (item['valido'], item.get('documentacao_completa', False),
                                           item.get('compativel_com_fontes_atuais', False),
                                           item['registro_modificado_em']), reverse=True)
            result.append(options[0])
        else:
            result.append({'arquivo': name, 'valido': False, 'erros': ['execucao_ausente']})
    return {'arquivos_esperados': len(result), 'execucoes_validas': sum(item['valido'] for item in result),
            'compativeis_com_limitacoes': sum(item['valido'] and bool(item.get('limitacoes')) for item in result),
            'todos_validos': bool(result) and all(item['valido'] for item in result),
            'verificacao_semantica_realizada_por_este_validador': False,
            'execucoes': result, 'reexecutar': [item['arquivo'] for item in result if not item['valido']]}


def self_test():
    cases = [
        ('dependencia_aprovada_nao_oculta_erro', '.py', 0, '{"passed":true,"checks":1}\n{"error":"failed"}'),
        ('zero_verificacoes_rejeitado', '.py', 0, '{"passed":true,"checks":0}'),
        ('falha_interna_rejeitada', '.wl', 0, '{"passed":true,"checks":{"a":false}}'),
        ('lista_vazia_rejeitada', '.py', 0, '{"passed":true,"checks":1,"results":[]}'),
        ('saida_falha_rejeitada', '.py', 1, '{"passed":true,"checks":1}'),
        ('sorry_rejeitado', '.lean', 0, "warning: declaration uses 'sorry'")]
    for name, suffix, code, text in cases:
        if not execution_errors(suffix, code, text)[0]:
            raise AssertionError(name)
    if execution_errors('.py', 0, '{"passed":true,"checks":1,"results":[{"id":"x","passed":true}]}')[0]:
        raise AssertionError('relatorio_valido_rejeitado')
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        folder = root / 'capitulo_01'
        folder.mkdir()
        principal, helper, unrelated = (folder / name for name in ('main.py', 'helper.py', 'other.py'))
        principal.write_text('import helper\n')
        helper.write_text('value=1\n')
        unrelated.write_text('value=0\n')
        closure = dependency_closure(principal, root)
        if closure != {principal, helper}:
            raise AssertionError('fechamento_transitivo_incorreto')
        initial = snapshot(closure, root)
        unrelated.write_text('value=2\n')
        if snapshot(dependency_closure(principal, root), root) != initial:
            raise AssertionError('arquivo_alheio_invalida_execucao')
        helper.write_text('value=3\n')
        if snapshot(dependency_closure(principal, root), root) == initial:
            raise AssertionError('mudanca_dependencia_nao_detectada')
        restricted = root / 'restricted'
        restricted.mkdir()
        escaped = root / 'external.wl'
        escaped.write_text('value = 1;\n')
        caller = restricted / 'main.wl'
        caller.write_text('Get["../external.wl"];\n')
        try:
            dependency_closure(caller, restricted)
        except ValueError as error:
            if 'fora da raiz' not in str(error):
                raise
        else:
            raise AssertionError('dependencia_externa_aceita')
        second = root / 'capitulo_02'
        second.mkdir()
        foreign = second / 'foreign.py'
        foreign.write_text('value=7\n')
        principal.write_text("from pathlib import Path\nimport sys\nsys.path.insert(0,str(Path(__file__).resolve().parents[1]/'capitulo_02'))\nimport foreign\n")
        closure = dependency_closure(principal, root)
        if closure != {principal, foreign}:
            raise AssertionError('import_entre_capitulos_omitido')
        initial = snapshot(closure, root)
        foreign.write_text('value=8\n')
        if snapshot(dependency_closure(principal, root), root) == initial:
            raise AssertionError('mudanca_import_entre_capitulos_omitida')
        shadow = folder / 'foreign.py'
        shadow.write_text('value=0\n')
        if dependency_closure(principal, root) != {principal, foreign}:
            raise AssertionError('precedencia_sys_path_ignorada')
        principal.write_text("import foreign\nfrom pathlib import Path\nimport sys\nBASE=Path(__file__).resolve().parents[1]/'capitulo_02'\nsys.path.insert(0,str(BASE))\nimport foreign\n")
        if dependency_closure(principal, root) != {principal, shadow, foreign}:
            raise AssertionError('ordem_das_insercoes_ignorada')
        principal.write_text("from pathlib import Path\nimport sys\nsys.path.insert(0,str(Path(__file__).resolve().parents[2]))\nimport foreign\n")
        try:
            dependency_closure(principal, root)
        except ValueError as error:
            if 'fora da raiz' not in str(error):
                raise
        else:
            raise AssertionError('escape_sys_path_aceito')
        principal.write_text("import sys\nsys.path.insert(0,obtain_path())\nimport foreign\n")
        try:
            dependency_closure(principal, root)
        except ValueError as error:
            if 'estaticamente' not in str(error):
                raise
        else:
            raise AssertionError('sys_path_dinamico_nao_rejeitado')
        for text, name in (
            ("from pathlib import Path\nimport sys\nsys.path=[str(Path(__file__).resolve().parents[1]/'capitulo_02')]+sys.path\nimport foreign\n", 'atribuicao_sys_path_rejeitada'),
            ("from pathlib import Path\nimport sys\npaths=sys.path\npaths.insert(0,str(Path(__file__).resolve().parents[1]/'capitulo_02'))\nimport foreign\n", 'alias_sys_path_rejeitado'),
            ("from pathlib import Path\nimport sys as system\nsystem.path.insert(0,str(Path(__file__).resolve().parents[1]/'capitulo_02'))\nimport foreign\n", 'alias_modulo_sys_rejeitado')):
            principal.write_text(text)
            try:
                dependency_closure(principal, root)
            except ValueError as error:
                if 'sys.path não suportado' not in str(error):
                    raise
            else:
                raise AssertionError(name)
        initializer = second / '__init__.py'
        initializer.write_text('value=1\n')
        principal.write_text('import capitulo_02.foreign\n')
        if dependency_closure(principal, root) != {principal, foreign, initializer}:
            raise AssertionError('inicializador_de_pacote_omitido')
        before_initializer = snapshot(dependency_closure(principal, root), root)
        initializer.write_text('value=2\n')
        if snapshot(dependency_closure(principal, root), root) == before_initializer:
            raise AssertionError('mudanca_inicializador_omitida')
        package = folder / 'barepkg'
        package.mkdir()
        package_init = package / '__init__.py'
        package_child = package / 'child.py'
        package_init.write_text('value=1\n')
        package_child.write_text('value=2\n')
        principal.write_text('from barepkg import child\n')
        if dependency_closure(principal, root) != {principal, package_init, package_child}:
            raise AssertionError('submodulo_de_pacote_simples_omitido')
        alternate = root / 'alternate'
        alternate_package = alternate / 'capitulo_02'
        alternate_package.mkdir(parents=True)
        alternate_init = alternate_package / '__init__.py'
        alternate_init.write_text('value=4\n')
        principal.write_text("from pathlib import Path\nimport sys\nsys.path.insert(0,str(Path(__file__).resolve().parents[1]/'alternate'))\nimport capitulo_02\n")
        if dependency_closure(principal, root) != {principal, alternate_init}:
            raise AssertionError('precedencia_pacote_capitulo_ignorada')
        principal.write_text("from pathlib import Path\nimport sys\ninsert=sys.path.insert\ninsert(0,str(Path(__file__).resolve().parents[1]/'capitulo_02'))\nimport foreign\n")
        try:
            dependency_closure(principal, root)
        except ValueError as error:
            if 'sys.path não suportado' not in str(error):
                raise
        else:
            raise AssertionError('metodo_sys_path_escapado')
        principal.write_text('import helper\n')
        logs = root / 'logs'
        logs.mkdir()
        log = logs / 'main.log'
        log.write_text('{"passed":true,"checks":1,"results":[{"id":"x","passed":true}]}')
        state = snapshot(dependency_closure(principal,root),root)
        old = {'arquivo':source_name(principal,root),'sha256':sha(principal),
               'comando':['python3',str(principal)],'dependencias':state,
               'codigo_saida':0,'log':str(log),'log_sha256':sha(log),
               'relatorios':reports(log.read_text()),'fontes_inalteradas_durante_execucao':False}
        complete = dict(old,fontes_antes=state,fontes_depois=state)
        (logs/'a_antigo.json').write_text(json.dumps(old))
        (logs/'b_completo.json').write_text(json.dumps(complete))
        combined = aggregate([logs],root)
        selected = next(item for item in combined['execucoes'] if item['arquivo']==source_name(principal,root))
        if not selected['documentacao_completa'] or not selected['registro'].endswith('b_completo.json'):
            raise AssertionError('registro_completo_nao_priorizado')
        lean_main, lean_helper = folder / 'Main.lean', folder / 'Helper.lean'
        lean_main.write_text('import capitulo_01.Helper\ndef mainValue : Nat := helperValue\n')
        lean_helper.write_text('def helperValue : Nat := 1\n')
        objects = root / 'olean' / 'capitulo_01'
        objects.mkdir(parents=True)
        own_object, imported_object = objects / 'Main.olean', objects / 'Helper.olean'
        own_object.write_bytes(b'main-object-fixture')
        imported_object.write_bytes(b'helper-object-fixture')
        lean_log = logs / 'Main.lean.log'
        lean_log.write_text('')
        state = snapshot(dependency_closure(lean_main, root), root)
        lean_record = {'arquivo':source_name(lean_main,root), 'sha256':sha(lean_main),
                       'comando':['lean','-o',str(own_object),str(lean_main)],
                       'fontes_antes':state, 'fontes_depois':state, 'codigo_saida':0,
                       'log':str(lean_log), 'log_sha256':sha(lean_log), 'relatorios':[],
                       'artefatos_lean':{str(own_object):sha(own_object),
                                        str(imported_object):sha(imported_object)}}
        checked = validate_record(lean_record, root)
        if not checked['valido'] or not checked['documentacao_completa']:
            raise AssertionError('objetos_lean_completos_rejeitados')
        for missing, name in ((own_object,'alvo_lean_omitido'),
                              (imported_object,'import_lean_omitido')):
            partial = dict(lean_record, artefatos_lean={key:value for key,value in lean_record['artefatos_lean'].items() if key != str(missing)})
            if validate_record(partial, root)['valido']:
                raise AssertionError(name)
        extra = objects / 'Other.olean'
        extra.write_bytes(b'other-object-fixture')
        with_extra = dict(lean_record, artefatos_lean=dict(lean_record['artefatos_lean'], **{str(extra):sha(extra)}))
        if validate_record(with_extra, root)['valido']:
            raise AssertionError('objeto_lean_alheio_aceito')
        wrong_output = dict(lean_record, comando=['lean','-o',str(extra),str(lean_main)])
        if validate_record(wrong_output, root)['valido']:
            raise AssertionError('saida_lean_alheia_aceita')
        moved_output = root / 'outro_cache' / 'capitulo_01' / 'Main.olean'
        wrong_cache = dict(lean_record, comando=['lean','-o',str(moved_output),str(lean_main)])
        if validate_record(wrong_cache, root)['valido']:
            raise AssertionError('objetos_lean_de_outro_cache_aceitos')
        historical = validate_record(dict(lean_record, artefatos_lean={}), root)
        if not historical['valido'] or historical['documentacao_completa'] or not historical['limitacoes']:
            raise AssertionError('historico_lean_sem_objetos_nao_limitado')
    results = [item[0] for item in cases] + ['relatorio_valido', 'fechamento_transitivo',
        'alteracao_alheia_ignorada', 'alteracao_dependencia_detectada','registro_completo_priorizado',
        'objetos_lean_completos_aceitos', 'alvo_lean_omitido_rejeitado',
        'import_lean_omitido_rejeitado', 'objeto_lean_alheio_rejeitado',
        'saida_lean_alheia_rejeitada', 'objetos_lean_de_outro_cache_rejeitados',
        'historico_lean_sem_objetos_limitado', 'dependencia_externa_rejeitada',
        'import_entre_capitulos', 'mudanca_import_entre_capitulos_detectada',
        'precedencia_sys_path', 'ordem_das_insercoes_preservada',
        'escape_sys_path_rejeitado', 'sys_path_dinamico_rejeitado',
        'inicializador_de_pacote_incluido', 'mudanca_inicializador_detectada',
        'submodulo_de_pacote_simples_incluido', 'atribuicao_sys_path_rejeitada',
        'alias_sys_path_rejeitado', 'alias_modulo_sys_rejeitado',
        'precedencia_pacote_capitulo', 'metodo_sys_path_escapado_rejeitado']
    return {'passed': True, 'checks': len(results), 'results': results}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('diretorios', nargs='*', type=Path)
    parser.add_argument('--saida', type=Path)
    parser.add_argument('--autoteste', action='store_true')
    args = parser.parse_args()
    if args.autoteste:
        print(json.dumps(self_test(), ensure_ascii=False))
        return 0
    if not args.diretorios:
        parser.error('Informe ao menos um diretório com registros de execução')
    result = aggregate([path.resolve() for path in args.diretorios])
    if args.saida:
        args.saida.write_text(json.dumps(result, ensure_ascii=False, indent=2))
    print(json.dumps({key: value for key, value in result.items() if key not in {'execucoes', 'reexecutar'}}, ensure_ascii=False))
    return 0 if result['todos_validos'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
