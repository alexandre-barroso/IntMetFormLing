import argparse
import ast
import json
from pathlib import Path
import re
from validar_execucoes import direct_dependencies

ROOT = Path(__file__).resolve().parent
DATA = {'cobertura.py', 'redteam.py', 'revisao_integral.py', 'prosa.py', 'revisao_v2.py'}
SUFFIXES = {'.py', '.wl', '.lean', '.m'}


def local_name(path, root):
    resolved = path.resolve()
    if not resolved.is_relative_to(root.resolve()):
        raise ValueError('Dependência fora da raiz: ' + str(path))
    return resolved.relative_to(root.resolve()).as_posix()


def masked(source, language):
    chars = list(source)
    start, end = ('/-', '-/') if language == 'lean' else ('(*', '*)')
    index = 0
    while index < len(source):
        stop = None
        if source.startswith(start, index):
            level = 1
            stop = index + 2
            while stop < len(source) and level:
                if source.startswith(start, stop):
                    level += 1
                    stop += 2
                elif source.startswith(end, stop):
                    level -= 1
                    stop += 2
                else:
                    stop += 1
        elif language == 'lean' and source.startswith('--', index):
            stop = source.find('\n', index)
            stop = len(source) if stop < 0 else stop
        elif source[index] == '"':
            stop = index + 1
            while stop < len(source):
                if source[stop] == '\\':
                    stop += 2
                elif source[stop] == '"':
                    stop += 1
                    break
                else:
                    stop += 1
        if stop is None:
            index += 1
        else:
            for position in range(index, min(stop, len(source))):
                if chars[position] != '\n':
                    chars[position] = ' '
            index = stop
    return ''.join(chars)


def signature_end(code, start, limit):
    stack = []
    pairs = {'(': ')', '[': ']', '{': '}'}
    index = start
    while index < limit:
        character = code[index]
        if character in pairs:
            stack.append(pairs[character])
        elif character in ')]}' and stack and character == stack[-1]:
            stack.pop()
        elif not stack and code.startswith(':=', index):
            return index
        index += 1
    return limit


def lean_statements(source):
    code = masked(source, 'lean')
    pattern = r'(?m)^[ \t]*(?:@\[[^\n]*?\]\s*)?(?:(?:noncomputable|private|protected|unsafe|partial|nonrec)\s+)*(namespace|section|end|variable|include|omit|universe|universes|open|attribute|set_option|theorem|lemma|axiom|example|def|abbrev|structure|inductive)\b(?:[ \t]+([^\s:(\[{]+))?'
    commands = list(re.finditer(pattern, code))
    scopes = [{'kind': 'root', 'name': '', 'context': []}]
    result = []
    for position, match in enumerate(commands):
        kind, name = match.group(1), match.group(2)
        next_start = commands[position + 1].start() if position + 1 < len(commands) else len(source)
        line = source.count('\n', 0, match.start()) + 1
        if kind in {'namespace', 'section'}:
            scopes.append({'kind': kind, 'name': name or '', 'context': []})
        elif kind == 'end':
            if len(scopes) > 1:
                scopes.pop()
        elif kind in {'variable', 'include', 'omit', 'universe', 'universes'}:
            text = source[match.start():next_start].strip()
            boundary = re.search(r'(?m)^\s*#', text)
            if boundary:
                text = text[:boundary.start()].strip()
            scopes[-1]['context'].append({'linha': line, 'declaracao': text})
        elif kind in {'theorem', 'lemma', 'axiom', 'example'}:
            end = signature_end(code, match.end(), next_start)
            header = source[match.start():end].strip()
            namespace = '.'.join(scope['name'] for scope in scopes if scope['kind'] == 'namespace')
            short = name if kind != 'example' else 'example@' + str(line)
            if not short:
                short = kind + '@' + str(line)
            qualified = short.removeprefix('_root_.') if short.startswith('_root_.') else '.'.join(filter(None, [namespace, short]))
            result.append({'nome': qualified, 'tipo': kind, 'linha': line,
                           'assinatura': header,
                           'contexto_lexical': [item for scope in scopes for item in scope['context']],
                           'nome_anonimo': kind == 'example'})
    return result


def python_checks(source):
    tree = ast.parse(source)
    checks, assertions = [], []
    for node in ast.walk(tree):
        if isinstance(node, ast.Assert):
            assertions.append({'linha': node.lineno, 'expressao': ast.get_source_segment(source, node.test)})
        if not isinstance(node, ast.Call):
            continue
        called = node.func.id if isinstance(node.func, ast.Name) else node.func.attr if isinstance(node.func, ast.Attribute) else None
        if called != 'check':
            continue
        argument = node.args[0] if node.args else None
        literal = isinstance(argument, ast.Constant) and isinstance(argument.value, str)
        checks.append({'nome': argument.value if literal else None, 'linha': node.lineno,
                       'identificador_dinamico': not literal,
                       'expressao_identificador': ast.get_source_segment(source, argument) if argument else None,
                       'chamada': ast.get_source_segment(source, node)})
    return sorted(checks, key=lambda item: item['linha']), assertions


def wolfram_checks(source):
    code = masked(source, 'wl')
    checks = []
    for match in re.finditer(r'\bcheck\s*\[', code):
        start = code.index('[', match.start())
        stack = [']']
        pairs = {'[': ']', '(': ')', '{': '}'}
        split = None
        index = start + 1
        while index < len(code) and stack:
            character = code[index]
            if character in pairs:
                stack.append(pairs[character])
            elif character in '])}' and character == stack[-1]:
                stack.pop()
            elif character == ',' and len(stack) == 1 and split is None:
                split = index
            index += 1
        if stack:
            raise ValueError('Chamada Wolfram sem fechamento')
        if re.match(r'\s*(?::=|=)', code[index:]):
            continue
        argument = source[start + 1:split if split is not None else index - 1].strip()
        literal = re.fullmatch(r'"(?:[^"\\]|\\.)*"', argument) is not None
        try:
            name = json.loads(argument) if literal else None
        except json.JSONDecodeError:
            name = argument[1:-1] if literal else None
        checks.append({'nome': name, 'linha': source.count('\n', 0, match.start()) + 1,
                       'identificador_dinamico': not literal, 'expressao_identificador': argument,
                       'chamada': source[match.start():index]})
    return checks


def inventory(root=ROOT, chapter=None):
    root = root.resolve()
    candidates = sorted(path for path in root.glob('capitulo_*/*')
                        if path.is_file() and path.suffix in SUFFIXES and path.name not in DATA)
    if chapter is not None:
        candidates = [path for path in candidates if path.parent.name == f'capitulo_{chapter:02}']
    programs = []
    dependency_cache = {}

    def dependencies(path):
        if path not in dependency_cache:
            found = direct_dependencies(path, root) if path.suffix in {'.py', '.wl', '.lean'} else set()
            for dependency in found:
                local_name(dependency, root)
                if dependency.name in DATA:
                    raise ValueError('Dependência excluída do índice executável: ' + str(dependency))
            dependency_cache[path] = found
        return dependency_cache[path]

    for path in candidates:
        name = local_name(path, root)
        source = path.read_text()
        pending = list(dependencies(path))
        closure = set()
        while pending:
            current = pending.pop()
            if current not in closure:
                closure.add(current)
                pending.extend(dependencies(current))
        row = {'arquivo': name, 'capitulo': int(path.parent.name.split('_')[-1]),
               'sistema': {'.py': 'python', '.wl': 'wolfram', '.lean': 'lean', '.m': 'matlab'}[path.suffix],
               'dependencias_diretas': sorted(local_name(item, root) for item in dependencies(path)),
               'dependencias_transitivas': sorted(local_name(item, root) for item in closure),
               'enunciados_lean': [], 'verificacoes': [], 'assercoes_python_sem_identificador': []}
        if path.suffix == '.lean':
            row['enunciados_lean'] = lean_statements(source)
        elif path.suffix == '.py':
            row['verificacoes'], row['assercoes_python_sem_identificador'] = python_checks(source)
        elif path.suffix == '.wl':
            row['verificacoes'] = wolfram_checks(source)
        programs.append(row)
    return {'natureza': 'Índice lexical de código local; não executa nem certifica proposições.',
            'assinaturas_lean': 'Texto declarado, com contexto lexical visível. O contexto pode conter variáveis não usadas; a elaboração efetiva pertence ao compilador Lean.',
            'identificadores': 'Chamadas check literais são listadas; expressões dinâmicas não são executadas ou expandidas. Outras formas de verificação podem existir nos programas.',
            'dependencias': 'Somente dependências locais de imports Python, imports Lean e Get Wolfram; bibliotecas externas não são enumeradas.',
            'capitulos': sorted({row['capitulo'] for row in programs}),
            'resumo': {'programas': len(programs),
                       'enunciados_lean': sum(len(row['enunciados_lean']) for row in programs),
                       'verificacoes_literais': sum(not item['identificador_dinamico'] for row in programs for item in row['verificacoes']),
                       'verificacoes_dinamicas': sum(item['identificador_dinamico'] for row in programs for item in row['verificacoes']),
                       'assercoes_python': sum(len(row['assercoes_python_sem_identificador']) for row in programs)},
            'programas': programs}


def details(report, name):
    matches = []
    for program in report['programas']:
        for kind in ('enunciados_lean', 'verificacoes'):
            for item in program[kind]:
                identity = item.get('nome')
                if identity == name or identity and identity.rsplit('.', 1)[-1] == name:
                    matches.append({'arquivo': program['arquivo'], 'sistema': program['sistema'],
                                    'classe': kind, **item})
    return {'busca': name, 'correspondencias': matches, 'quantidade': len(matches),
            'aviso': 'A busca apresenta todas as correspondências; nomes repetidos não são escolhidos silenciosamente.'}


def main():
    parser = argparse.ArgumentParser(description='Índice autônomo dos programas e enunciados por capítulo.')
    parser.add_argument('--capitulo', type=int)
    parser.add_argument('--detalhar')
    parser.add_argument('--resumo', action='store_true')
    parser.add_argument('--saida', type=Path)
    args = parser.parse_args()
    if args.capitulo is not None and args.capitulo < 1:
        parser.error('O capítulo deve ser um inteiro positivo.')
    report = inventory(chapter=args.capitulo)
    if args.capitulo is not None and not report['programas']:
        parser.error('Capítulo sem programas locais.')
    if args.detalhar:
        report = details(report, args.detalhar)
    elif args.resumo:
        report.pop('programas')
    text = json.dumps(report, ensure_ascii=False, indent=2)
    if args.saida:
        args.saida.write_text(text + '\n')
    print(text)
    return 1 if args.detalhar and not report['correspondencias'] else 0


if __name__ == '__main__':
    raise SystemExit(main())
