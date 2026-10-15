import ast
import hashlib
import json
from pathlib import Path
import re

def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()

def balanced(source, start):
    pairs = {'[':']', '{':'}', '(':')'}
    stack = []
    quoted = False
    escaped = False
    for index in range(start, len(source)):
        character = source[index]
        if quoted:
            if escaped:
                escaped = False
            elif character == '\\':
                escaped = True
            elif character == '"':
                quoted = False
            continue
        if character == '"':
            quoted = True
        elif character in pairs:
            stack.append(pairs[character])
        elif character in ']})':
            if not stack or stack.pop() != character:
                raise ValueError('Unbalanced Wolfram expression')
            if not stack:
                return index + 1
    raise ValueError('Unterminated Wolfram expression')

def extract(path):
    source = path.read_text()
    result = {}

    def add(name, start, end, kind):
        line = source[:start].count('\n') + 1
        text = source[start:end].strip()
        key = f'{path.name}:{line}:{name}'
        result[key] = {'arquivo':path.name, 'linha':line, 'objeto':name, 'tipo':kind, 'sha256':digest(text), 'fragmento':text}

    if path.suffix == '.py':
        tree = ast.parse(source)
        lines = source.splitlines(keepends=True)
        for node in ast.walk(tree):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'check' and node.args and isinstance(node.args[0], ast.Constant) and isinstance(node.args[0].value, str):
                start = sum(map(len,lines[:node.lineno-1])) + len(lines[node.lineno-1].encode()[:node.col_offset].decode())
                end = sum(map(len,lines[:node.end_lineno-1])) + len(lines[node.end_lineno-1].encode()[:node.end_col_offset].decode())
                add(node.args[0].value, start, end, 'check')
            elif isinstance(node,(ast.FunctionDef,ast.AsyncFunctionDef)):
                start = sum(map(len,lines[:node.lineno-1])) + len(lines[node.lineno-1].encode()[:node.col_offset].decode())
                end = sum(map(len,lines[:node.end_lineno-1])) + len(lines[node.end_lineno-1].encode()[:node.end_col_offset].decode())
                add(node.name,start,end,'definicao')
    elif path.suffix == '.wl':
        for match in re.finditer(r'\bcheck\s*\[\s*"([^"\\]*(?:\\.[^"\\]*)*)"\s*,', source):
            start = source.index('[',match.start())
            add(match.group(1), match.start(), balanced(source,start), 'check')
    elif path.suffix == '.lean':
        pattern = r'(?m)^[ \t]*(?:(?:noncomputable|private|protected)\s+)*(namespace|end|theorem|lemma|def|abbrev|structure|inductive)\b(?:\s+([^\s:(\[{]+))?'
        entries = list(re.finditer(pattern, source))
        namespaces = []
        for index, match in enumerate(entries):
            kind, name = match.group(1), match.group(2)
            if kind == 'namespace':
                namespaces.append(name)
            elif kind == 'end':
                if namespaces:
                    namespaces.pop()
            else:
                end = entries[index+1].start() if index+1<len(entries) else len(source)
                for boundary in re.finditer(r'(?m)^(?:#print|#check|set_option|open|attribute)\b',source[match.start():end]):
                    end=match.start()+boundary.start()
                    break
                add('.'.join(namespaces+[name]),match.start(),end,kind)
    return result

def catalogue(folder):
    result = {}
    for path in sorted(folder.iterdir()):
        if path.suffix in ('.py','.lean','.wl') and path.name not in ('cobertura.py','redteam.py','revisao_integral.py','prosa.py'):
            result.update(extract(path))
    return result

def resolve(objects, witness):
    matches = [(key,value) for key,value in objects.items() if value['arquivo']==witness['arquivo'] and (value['objeto']==witness['nome'] or value['objeto'].endswith('.'+witness['nome']))]
    if 'linha' in witness:
        matches = [(key,value) for key,value in matches if value['linha']==witness['linha']]
    if 'indice' in witness:
        matches = matches[witness['indice']:witness['indice']+1]
    if len(matches) != 1:
        raise ValueError({'testemunha':witness, 'candidatos':[key for key,value in matches]})
    return matches[0]

def seal(record):
    return digest(json.dumps({key:value for key,value in record.items() if key!='assinatura_revisao'},ensure_ascii=False,sort_keys=True,separators=(',',':')))

def freeze(record, rows, objects, files):
    result = json.loads(json.dumps(record,ensure_ascii=False))
    result['fontes'] = {identity:{key:rows[identity][key] for key in ('sha256','context_sha256','source_file_sha256','file','line','expression')} for identity in result['ids']}
    for system, witnesses in result['testemunhas'].items():
        for witness in witnesses:
            key,item = resolve(objects,witness)
            witness['objeto_id'] = key
            witness['objeto_sha256'] = item['sha256']
            witness['arquivo_sha256'] = files[item['arquivo']]
    result['assinatura_revisao'] = seal(result)
    return result
