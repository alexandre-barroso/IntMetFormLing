from fractions import Fraction
from pathlib import Path
import hashlib
import math
import re

class Unsupported(ValueError):
    pass

def tokens(source):
    if re.search(r'[0-9]\.[0-9]',source):
        raise Unsupported('ambiguous literal period in Portuguese notation')
    source = source.strip().rstrip('.,;')
    source = source.replace('{,}', '.').replace('\\,', '').replace('~', '')
    source = re.sub(r'\\(?:left|right)\b', '', source)
    source = re.sub(r'\\(?:quad|qquad|;|!|:)\b', ' ', source)
    pattern = r'\\[A-Za-z]+|\\%|[0-9]+(?:\.[0-9]+)?|[{}()+*/^!|=<>−-]'
    output = []
    offset = 0
    for match in re.finditer(pattern, source):
        if source[offset:match.start()].strip():
            raise Unsupported(source[offset:match.start()])
        output.append(match.group().replace('−', '-'))
        offset = match.end()
    if source[offset:].strip():
        raise Unsupported(source[offset:])
    return output

class Parser:
    relations = {'=': '=', '<': '<', '>': '>', '\\leq': '<=', '\\le': '<=', '\\geq': '>=', '\\ge': '>=', '\\neq': '!=', '\\approx': '~'}

    def __init__(self, source):
        self.values = tokens(source)
        self.position = 0

    def peek(self):
        return self.values[self.position] if self.position < len(self.values) else None

    def take(self, expected=None):
        value = self.peek()
        if value is None or expected is not None and value != expected:
            raise Unsupported((value, expected))
        self.position += 1
        return value

    def atom(self):
        value = self.take()
        if value in ('-', '+'):
            item = self.atom()
            return ('neg', item) if value == '-' else item
        if value in ('{', '('):
            result = self.expr()
            self.take('}' if value == '{' else ')')
            return result
        if value == '|':
            result = self.expr()
            self.take('|')
            return ('abs', result)
        if value in ('\\frac', '\\tfrac', '\\dfrac'):
            return ('div', self.tex_argument(), self.tex_argument())
        if re.fullmatch(r'[0-9]+(?:\.[0-9]+)?', value):
            return ('number', value)
        raise Unsupported(value)

    def tex_argument(self):
        value = self.peek()
        if value == '{' or value is not None and re.fullmatch(r'[0-9]',value):
            return self.atom()
        raise Unsupported('unbraced multi-token TeX argument')

    def power(self):
        if self.peek() in ('-', '+'):
            operator = self.take()
            result = self.power()
            return ('neg', result) if operator == '-' else result
        result = self.atom()
        if self.peek() == '^':
            self.take()
            result = ('pow', result, self.tex_argument())
        while self.peek() in ('!', '\\%'):
            operator = self.take()
            result = ('factorial', result) if operator == '!' else ('percent', result)
        return result

    def product(self):
        result = self.power()
        while True:
            value = self.peek()
            if value in ('*', '\\times', '\\cdot', '/'):
                self.take()
                result = ('div' if value == '/' else 'mul', result, self.power())
            elif value in ('(', '{', '\\frac', '\\tfrac', '\\dfrac'):
                result = ('mul', result, self.power())
            else:
                return result

    def expr(self):
        result = self.product()
        while self.peek() in ('+', '-'):
            operator = self.take()
            result = ('add' if operator == '+' else 'sub', result, self.product())
        return result

    def parse(self):
        first = self.expr()
        result = []
        while self.peek() in self.relations:
            operator = self.relations[self.take()]
            right = self.expr()
            result.append((operator, first, right))
            first = right
        if self.peek() is not None or not result:
            raise Unsupported(self.peek())
        return result

def evaluate(tree):
    name, *args = tree
    if name == 'number':
        return Fraction(args[0])
    values = [evaluate(item) for item in args]
    if name == 'neg':
        return -values[0]
    if name == 'abs':
        return abs(values[0])
    if name == 'percent':
        return values[0] / 100
    if name == 'factorial':
        if values[0].denominator != 1 or values[0] < 0:
            raise Unsupported('factorial domain')
        return Fraction(math.factorial(values[0].numerator))
    if name == 'add':
        return values[0] + values[1]
    if name == 'sub':
        return values[0] - values[1]
    if name == 'mul':
        return values[0] * values[1]
    if name == 'div':
        if values[1] == 0:
            raise Unsupported('zero denominator')
        return values[0] / values[1]
    if name == 'pow':
        if values[1].denominator != 1 or values[0] == 0 and values[1] <= 0:
            raise Unsupported('power domain')
        return values[0] ** values[1].numerator
    raise Unsupported(name)

def tolerance(tree):
    if tree[0] == 'percent':
        return tolerance(tree[1]) / 100
    if tree[0] == 'neg':
        return tolerance(tree[1])
    if tree[0] != 'number':
        raise Unsupported('rounding target must be a printed numeral')
    digits = len(tree[1].split('.')[1]) if '.' in tree[1] else 0
    return Fraction(1, 2 * 10 ** digits)

def render(tree, system):
    name, *args = tree
    if name == 'number':
        value = Fraction(args[0])
        if system == 'py':
            return f'F({value.numerator},{value.denominator})'
        return str(value.numerator) if value.denominator == 1 else f'({value.numerator}/{value.denominator})'
    values = [render(item, system) for item in args]
    if name == 'neg':
        return f'(-{values[0]})'
    if name == 'abs':
        return f'abs({values[0]})' if system == 'py' else f'Abs[{values[0]}]' if system == 'wl' else f'|{values[0]}|'
    if name == 'percent':
        return f'({values[0]}/100)'
    if name == 'factorial':
        if args[0][0] != 'number':
            raise Unsupported('compound factorial argument requires a separate literal proof')
        value = evaluate(args[0])
        if value.denominator != 1 or value < 0:
            raise Unsupported('factorial domain')
        return f'F(math.factorial({value.numerator}))' if system == 'py' else f'Factorial[{value.numerator}]' if system == 'wl' else f'(Nat.factorial {value.numerator} : ℚ)'
    if name == 'pow':
        literal = args[1]
        if literal[0] == 'neg':
            literal = literal[1]
        if literal[0] != 'number':
            raise Unsupported('compound exponent requires a separate literal proof')
        value = evaluate(args[1])
        if value.denominator != 1:
            raise Unsupported('integer exponent required')
        exponent = '**' if system == 'py' else '^'
        power = f'({values[0]}{exponent}{abs(value.numerator)})'
        return power if value >= 0 else f'(1/{power})'
    operator = {'add': '+', 'sub': '-', 'mul': '*', 'div': '/'}[name]
    return f'({values[0]}{operator}{values[1]})'

def statement(relations, system, negate=False):
    parts = []
    for operator, left, right in relations:
        evaluate(left)
        evaluate(right)
        a, b = render(left, system), render(right, system)
        if system == 'lean':
            a = f'({a} : ℚ)'
        if operator == '~':
            bound = tolerance(right)
            difference = f'({a}-{b})'
            absolute = f'abs{difference}' if system == 'py' else f'Abs[{difference}]' if system == 'wl' else f'|{difference}|'
            part = f'{absolute} <= ' + (f'F({bound.numerator},{bound.denominator})' if system == 'py' else f'({bound.numerator}/{bound.denominator})')
        else:
            op = ('==' if system != 'lean' else '=') if operator == '=' else ('≠' if system == 'lean' else '!=') if operator == '!=' else operator
            part = f'{a} {op} {b}'
        if system == 'lean':
            part = part.replace('<=', '≤').replace('>=', '≥')
        parts.append(f'({part})')
    conjunction = ' and ' if system == 'py' else ' && ' if system == 'wl' else ' ∧ '
    result = conjunction.join(parts)
    return (f'not ({result})' if system == 'py' else f'!({result})' if system == 'wl' else f'¬ ({result})') if negate else result

def generated(chapter, rows):
    accepted = []
    for row in rows:
        if row['chapter'] != chapter or row['kind'] not in ('inline', 'display', 'figure_inline'):
            continue
        try:
            relations = Parser(row['expression']).parse()
            expressions = {system: statement(relations, system, row['id'] == 'c08.e0327') for system in ('py', 'lean', 'wl')}
        except (Unsupported, ZeroDivisionError):
            continue
        accepted.append((row, relations, expressions))
    lean = ['import Mathlib', f'namespace Chapter{chapter:02}SourceArithmetic']
    py = ['from fractions import Fraction as F', 'import math', 'import json', 'results = []', 'def check(identity, value):', '    results.append({"id": identity, "passed": bool(value)})']
    wl = ['ClearAll["Global`*"];', 'results={};', 'check[id_,value_]:=AppendTo[results,<|"id"->id,"passed"->TrueQ[value]|>];']
    for row, relations, expressions in accepted:
        name = row['id'].replace('.', '_')
        lean.extend([f'theorem {name} : {expressions["lean"]} := by norm_num', f'#print axioms {name}'])
        py.append(f'check({row["id"]!r}, {expressions["py"]})')
        wl.append(f'check["{row["id"]}", {expressions["wl"]}];')
    lean.append(f'end Chapter{chapter:02}SourceArithmetic')
    py.extend(['report = {"checks":len(results),"passed":all(item["passed"] for item in results),"results":results}', 'print(json.dumps(report))', 'raise SystemExit(0 if report["passed"] else 1)'])
    wl.extend(['Print[ExportString[<|"checks"->Length[results],"passed"->And@@Lookup[results,"passed"],"results"->results|>,"RawJSON"]];', 'Exit[If[And@@Lookup[results,"passed"],0,1]];'])
    return {'Aritmetica.lean':'\n'.join(lean)+'\n', 'aritmetica.py':'\n'.join(py)+'\n', 'aritmetica.wl':'\n'.join(wl)+'\n'}, accepted

def records(chapter, rows):
    files, accepted = generated(chapter, rows)
    result = []
    for row, relations, expressions in accepted:
        result.append({'ids':[row['id']], 'proposicao':row['expression'], 'hipoteses':['Aritmética racional exata; todos os denominadores são não nulos; fatoriais e expoentes respeitam os domínios verificados pelo transcritor.', 'Cada aproximação tem erro absoluto no máximo igual à metade da última casa decimal impressa.'] if any(x[0]=='~' for x in relations) else ['Aritmética racional exata; todos os denominadores são não nulos; fatoriais e expoentes respeitam os domínios verificados pelo transcritor.'], 'alcance':'completa', 'testemunhas':{'py':[{'arquivo':'aritmetica.py','nome':row['id'],'metodo':'calculo_exato'}], 'wl':[{'arquivo':'aritmetica.wl','nome':row['id'],'metodo':'calculo_exato'}], 'lean':[{'arquivo':'Aritmetica.lean','nome':f'Chapter{chapter:02}SourceArithmetic.'+row['id'].replace('.','_'),'metodo':'prova_geral'}]}, 'pendencias':{}, 'vinculo':'transcricao_integral_reproduzivel', 'sha256':row['sha256'], 'context_sha256':row['context_sha256']})
        if row['id']=='c08.e0327':
            result[-1]['proposicao']='¬ (0 ≥ 2)'
            result[-1]['hipoteses'].append('O livro apresenta 0 ≥ 2 como contradição intencional da conjunção de duas condições de margem; os três sistemas refutam essa desigualdade, não a afirmam.')
    return result
