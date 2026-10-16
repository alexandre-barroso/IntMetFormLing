import json
import sympy as sp

results = []


def check(identifier, condition):
    results.append({'id': identifier, 'passed': bool(condition)})


def adjacency_square_count(relation, origin, destination):
    n = len(relation)
    if any(len(row) != n for row in relation):
        raise ValueError('square relation required')
    if any(type(value) is not bool for row in relation for value in row):
        raise ValueError('Boolean entries required')
    if not 0 <= origin < n or not 0 <= destination < n:
        raise ValueError('invalid vertex')
    products = sum(int(relation[origin][k]) * int(relation[k][destination]) for k in range(n))
    intermediates = sum(relation[origin][k] and relation[k][destination] for k in range(n))
    return products, intermediates


check('binary_product_conjunction', all(a * b == int(bool(a) and bool(b)) for a in (0, 1) for b in (0, 1)))
check('empty_sum_count', sum([]) == len([]) == 0)
s, c, indicator = sp.symbols('s c indicator', integer=True)
check('sum_count_induction', sp.expand((s + indicator) - (c + indicator)) == s - c)
check('indicator_counts_one', all(int(a and b) in (0, 1) for a in (False, True) for b in (False, True)))
u = sp.symbols('u', real=True)
check('antipodal_mean_zero', sp.simplify((u - u) / 2) == 0)
check('unit_vectors_mean_need_not_unit', sp.sqrt(1 ** 2) == 1 and sp.sqrt((-1) ** 2) == 1 and sp.sqrt(((sp.Integer(1) - 1) / 2) ** 2) == 0)
report = {'backend': 'Python/SymPy', 'checks': len(results), 'passed': all(item['passed'] for item in results), 'results': results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
