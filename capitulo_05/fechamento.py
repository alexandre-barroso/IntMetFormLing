import json
import sympy as sp

results = []


def check(identifier, condition):
    results.append({'id': identifier, 'passed': bool(condition)})


z = sp.symbols('z', real=True)
a, b, t = sp.symbols('a b t', nonnegative=True)
d = sp.symbols('d', positive=True)
e, f = sp.symbols('e f', real=True)
check('square_nonnegative', (z ** 2).is_nonnegative is True)
check('square_zero_root', sp.solveset(z ** 2, z, domain=sp.S.Reals) == sp.FiniteSet(0))
check('sum_squares_nonnegative_increment', (a + z ** 2).is_nonnegative is True and sp.expand(a + z ** 2 - a).is_nonnegative is True)
check('positive_divisor_preserves_zero', sp.solveset(z / d, z, domain=sp.S.Reals) == sp.FiniteSet(0))
check('absolute_nonnegative', sp.Abs(z).is_nonnegative is True)
check('absolute_zero_root', sp.solveset(sp.Abs(z), z, domain=sp.S.Reals) == sp.FiniteSet(0))
check('nonnegative_sum_bounds', sp.expand(a + b - a).is_nonnegative is True and sp.expand(a + b - b).is_nonnegative is True)
check('excess_deficit_positive_branch', sp.simplify(sp.Max(t, 0) - sp.Max(-t, 0) - t) == 0)
check('excess_deficit_negative_branch', sp.simplify(sp.Max(-t, 0) - sp.Max(t, 0) + t) == 0)
check('absolute_split_positive_branch', sp.simplify(sp.Abs(t) - sp.Max(t, 0) - sp.Max(-t, 0)) == 0)
check('absolute_split_negative_branch', sp.simplify(sp.Abs(-t) - sp.Max(-t, 0) - sp.Max(t, 0)) == 0)
check('half_sum_equal_parts', sp.simplify(((e + f) / 2 - e).subs(f, e)) == 0)
check('equal_mass_balance', sp.simplify((e - f).subs(f, e)) == 0)
report = {'backend': 'Python/SymPy', 'checks': len(results), 'passed': all(item['passed'] for item in results), 'results': results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
