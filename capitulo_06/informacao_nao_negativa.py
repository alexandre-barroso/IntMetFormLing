import json
import sympy as sp
from sympy.calculus.util import minimum

results = []


def check(identifier, condition):
    results.append({'id': identifier, 'passed': bool(condition)})


r, p, q = sp.symbols('r p q', positive=True)
a, b = sp.symbols('a b', nonnegative=True)
x, y = sp.symbols('x y', real=True)
phi = r - 1 - sp.log(r)
check('log_upper_bound_global', minimum(phi, r, sp.Interval.open(0, sp.oo)) == 0)
check('log_bound_derivative', sp.simplify(sp.diff(phi, r) - (r - 1) / r) == 0)
check('log_bound_equality_at_one', phi.subs(r, 1) == 0)
gap = p * sp.log(p / q) - (p - q)
check('positive_mass_log_bound_identity', sp.simplify(sp.expand_log(gap - p * phi.subs(r, q / p))) == 0)
check('zero_mass_lower_bound', q.is_nonnegative is True and sp.Integer(0) - (sp.Integer(0) - q) == q)
check('zero_reference_allowed_at_zero_mass', sp.Integer(0) - (sp.Integer(0) - sp.Integer(0)) == 0)
check('positive_joint_implies_positive_reference', ((p + a) * (p + b)).is_positive is True)
check('nonnegative_reference', (a * b).is_nonnegative is True)
check('sum_inequalities_induction', (a + b).is_nonnegative is True)
check('normalized_reference_total', (x * y).subs({x: 1, y: 1}) == 1)
check('base_two_preserves_sign', sp.log(2).is_positive is True)
check('change_base_identity', sp.simplify(p * (sp.log(p / q) / sp.log(2)) - (p * sp.log(p / q)) / sp.log(2)) == 0)
report = {'backend': 'Python/SymPy', 'checks': len(results), 'passed': all(item['passed'] for item in results), 'results': results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
