import json
import sympy as s

results = []

def check(name, condition):
    results.append({'id': name, 'passed': bool(condition)})

a, b, c, x, y, u, v = s.symbols('a b c x y u v', real=True)
check('lagrange_empty', (a*b-c*c).subs({a: 0, b: 0, c: 0}) == 0)
check('lagrange_append', s.expand((a+x*x)*(b+y*y)-(c+x*y)**2-(a*b-c*c)-(y*y*a+x*x*b-2*x*y*c)) == 0)
check('lagrange_cross_term', s.expand((u*y-v*x)**2-(y*y*u*u+x*x*v*v-2*x*y*u*v)) == 0)
check('lagrange_square_nonnegative', s.ask(s.Q.nonnegative((u*y-v*x)**2)) is True)
d, t = s.symbols('d t', positive=True)
check('positive_side_excludes_above_one', s.expand((d+t)**2-d*d) == 2*d*t+t*t and (2*d*t+t*t).is_positive is True)
check('negative_side_excludes_below_minus_one', s.expand((-d-t)**2-d*d) == 2*d*t+t*t and (2*d*t+t*t).is_positive is True)
n = s.symbols('n', integer=True, positive=True)
m = s.symbols('m', real=True)
check('constant_vector_centering', s.cancel(n*m/n-m) == 0)
nonzero = s.symbols('nonzero', real=True, nonzero=True)
tail = s.symbols('tail', nonnegative=True)
positive_tail = s.symbols('positive_tail', positive=True)
check('nonzero_coordinate_forces_positive_square_sum', (nonzero**2+tail).is_positive is True)
check('positive_tail_forces_positive_square_sum', (x*x+positive_tail).is_positive is True)
check('all_zero_coordinates_give_zero_square_sum_step', s.expand(s.Integer(0)**2+0) == 0)
X = tuple(map(s.Rational, (-1, 0, 1)))
Y = tuple(map(s.Rational, (1, 0, 1)))
mx, my = sum(X)/3, sum(Y)/3
xx = sum((q-mx)**2 for q in X)
yy = sum((q-my)**2 for q in Y)
xy = sum((p-mx)*(q-my) for p, q in zip(X, Y))
check('countermodel_nonlinear', all(q == p*p for p, q in zip(X, Y)))
check('countermodel_nonzero_dispersions', xx == 2 and yy == s.Rational(2, 3))
check('countermodel_zero_pearson', xy/s.sqrt(xx*yy) == 0)
intercept, slope = s.symbols('intercept slope', real=True)
check('countermodel_no_affine_relation', s.linsolve([intercept+slope*p-q for p, q in zip(X, Y)], (intercept, slope)) == s.EmptySet)
px = s.Rational(sum(p == 0 for p in X), 3)
py = s.Rational(sum(q == 0 for q in Y), 3)
joint = s.Rational(sum(p == 0 and q == 0 for p, q in zip(X, Y)), 3)
check('countermodel_dependent', joint == s.Rational(1, 3) and px*py == s.Rational(1, 9) and joint != px*py)
report = {'backend': 'Python 3/SymPy', 'scope': 'Algebraic induction certificates for Lagrange identity and scalar bounds; exact nonlinear dependence countermodel. Finite-dimensional Pearson theorem is checked in Lean.', 'checks': len(results), 'passed': all(r['passed'] for r in results), 'results': results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
