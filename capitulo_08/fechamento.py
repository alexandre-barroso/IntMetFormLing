import itertools
import json
import sympy as s
from sympy.logic.inference import satisfiable

results = []

def check(name, condition):
    results.append({'id': name, 'passed': bool(condition)})

a, b, prefix, suffix = s.symbols('a b prefix suffix', real=True)
n = s.symbols('n', integer=True, positive=True)
check('context_adjacent_transposition', s.cancel((prefix+a+b+suffix)/n-(prefix+b+a+suffix)/n) == 0)
check('context_denominator_positive', n.is_positive is True)
v = s.symbols('v0:4', real=True)
check('context_all_four_permutations', all(s.expand(sum(p)/4-sum(v)/4) == 0 for p in itertools.permutations(v)))
profiles = ((2, 0), (1, 1), (1, 1), (0, 2))
w1, w2 = s.symbols('w1 w2', real=True)
harmony = tuple(-w1*p[0]-w2*p[1] for p in profiles)
check('potts_exact_profiles', harmony == (-2*w1, -w1-w2, -w1-w2, -2*w2))
check('potts_complete_deletion_hg', all(satisfiable(s.And(w1 > w2, harmony[3] <= h), use_lra_theory=True) is False for h in harmony[:3]))
check('potts_complete_deletion_ot', all(profiles[3] < p for p in profiles[:3]))
check('squared_distance_triangle_fails', (s.Rational(0)-2)**2 > (s.Rational(0)-1)**2+(s.Rational(1)-2)**2)
projection = s.Matrix([[1, 0]])
x, y = s.Matrix([1, 0]), s.Matrix([1, 1])
check('projection_collapses_distinct_vectors', x != y and projection*x == projection*y)
def erase_boundaries(sequence):
    return tuple(c for c in sequence if c != '-')

check('erasure_empty', erase_boundaries(()) == ())
head = s.Symbol('head')
tail = (s.Symbol('tail_erased'),)
check('erasure_kept_nonmarker_step', erase_boundaries((head,)+tail) == (head,)+erase_boundaries(tail))
check('erasure_marker_step', erase_boundaries(('-',)+tail) == erase_boundaries(tail))
check('canonical_requires_nonboundary_change', erase_boundaries('Cylinder-ical-ly') != erase_boundaries('Cylindrically'))
v0, va, vb, vab = map(s.Rational, (1, 0, 1, 0))
phi_a = ((va-v0)+(vab-vb))/2
check('shapley_valid_performances', all(0 <= v <= 1 for v in (v0, va, vb, vab)))
check('shapley_negative_contribution', phi_a == -1 and phi_a < 0)
report = {'backend': 'Python 3/SymPy', 'scope': 'General adjacent-transposition identity and complete four-neighbor permutation check; exact Potts profiles with general weight inequalities; exact distance countermodels. Arbitrary finite permutation theorem is checked in Lean.', 'checks': len(results), 'passed': all(r['passed'] for r in results), 'results': results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
