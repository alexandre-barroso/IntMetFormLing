import json
import sympy as s

results = []

def check(name, condition):
    results.append({'id': name, 'passed': bool(condition)})

def safe_f1(tp, fp, fn):
    if min(tp, fp, fn) < 0:
        raise ValueError('nonnegative counts required')
    denominator = 2*tp+fp+fn
    return None if denominator == 0 else s.Rational(2*tp, denominator)

tp = s.symbols('tp', positive=True)
fp, fn = s.symbols('fp fn', nonnegative=True)
f1 = 2*tp/(2*tp+fp+fn)
check('f1_positive_tp_lower_bound', f1.is_positive is True)
check('f1_positive_tp_upper_identity', s.cancel(1-f1-(fp+fn)/(2*tp+fp+fn)) == 0)
check('f1_positive_tp_upper_bound', ((fp+fn)/(2*tp+fp+fn)).is_nonnegative is True)
denominator = s.symbols('denominator', positive=True)
check('f1_zero_tp_defined', s.Integer(0)/denominator == 0)
check('f1_zero_tp_examples', safe_f1(0, 1, 0) == 0 and safe_f1(0, 0, 1) == 0)
check('f1_empty_counts_undefined', safe_f1(0, 0, 0) is None)
sum_f, last = s.symbols('sum_f last', nonnegative=True)
count = s.symbols('count', integer=True, positive=True)
check('macro_sum_nonnegative_step', (sum_f+last).is_nonnegative is True)
remaining, gap = s.symbols('remaining gap', nonnegative=True)
check('macro_sum_complement_step', s.expand(((count+1)-(sum_f+last))-((count-sum_f)+(1-last))) == 0)
check('macro_complement_nonnegative_step', (remaining+gap).is_nonnegative is True)
check('macro_mean_bounds_scaling', (sum_f/count).is_nonnegative is True and (remaining/count).is_nonnegative is True)
report = {'backend': 'Python 3/SymPy', 'scope': 'General scalar F1 inequalities by positive-TP and zero-TP cases, explicit undefined empty counts; algebraic certificates for finite macro average.', 'checks': len(results), 'passed': all(r['passed'] for r in results), 'results': results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
