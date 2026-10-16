from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from capitulo_08 import medias_gerais as m
from capitulo_01 import somas_finitas as s
from capitulo_07.probabilidade_geral import *


def conjunction(values):
    result = values[-1]
    for value in reversed(values[:-1]):
        result = And(value, result)
    return result


def unpack(proof, size):
    result = []
    for _ in range(size - 1):
        result.append(('and_l', proof))
        proof = ('and_r', proof)
    return result + [proof]


def f1(t, p, n):
    twice = Add(t, t)
    return Div(twice, Add(twice, Add(p, n)))


def certificates():
    kernel = m.certificates()
    t, p, n = (V('count_' + v, 'R') for v in ('tp', 'fp', 'fn'))
    twice, extra = Add(t, t), Add(p, n)
    d = Add(twice, extra)
    assumptions = (Le(RZERO, t), Le(RZERO, p), Le(RZERO, n), Lt(RZERO, d))
    numerator = apply(ax('addition_monotone', RZERO, t, RZERO, t), hyp(assumptions[0]), hyp(assumptions[0]))
    numerator = rewrite(kernel, numerator, ring(Add(RZERO, RZERO), RZERO))
    remainder = apply(ax('addition_monotone', RZERO, p, RZERO, n), hyp(assumptions[1]), hyp(assumptions[2]))
    remainder = rewrite(kernel, remainder, ring(Add(RZERO, RZERO), RZERO))
    upper = apply(ax('addition_monotone', twice, twice, RZERO, extra), ax('real_order_reflexive', twice), remainder)
    upper = rewrite(kernel, upper, ring(Add(twice, RZERO), twice))
    upper = rewrite(kernel, upper, ring(Mul(RONE, d), d), True)
    lower = rewrite(kernel, numerator, ring(Mul(RZERO, d), RZERO), True)
    lo = apply(('and_r', apply(ax('gram_order_division', d, twice, RZERO), hyp(assumptions[3]))), lower)
    hi = apply(('and_r', apply(ax('gram_division_order', d, twice, RONE), hyp(assumptions[3]))), upper)
    target = And(Le(RZERO, f1(t, p, n)), Le(f1(t, p, n), RONE))
    kernel.theorem('f1_nonnegative_counts_range_general', alls((t, p, n), imps(assumptions, target)), close(('and_i', lo, hi), (t, p, n), assumptions))
    xs, i = V('class_list', s.LIST), V('class_index', s.INDEX)
    tp, fp, fn = (V('class_' + v, s.FUNCTION) for v in ('tp', 'fp', 'fn'))
    ti, pi, ni = A(tp, i), A(fp, i), A(fn, i)
    conditions = (Le(RZERO, ti), Le(RZERO, pi), Le(RZERO, ni), Lt(RZERO, Add(Add(ti, ti), Add(pi, ni))))
    valid = Lam(i, conjunction(conditions))
    scores = Lam(i, f1(ti, pi, ni))
    valid_all = s.every(xs, valid)
    each = apply(ref('f1_nonnegative_counts_range_general', ti, pi, ni), *unpack(hyp(conjunction(conditions)), 4))
    low, high = Lam(i, Le(RZERO, A(scores, i))), Lam(i, Le(A(scores, i), RONE))
    low_imp = close(('and_l', each), (i,), (conjunction(conditions),))
    high_imp = close(('and_r', each), (i,), (conjunction(conditions),))
    low_all = apply(ref('finite_every_implication', xs, valid, low), ('conversion', All(i, Imp(A(valid, i), A(low, i))), low_imp), hyp(valid_all))
    high_all = apply(ref('finite_every_implication', xs, valid, high), ('conversion', All(i, Imp(A(valid, i), A(high, i))), high_imp), hyp(valid_all))
    count_positive = Lt(RZERO, m.count(xs))
    result = apply(ref('finite_macro_average_range', xs, scores), hyp(count_positive), low_all, high_all)
    statement = alls((xs, tp, fp, fn), imps((count_positive, valid_all), kernel.infer(result).conclusion))
    kernel.theorem('f1_macro_average_range_general', statement, close(result, (xs, tp, fp, fn), (count_positive, valid_all)))
    return kernel


def verify():
    kernel = certificates()
    results = []
    def check(name, condition):
        if not condition:
            raise AssertionError(name)
        results.append({'id': name, 'passed': True})
    check('f1_nonnegative_counts_range_general', 'f1_nonnegative_counts_range_general' in kernel.verified)
    check('f1_macro_average_range_general', 'f1_macro_average_range_general' in kernel.verified)
    check('reject_invalid_denominator', rejects(lambda: kernel.infer(apply(ref('f1_nonnegative_counts_range_general', RZERO, RZERO, RZERO), *([ax('real_order_reflexive', RZERO)] * 4)))))
    return {'passed': True, 'results': results, 'scope': 'Every finite nonempty family of nonnegative TP/FP/FN counts with each F1 denominator positive; each F1 and their macro-average lie in [0,1].'}


if __name__ == '__main__':
    print(json.dumps(verify()))
