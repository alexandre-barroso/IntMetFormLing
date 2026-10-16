from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from capitulo_01 import somas_finitas as s
from capitulo_07 import gram_geral as gram
from capitulo_07.probabilidade_geral import *


def count(xs):
    i = V('count_index', s.INDEX)
    return s.total(xs, Lam(i, RONE))


def foundations():
    x, y, d = V('average_x', 'R'), V('average_y', 'R'), V('average_d', 'R')
    return {
        'average_one_positive': Lt(RZERO, RONE),
        'average_positive_sum': alls((x, y), imps((Lt(RZERO, x), Le(RZERO, y)), Lt(RZERO, Add(x, y)))),
        'average_division_positive': alls((x, d), imps((Lt(RZERO, x), Lt(RZERO, d)), Lt(RZERO, Div(x, d)))),
        'average_division_self': All(d, Imp(Lt(RZERO, d), Eq(Div(d, d), RONE))),
        'average_division_scale': alls((x, d), Imp(Lt(RZERO, d), Eq(Div(x, d), Mul(Div(RONE, d), x)))),
        'average_division_zero': All(d, Imp(Lt(RZERO, d), Eq(Div(RZERO, d), RZERO))),
    } | gram.foundations()


def derive_monotone(kernel):
    xs, t = V('monotone_list', s.LIST), V('monotone_tail', s.LIST)
    h, i = V('monotone_head', s.INDEX), V('monotone_index', s.INDEX)
    f, g = V('monotone_f', s.FUNCTION), V('monotone_g', s.FUNCTION)
    p = Lam(i, Le(A(f, i), A(g, i)))
    result = lambda ys: Imp(s.every(ys, p), Le(s.total(ys, f), s.total(ys, g)))
    body = alls((f, g), result(xs))
    base = s.transformed(kernel, Le(s.total(s.NIL, f), s.total(s.NIL, g)), [ax('sum_nil', f), ax('sum_nil', g)], lambda _: ax('real_order_reflexive', RZERO))
    base = close(base, (f, g), (s.every(s.NIL, p),))
    ih = substitute(body, xs, t)
    assumption = s.every(A(s.CONS, h, t), p)
    split = rewrite(kernel, hyp(assumption), ax('every_cons', p, h, t))
    tail = apply(instantiate(hyp(ih), f, g), ('and_r', split))
    step = apply(ax('addition_monotone', A(f, h), A(g, h), s.total(t, f), s.total(t, g)), ('and_l', split), tail)
    step = rewrite(kernel, step, ax('sum_cons', f, h, t), True)
    step = rewrite(kernel, step, ax('sum_cons', g, h, t), True)
    step = close(close(step, (f, g), (assumption,)), (h, t), (ih,))
    kernel.theorem('finite_sum_monotone', All(xs, body), ('list_induction', xs, h, t, body, base, step))


def derive_normalization(kernel):
    xs, head = V('weight_list', s.LIST), V('weight_head', s.INDEX)
    f = V('weight_function', s.FUNCTION)
    i, d = V('weight_index', s.INDEX), V('weight_denominator', 'R')
    pos = Lam(i, Lt(RZERO, A(f, i)))
    nneg = Lam(i, Le(RZERO, A(f, i)))
    everypos = s.every(xs, pos)
    point = close(ax('positive_implies_nonnegative', A(f, i)), (i,))
    nonnegative = apply(ref('finite_every_implication', xs, pos, nneg), ('conversion', All(i, Imp(A(pos, i), A(nneg, i))), point), hyp(everypos))
    tailpos = apply(ref('finite_sum_nonnegative', xs, f), nonnegative)
    headpos = Lt(RZERO, A(f, head))
    totalpos = apply(ax('average_positive_sum', A(f, head), s.total(xs, f)), hyp(headpos), tailpos)
    totalpos = rewrite(kernel, totalpos, ax('sum_cons', f, head, xs), True)
    statement = alls((xs, f, head), imps((headpos, everypos), Lt(RZERO, s.total(A(s.CONS, head, xs), f))))
    kernel.theorem('finite_positive_nonempty_sum', statement, close(totalpos, (xs, f, head), (headpos, everypos)))
    weights = Lam(i, Div(A(f, i), d))
    scaled = Lam(i, Mul(Div(RONE, d), A(f, i)))
    pd = Lt(RZERO, d)
    equality = Lam(i, Eq(A(weights, i), A(scaled, i)))
    equality_all = close(apply(ax('average_division_scale', A(f, i), d), hyp(pd)), (i,))
    all_equal = apply(ref('finite_every_from_all', xs, equality), ('conversion', All(i, A(equality, i)), equality_all))
    sums_equal = apply(ref('finite_sum_congruence', xs, weights, scaled), all_equal)
    scale = ref('finite_sum_scale', xs, f, Div(RONE, d))
    sums_equal = eq_trans(s.total(xs, weights), s.total(xs, scaled), Mul(Div(RONE, d), s.total(xs, f)), sums_equal, scale)
    sums_equal = rewrite(kernel, sums_equal, apply(ax('average_division_scale', s.total(xs, f), d), hyp(pd)), True)
    kernel.theorem('finite_sum_division', alls((xs, f, d), Imp(pd, Eq(s.total(xs, weights), Div(s.total(xs, f), d)))), close(sums_equal, (xs, f, d), (pd,)))
    z = s.total(xs, f)
    pz = Lt(RZERO, z)
    normalized = Lam(i, Div(A(f, i), z))
    normsum = apply(ref('finite_sum_division', xs, f, z), hyp(pz))
    normsum = rewrite(kernel, normsum, apply(ax('average_division_self', z), hyp(pz)))
    kernel.theorem('finite_normalization_sum_one', alls((xs, f), Imp(pz, Eq(s.total(xs, normalized), RONE))), close(normsum, (xs, f), (pz,)))
    normalizedpos = Lam(i, Lt(RZERO, A(normalized, i)))
    eachpositive = close(apply(ax('average_division_positive', A(f, i), z), hyp(Lt(RZERO, A(f, i))), hyp(pz)), (i,), (Lt(RZERO, A(f, i)),))
    result = apply(ref('finite_every_implication', xs, pos, normalizedpos), ('conversion', All(i, Imp(A(pos, i), A(normalizedpos, i))), eachpositive), hyp(everypos))
    statement = alls((xs, f), imps((pz, everypos), s.every(xs, normalizedpos)))
    kernel.theorem('finite_normalization_positive', statement, close(result, (xs, f), (pz, everypos)))


def derive_average(kernel):
    xs, f, i = V('macro_list', s.LIST), V('macro_scores', s.FUNCTION), V('macro_index', s.INDEX)
    ones = Lam(i, RONE)
    low = Lam(i, Le(RZERO, A(f, i)))
    high = Lam(i, Le(A(f, i), RONE))
    conditions = (Lt(RZERO, count(xs)), s.every(xs, low), s.every(xs, high))
    positive_count = hyp(conditions[0])
    nn = apply(ref('finite_sum_nonnegative', xs, f), hyp(conditions[1]))
    upper = apply(ref('finite_sum_monotone', xs, f, ones), ('conversion', s.every(xs, Lam(i, Le(A(f, i), A(ones, i)))), hyp(conditions[2])))
    up = apply(('and_r', apply(ax('gram_division_order', count(xs), s.total(xs, f), RONE), positive_count)), rewrite(kernel, upper, ring(Mul(RONE, count(xs)), count(xs)), True))
    lo = apply(('and_r', apply(ax('gram_order_division', count(xs), s.total(xs, f), RZERO), positive_count)), rewrite(kernel, nn, ring(Mul(RZERO, count(xs)), RZERO), True))
    result = And(Le(RZERO, Div(s.total(xs, f), count(xs))), Le(Div(s.total(xs, f), count(xs)), RONE))
    kernel.theorem('finite_macro_average_range', alls((xs, f), imps(conditions, result)), close(('and_i', lo, up), (xs, f), conditions))


def derive_softmax(kernel):
    exp = C('real_exp', FT('R', 'R'))
    x = V('exponential_value', 'R')
    add_axioms(kernel, {'real_exponential_positive': All(x, Lt(RZERO, A(exp, x)))})
    head, tail, f, i = V('softmax_head', s.INDEX), V('softmax_tail', s.LIST), V('softmax_scores', s.FUNCTION), V('softmax_index', s.INDEX)
    xs = A(s.CONS, head, tail)
    weights = Lam(i, A(exp, A(f, i)))
    positive = Lam(i, Lt(RZERO, A(weights, i)))
    each = close(ax('real_exponential_positive', A(f, i)), (i,))
    alltail = apply(ref('finite_every_from_all', tail, positive), ('conversion', All(i, A(positive, i)), each))
    headpos = ax('real_exponential_positive', A(f, head))
    zpos = apply(ref('finite_positive_nonempty_sum', tail, weights, head), ('conversion', Lt(RZERO, A(weights, head)), headpos), alltail)
    allpositive = apply(ref('finite_every_from_all', xs, positive), ('conversion', All(i, A(positive, i)), each))
    one = apply(ref('finite_normalization_sum_one', xs, weights), zpos)
    positives = apply(ref('finite_normalization_positive', xs, weights), zpos, allpositive)
    result = ('and_i', zpos, ('and_i', one, positives))
    statement = alls((head, tail, f), kernel.infer(result).conclusion)
    kernel.theorem('attention_softmax_row_general', statement, close(result, (head, tail, f)))


def certificates():
    kernel = s.certificates()
    add_axioms(kernel, foundations())
    derive_monotone(kernel)
    derive_normalization(kernel)
    derive_average(kernel)
    derive_softmax(kernel)
    return kernel


def verify():
    kernel = certificates()
    results = []
    def check(name, condition):
        if not condition:
            raise AssertionError(name)
        results.append({'id': name, 'passed': True})
    check('finite_positive_nonempty_sum', 'finite_positive_nonempty_sum' in kernel.verified)
    check('finite_normalization_sum_one', 'finite_normalization_sum_one' in kernel.verified)
    check('finite_normalization_positive', 'finite_normalization_positive' in kernel.verified)
    check('attention_softmax_row_general', 'attention_softmax_row_general' in kernel.verified)
    check('finite_macro_average_range', 'finite_macro_average_range' in kernel.verified)
    check('reject_zero_normalization_denominator', rejects(lambda: kernel.infer(apply(ref('finite_sum_division', s.NIL, V('test_weights', s.FUNCTION), RZERO), ax('real_order_reflexive', RZERO)))))
    return {'passed': True, 'results': results, 'scope': 'Arbitrary finite sequences; positive nonempty sums, normalization and macro-average bounds, with strictly positive denominator and all score bounds explicit.', 'axioms': list(kernel.axioms)}


if __name__ == '__main__':
    print(json.dumps(verify()))
