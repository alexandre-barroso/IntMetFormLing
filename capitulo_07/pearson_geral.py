from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from capitulo_01 import somas_finitas as s
from capitulo_05 import triplice as variance
from capitulo_07 import gram_geral as gram
from capitulo_08 import medias_gerais as averages
from capitulo_07.probabilidade_geral import *


def centered(xs, f):
    i = V('centered_index', s.INDEX)
    return Lam(i, Sub(A(f, i), Div(s.total(xs, f), averages.count(xs))))


def derive_pearson(kernel):
    sqrt = C('positive_square_root', FT('R', 'R'))
    value = V('root_value', 'R')
    add_axioms(kernel, {'positive_square_root_definition': All(value, Imp(Lt(RZERO, value), And(Lt(RZERO, A(sqrt, value)), Eq(gram.square(A(sqrt, value)), value))))})
    xs, f, g = V('pearson_list', s.LIST), V('pearson_x', s.FUNCTION), V('pearson_y', s.FUNCTION)
    u, v = centered(xs, f), centered(xs, g)
    aa, bb, cc = s.total(xs, gram.squared(u)), s.total(xs, gram.squared(v)), s.total(xs, gram.product(u, v))
    conditions = (Lt(RZERO, aa), Lt(RZERO, bb))
    product_positive = apply(ax('gram_positive_product', aa, bb), hyp(conditions[0]), hyp(conditions[1]))
    root = apply(ax('positive_square_root_definition', Mul(aa, bb)), product_positive)
    result = apply(ref('finite_normalized_dot_range', xs, u, v, A(sqrt, Mul(aa, bb))), hyp(conditions[0]), hyp(conditions[1]), ('and_l', root), ('and_r', root))
    statement = alls((xs, f, g), imps(conditions, kernel.infer(result).conclusion))
    kernel.theorem('finite_pearson_centered_range', statement, close(result, (xs, f, g), conditions))


def derive_sxx(kernel):
    h, t, f, i, j = V('sxx_head', s.INDEX), V('sxx_tail', s.LIST), V('sxx_values', s.FUNCTION), V('sxx_i', s.INDEX), V('sxx_j', s.INDEX)
    xs = A(s.CONS, h, t)
    count = averages.count(xs)
    mean = Div(s.total(xs, f), count)
    positive_count = Lt(RZERO, count)
    dev = Lam(i, Mul(Sub(A(f, i), mean), Sub(A(f, i), mean)))
    sxx = s.total(xs, dev)
    eqmean = Lam(i, Eq(A(f, i), mean))
    inner = Lam(i, s.every(xs, Lam(j, Eq(A(f, i), A(f, j)))))
    pairwise = s.every(xs, inner)
    allmean = s.every(xs, eqmean)
    scalar_i, scalar_j = Eq(A(f, i), mean), Eq(A(f, j), mean)
    eqij = eq_trans(A(f, i), mean, A(f, j), hyp(scalar_i), symmetric(A(f, j), mean, hyp(scalar_j)))
    all_j = close(eqij, (j,), (scalar_j,))
    inner_i = apply(ref('finite_every_implication', xs, eqmean, Lam(j, Eq(A(f, i), A(f, j)))), all_j, hyp(allmean))
    each_i = close(inner_i, (i,), (scalar_i,))
    allpairs = apply(ref('finite_every_implication', xs, eqmean, inner), each_i, hyp(allmean))
    pair_from_mean = close(allpairs, assumptions=(allmean,))
    extract = rewrite(kernel, hyp(pairwise), ax('every_cons', inner, h, t))
    head_equal = ('and_l', extract)
    eqhead = Lam(i, Eq(A(f, i), A(f, h)))
    scalar_head = Eq(A(f, h), A(f, i))
    sym = close(symmetric(A(f, h), A(f, i), hyp(scalar_head)), (i,), (scalar_head,))
    constant_all = apply(ref('finite_every_implication', xs, Lam(i, Eq(A(f, h), A(f, i))), eqhead), sym, head_equal)
    constant = Lam(i, A(f, h))
    sum_eq = apply(ref('finite_sum_congruence', xs, f, constant), ('conversion', s.every(xs, Lam(i, Eq(A(f, i), A(constant, i)))), constant_all))
    constant_sum = ref('finite_sum_constant', xs, A(f, h))
    sum_eq = eq_trans(s.total(xs, f), s.total(xs, constant), Mul(A(f, h), count), sum_eq, constant_sum)
    variable = V('sxx_sum_replace', 'R')
    mean_equal = ('eq_e', sum_eq, variable, Eq(Div(s.total(xs, f), count), Div(variable, count)), ('eq_i', mean))
    cancellation = apply(ax('positive_division_cancel', A(f, h), count), hyp(positive_count))
    mean_equal = rewrite(kernel, mean_equal, cancellation)
    mean_eqhead = symmetric(mean, A(f, h), mean_equal)
    values_mean = rewrite(kernel, constant_all, mean_eqhead)
    zero_characterization = ref('finite_squared_deviations_zero_iff', xs, f, mean)
    zero = Eq(sxx, RZERO)
    zero_to_pair = apply(pair_from_mean, apply(('and_l', zero_characterization), hyp(zero)))
    pair_to_zero = apply(('and_r', zero_characterization), values_mean)
    iff = ('and_i', close(zero_to_pair, assumptions=(zero,)), close(pair_to_zero, assumptions=(pairwise,)))
    formula = alls((h, t, f), Imp(positive_count, Iff(zero, pairwise)))
    kernel.theorem('finite_sxx_zero_iff_pairwise_equal', formula, close(iff, (h, t, f), (positive_count,)))
    all_nonnegative = close(ref('square_nonnegative_general', Sub(A(f, i), mean)), (i,))
    nonnegative_pred = Lam(i, Le(RZERO, A(dev, i)))
    every_nonnegative = apply(ref('finite_every_from_all', xs, nonnegative_pred), ('conversion', All(i, A(nonnegative_pred, i)), all_nonnegative))
    nn = apply(ref('finite_sum_nonnegative', xs, dev), every_nonnegative)
    positive = Lt(RZERO, sxx)
    notpair = Imp(pairwise, BOTTOM)
    zero_under_pair = apply(('and_r', apply(ref('finite_sxx_zero_iff_pairwise_equal', h, t, f), hyp(positive_count))), hyp(pairwise))
    invalid_positive = rewrite(kernel, hyp(positive), zero_under_pair)
    contradiction = apply(ax('real_strict_nonstrict_inconsistent', RZERO, RZERO), invalid_positive, ax('real_order_reflexive', RZERO))
    forward = close(close(contradiction, assumptions=(pairwise,)), assumptions=(positive,))
    choices = apply(ax('nonnegative_zero_or_positive', sxx), nn)
    pair_under_zero = apply(('and_l', apply(ref('finite_sxx_zero_iff_pairwise_equal', h, t, f), hyp(positive_count))), hyp(zero))
    badzero = apply(hyp(notpair), pair_under_zero)
    backward = ('or_e', choices, ('false_e', positive, badzero), hyp(positive))
    backward = close(backward, assumptions=(notpair,))
    result = Iff(positive, notpair)
    kernel.theorem('finite_sxx_positive_iff_nonconstant', alls((h, t, f), Imp(positive_count, result)), close(('and_i', forward, backward), (h, t, f), (positive_count,)))


def certificates():
    kernel = variance.certificates()
    add_axioms(kernel, gram.foundations())
    gram.derive_squares(kernel)
    gram.derive_quadratic(kernel)
    gram.derive_normalized(kernel)
    derive_pearson(kernel)
    derive_sxx(kernel)
    return kernel


def verify():
    kernel = certificates()
    results = []
    def check(name, condition):
        if not condition:
            raise AssertionError(name)
        results.append({'id': name, 'passed': True})
    check('finite_squared_deviations_zero_iff', 'finite_squared_deviations_zero_iff' in kernel.verified)
    check('finite_pearson_centered_range', 'finite_pearson_centered_range' in kernel.verified)
    check('finite_sxx_zero_iff_pairwise_equal', 'finite_sxx_zero_iff_pairwise_equal' in kernel.verified)
    check('finite_sxx_positive_iff_nonconstant', 'finite_sxx_positive_iff_nonconstant' in kernel.verified)
    return {'passed': True, 'results': results, 'scope': 'Arbitrary finite real samples. Pearson uses the positive square root of two strictly positive centered square sums. Sxx vanishes exactly for pairwise identical entries and is positive exactly when they are not all equal; nonempty sample and positive count are explicit.'}


if __name__ == '__main__':
    print(json.dumps(verify()))
