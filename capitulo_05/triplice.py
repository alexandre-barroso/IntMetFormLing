from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from capitulo_01.somas_finitas import *
from capitulo_07.probabilidade_geral import Or, Lt, BOTTOM, eq_trans
import capitulo_01.somas_finitas as sums

ABS = C('real_absolute_value', FT('R', 'R'))
POS = C('real_positive_part', FT('R', 'R'))


def real_axioms():
    x, y, d = V('real_x', 'R'), V('real_y', 'R'), V('real_d', 'R')
    return {
        'real_zero_total_order': All(x, Or(Le(RZERO, x), Le(x, RZERO))),
        'field_zero_product': alls((x, y), Imp(Eq(Mul(x, y), RZERO), Or(Eq(x, RZERO), Eq(y, RZERO)))),
        'positive_denominator_reconstruction': alls((x, d), Imp(Lt(RZERO, d), Eq(Mul(Div(x, d), d), x))),
        'positive_denominator_zero': All(d, Imp(Lt(RZERO, d), Eq(Div(RZERO, d), RZERO))),
        'absolute_nonnegative_branch': All(x, Imp(Le(RZERO, x), Eq(A(ABS, x), x))),
        'absolute_nonpositive_branch': All(x, Imp(Le(x, RZERO), Eq(A(ABS, x), Sub(RZERO, x)))),
        'positive_part_nonnegative_branch': All(x, Imp(Le(RZERO, x), Eq(A(POS, x), x))),
        'positive_part_nonpositive_branch': All(x, Imp(Le(x, RZERO), Eq(A(POS, x), RZERO))),
        'strict_difference_order': alls((x, y), Iff(Lt(x, y), Lt(RZERO, Sub(y, x)))),
        'positive_division_cancel': alls((x, d), Imp(Lt(RZERO, d), Eq(Div(Mul(x, d), d), x))),
    }


def nonnegative_negation(kernel, x, hypothesis):
    premise = rewrite(kernel, hypothesis, ring(Add(RZERO, x), x), reverse=True)
    return apply(ax('addition_right_forward', RZERO, x, RZERO), premise)


def derive_scalar(kernel):
    x, y, d = V('scalar_x', 'R'), V('scalar_y', 'R'), V('scalar_d', 'R')
    hp, hn = Le(RZERO, x), Le(x, RZERO)
    positive = apply(ax('nonnegative_multiplication_monotone', x, RZERO, x), ('assume', hp), ('assume', hp))
    positive = rewrite(kernel, positive, ring(Mul(x, RZERO), RZERO))
    nx = Sub(RZERO, x)
    nx_positive = nonnegative_negation(kernel, x, ('assume', hn))
    negative = apply(ax('nonnegative_multiplication_monotone', nx, RZERO, nx), nx_positive, nx_positive)
    negative = rewrite(kernel, negative, ring(Mul(nx, RZERO), RZERO))
    negative = rewrite(kernel, negative, ring(Mul(nx, nx), Mul(x, x)))
    proof = ('or_e', ax('real_zero_total_order', x), positive, negative)
    kernel.theorem('square_nonnegative_general', All(x, Le(RZERO, Mul(x, x))), close(proof, (x,)))
    hsq = Eq(Mul(x, x), RZERO)
    hz = Eq(x, RZERO)
    choices = apply(ax('field_zero_product', x, x), ('assume', hsq))
    forward = ('or_e', choices, ('assume', hz), ('assume', hz))
    backward = polynomial(kernel, hsq, [('assume', hz)])
    kernel.theorem('square_zero_iff_general', All(x, Iff(hsq, hz)), close(both((close(forward, assumptions=(hsq,)), close(backward, assumptions=(hz,)))), (x,)))
    abs_nonnegative_positive = rewrite(kernel, ('assume', hp), apply(ax('absolute_nonnegative_branch', x), ('assume', hp)), reverse=True)
    abs_nonnegative_negative = rewrite(kernel, nx_positive, apply(ax('absolute_nonpositive_branch', x), ('assume', hn)), reverse=True)
    proof = ('or_e', ax('real_zero_total_order', x), abs_nonnegative_positive, abs_nonnegative_negative)
    kernel.theorem('absolute_nonnegative_general', All(x, Le(RZERO, A(ABS, x))), close(proof, (x,)))
    h_abs = Eq(A(ABS, x), RZERO)
    abs_pos = apply(ax('absolute_nonnegative_branch', x), ('assume', hp))
    abs_neg = apply(ax('absolute_nonpositive_branch', x), ('assume', hn))
    forward_positive = rewrite(kernel, ('assume', h_abs), abs_pos)
    negzero = rewrite(kernel, ('assume', h_abs), abs_neg)
    forward_negative = polynomial(kernel, Eq(Sub(RZERO, Sub(RZERO, x)), RZERO), [negzero])
    forward_negative = rewrite(kernel, forward_negative, ring(Sub(RZERO, Sub(RZERO, x)), x))
    forward = ('or_e', ax('real_zero_total_order', x), forward_positive, forward_negative)
    zero_abs = apply(ax('absolute_nonnegative_branch', RZERO), ax('real_order_reflexive', RZERO))
    backward = transformed(kernel, h_abs, [('assume', hz)], lambda _: zero_abs)
    kernel.theorem('absolute_zero_iff_general', All(x, Iff(h_abs, hz)), close(both((close(forward, assumptions=(h_abs,)), close(backward, assumptions=(hz,)))), (x,)))
    diffzero, equal = Eq(Sub(x, y), RZERO), Eq(x, y)
    forward = polynomial(kernel, Eq(Add(Sub(x, y), y), y), [('assume', diffzero)])
    forward = rewrite(kernel, forward, ring(Add(Sub(x, y), y), x))
    backward = polynomial(kernel, diffzero, [('assume', equal)])
    kernel.theorem('difference_zero_iff_general', alls((x, y), Iff(diffzero, equal)), close(both((close(forward, assumptions=(diffzero,)), close(backward, assumptions=(equal,)))), (x, y)))
    hdiv, denom = Eq(Div(x, d), RZERO), Lt(RZERO, d)
    reconstruction = apply(ax('positive_denominator_reconstruction', x, d), ('assume', denom))
    forward = rewrite(kernel, reconstruction, ('assume', hdiv))
    forward = rewrite(kernel, forward, ring(Mul(RZERO, d), RZERO))
    forward = symmetric(RZERO, x, forward)
    backward = transformed(kernel, hdiv, [('assume', hz)], lambda _: apply(ax('positive_denominator_zero', d), ('assume', denom)))
    kernel.theorem('positive_division_zero_iff_general', alls((x, d), Imp(denom, Iff(hdiv, hz))), close(both((close(forward, assumptions=(hdiv,)), close(backward, assumptions=(hz,)))), (x, d), (denom,)))


def every_equivalence(kernel, xs, p, q, pointwise):
    i = V('equivalence_index', INDEX)
    forward = close(('and_l', instantiate(pointwise, i)), (i,))
    backward = close(('and_r', instantiate(pointwise, i)), (i,))
    a = apply(instantiate(('ref', 'finite_every_implication'), xs, p, q), forward)
    b = apply(instantiate(('ref', 'finite_every_implication'), xs, q, p), backward)
    return both((a, b))


def combine_iff(kernel, first, second):
    first_formula = normalize(kernel.infer(first).conclusion)
    second_formula = normalize(kernel.infer(second).conclusion)
    left = first_formula[1][1]
    middle = first_formula[1][2]
    if not same(middle, second_formula[1][1]):
        raise ValueError('iff chain mismatch')
    right = second_formula[1][2]
    forward = apply(('and_l', second), apply(('and_l', first), ('assume', left)))
    backward = apply(('and_r', first), apply(('and_r', second), ('assume', right)))
    return both((close(forward, assumptions=(left,)), close(backward, assumptions=(right,))))


def derive_zero_measures(kernel):
    xs = V('measure_list', LIST)
    f, g = V('measure_f', FUNCTION), V('measure_g', FUNCTION)
    m, d, i = V('mean', 'R'), V('divisor', 'R'), V('measure_index', INDEX)
    deviation = Sub(A(f, i), m)
    square = Lam(i, Mul(deviation, deviation))
    nonnegative = close(instantiate(('ref', 'square_nonnegative_general'), deviation), (i,))
    nonnegative = apply(instantiate(('ref', 'finite_every_from_all'), xs, Lam(i, Le(RZERO, A(square, i)))), nonnegative)
    sum_zero = apply(instantiate(('ref', 'finite_nonnegative_sum_zero_iff'), xs, square), nonnegative)
    scalar_zero = combine_iff(kernel, instantiate(('ref', 'square_zero_iff_general'), deviation), instantiate(('ref', 'difference_zero_iff_general'), A(f, i), m))
    zero_predicate = Lam(i, Eq(A(square, i), RZERO))
    target_predicate = Lam(i, Eq(A(f, i), m))
    pointwise = close(scalar_zero, (i,))
    transformed_every = every_equivalence(kernel, xs, zero_predicate, target_predicate, pointwise)
    result = combine_iff(kernel, sum_zero, transformed_every)
    formula = alls((xs, f, m), Iff(Eq(total(xs, square), RZERO), every(xs, target_predicate)))
    kernel.theorem('finite_squared_deviations_zero_iff', formula, close(result, (xs, f, m)))
    division = apply(instantiate(('ref', 'positive_division_zero_iff_general'), total(xs, square), d), ('assume', Lt(RZERO, d)))
    combined = combine_iff(kernel, division, instantiate(('ref', 'finite_squared_deviations_zero_iff'), xs, f, m))
    formula = alls((xs, f, m, d), Imp(Lt(RZERO, d), Iff(Eq(Div(total(xs, square), d), RZERO), every(xs, target_predicate))))
    kernel.theorem('finite_normalized_variance_zero_iff', formula, close(combined, (xs, f, m, d), (Lt(RZERO, d),)))
    difference = Sub(A(f, i), A(g, i))
    absolute = Lam(i, A(ABS, difference))
    nonnegative = close(instantiate(('ref', 'absolute_nonnegative_general'), difference), (i,))
    nonnegative = apply(instantiate(('ref', 'finite_every_from_all'), xs, Lam(i, Le(RZERO, A(absolute, i)))), nonnegative)
    sum_zero = apply(instantiate(('ref', 'finite_nonnegative_sum_zero_iff'), xs, absolute), nonnegative)
    scalar_zero = combine_iff(kernel, instantiate(('ref', 'absolute_zero_iff_general'), difference), instantiate(('ref', 'difference_zero_iff_general'), A(f, i), A(g, i)))
    q = Lam(i, Eq(A(f, i), A(g, i)))
    equivalence = every_equivalence(kernel, xs, Lam(i, Eq(A(absolute, i), RZERO)), q, close(scalar_zero, (i,)))
    result = combine_iff(kernel, sum_zero, equivalence)
    formula = alls((xs, f, g), Iff(Eq(total(xs, absolute), RZERO), every(xs, q)))
    kernel.theorem('finite_absolute_differences_zero_iff', formula, close(result, (xs, f, g)))
    denominator = Add(RONE, RONE)
    hd = Lt(RZERO, denominator)
    division = apply(instantiate(('ref', 'positive_division_zero_iff_general'), total(xs, absolute), denominator), ax('two_positive'))
    result = combine_iff(kernel, division, instantiate(('ref', 'finite_absolute_differences_zero_iff'), xs, f, g))
    formula = alls((xs, f, g), Iff(Eq(Div(total(xs, absolute), denominator), RZERO), every(xs, q)))
    kernel.theorem('finite_dispersion_zero_iff', formula, close(result, (xs, f, g)))


def derive_population_sample(kernel):
    xs = V('variance_list', LIST)
    f = V('observations', FUNCTION)
    i = V('variance_index', INDEX)
    n = total(xs, Lam(i, RONE))
    mean = Div(total(xs, f), n)
    for name, divisor, hypothesis in [('finite_population_variance_zero_iff', n, Lt(RZERO, n)), ('finite_sample_variance_zero_iff', Sub(n, RONE), Lt(RONE, n))]:
        positive = ('assume', hypothesis) if divisor == n else apply(('and_l', ax('strict_difference_order', RONE, n)), ('assume', hypothesis))
        proof = apply(instantiate(('ref', 'finite_normalized_variance_zero_iff'), xs, f, mean, divisor), positive)
        formula = alls((xs, f), Imp(hypothesis, kernel.infer(proof).conclusion))
        kernel.theorem(name, formula, close(proof, (xs, f), (hypothesis,)))


def derive_excess(kernel):
    x = V('excess_scalar', 'R')
    nx = Sub(RZERO, x)
    hp, hn = Le(RZERO, x), Le(x, RZERO)
    positive_negation = nonnegative_negation(kernel, x, ('assume', hn))
    negative_negation = apply(ax('addition_monotone', RZERO, x, nx, nx), ('assume', hp), ax('real_order_reflexive', nx))
    negative_negation = rewrite(kernel, negative_negation, ring(Add(RZERO, nx), nx))
    negative_negation = rewrite(kernel, negative_negation, ring(Add(x, nx), RZERO))
    positive_eqs = [apply(ax('positive_part_nonnegative_branch', x), ('assume', hp)), apply(ax('positive_part_nonpositive_branch', nx), negative_negation), apply(ax('absolute_nonnegative_branch', x), ('assume', hp))]
    negative_eqs = [apply(ax('positive_part_nonpositive_branch', x), ('assume', hn)), apply(ax('positive_part_nonnegative_branch', nx), positive_negation), apply(ax('absolute_nonpositive_branch', x), ('assume', hn))]
    for name, formula in [('scalar_excess_deficit', Eq(Sub(A(POS, x), A(POS, nx)), x)), ('scalar_absolute_excess_split', Eq(A(ABS, x), Add(A(POS, x), A(POS, nx))))]:
        positive = polynomial(kernel, formula, positive_eqs)
        negative = polynomial(kernel, formula, negative_eqs)
        proof = ('or_e', ax('real_zero_total_order', x), positive, negative)
        kernel.theorem(name, All(x, formula), close(proof, (x,)))
    xs = V('excess_list', LIST)
    f, g = V('excess_f', FUNCTION), V('excess_g', FUNCTION)
    i = V('excess_index', INDEX)
    difference = Sub(A(f, i), A(g, i))
    excess = Lam(i, A(POS, difference))
    deficit = Lam(i, A(POS, Sub(RZERO, difference)))
    absolute = Lam(i, A(ABS, difference))
    difference_function = Lam(i, difference)
    difference_parts = Lam(i, Sub(A(excess, i), A(deficit, i)))
    pointwise = close(instantiate(('ref', 'scalar_excess_deficit'), difference), (i,))
    p = Lam(i, Eq(A(difference_parts, i), A(difference_function, i)))
    every_eq = apply(instantiate(('ref', 'finite_every_from_all'), xs, p), pointwise)
    equality = apply(instantiate(('ref', 'finite_sum_congruence'), xs, difference_parts, difference_function), every_eq)
    equality = rewrite(kernel, equality, instantiate(('ref', 'finite_sum_subtract'), xs, excess, deficit))
    equality = rewrite(kernel, equality, instantiate(('ref', 'finite_sum_subtract'), xs, f, g))
    kernel.theorem('finite_excess_deficit_difference', alls((xs, f, g), kernel.infer(equality).conclusion), close(equality, (xs, f, g)))
    same_mass = Eq(total(xs, f), total(xs, g))
    zero_difference = rewrite(kernel, equality, ('assume', same_mass))
    zero_difference = rewrite(kernel, zero_difference, ring(Sub(total(xs, g), total(xs, g)), RZERO))
    balance = apply(('and_l', instantiate(('ref', 'difference_zero_iff_general'), total(xs, excess), total(xs, deficit))), zero_difference)
    kernel.theorem('finite_equal_mass_excess_balance', alls((xs, f, g), Imp(same_mass, kernel.infer(balance).conclusion)), close(balance, (xs, f, g), (same_mass,)))
    sum_parts = Lam(i, Add(A(excess, i), A(deficit, i)))
    pointwise = close(instantiate(('ref', 'scalar_absolute_excess_split'), difference), (i,))
    p = Lam(i, Eq(A(absolute, i), A(sum_parts, i)))
    every_eq = apply(instantiate(('ref', 'finite_every_from_all'), xs, p), pointwise)
    equality = apply(instantiate(('ref', 'finite_sum_congruence'), xs, absolute, sum_parts), every_eq)
    equality = rewrite(kernel, equality, instantiate(('ref', 'finite_sum_add'), xs, excess, deficit))
    kernel.theorem('finite_absolute_excess_split', alls((xs, f, g), kernel.infer(equality).conclusion), close(equality, (xs, f, g)))
    equality = rewrite(kernel, equality, balance, reverse=True)
    equality = rewrite(kernel, equality, ring(Add(total(xs, excess), total(xs, excess)), Mul(total(xs, excess), Add(RONE, RONE))))
    two = Add(RONE, RONE)
    target = Eq(Div(total(xs, absolute), two), total(xs, excess))
    divided = transformed(kernel, target, [equality], lambda _: apply(ax('positive_division_cancel', total(xs, excess), two), ax('two_positive')))
    kernel.theorem('finite_half_absolute_sum_equals_excess', alls((xs, f, g), Imp(same_mass, target)), close(divided, (xs, f, g), (same_mass,)))


def certificates():
    kernel = sums.certificates()
    kernel.axioms.update(real_axioms() | {'two_positive': Lt(RZERO, Add(RONE, RONE))})
    derive_scalar(kernel)
    derive_zero_measures(kernel)
    derive_population_sample(kernel)
    derive_excess(kernel)
    return kernel


def check(name, value):
    if not value:
        raise AssertionError(name)


def verify():
    kernel = certificates()
    check('finite_population_variance_zero_iff', 'finite_population_variance_zero_iff' in kernel.verified and not kernel.verified['finite_population_variance_zero_iff'].assumptions)
    check('finite_sample_variance_zero_iff', 'finite_sample_variance_zero_iff' in kernel.verified and not kernel.verified['finite_sample_variance_zero_iff'].assumptions)
    check('absolute_nonnegative_general', 'absolute_nonnegative_general' in kernel.verified and not kernel.verified['absolute_nonnegative_general'].assumptions)
    check('absolute_zero_iff_general', 'absolute_zero_iff_general' in kernel.verified and not kernel.verified['absolute_zero_iff_general'].assumptions)
    check('difference_zero_iff_general', 'difference_zero_iff_general' in kernel.verified and not kernel.verified['difference_zero_iff_general'].assumptions)
    check('finite_absolute_differences_zero_iff', 'finite_absolute_differences_zero_iff' in kernel.verified and not kernel.verified['finite_absolute_differences_zero_iff'].assumptions)
    check('finite_absolute_excess_split', 'finite_absolute_excess_split' in kernel.verified and not kernel.verified['finite_absolute_excess_split'].assumptions)
    check('finite_dispersion_zero_iff', 'finite_dispersion_zero_iff' in kernel.verified and not kernel.verified['finite_dispersion_zero_iff'].assumptions)
    check('finite_equal_mass_excess_balance', 'finite_equal_mass_excess_balance' in kernel.verified and not kernel.verified['finite_equal_mass_excess_balance'].assumptions)
    check('finite_excess_deficit_difference', 'finite_excess_deficit_difference' in kernel.verified and not kernel.verified['finite_excess_deficit_difference'].assumptions)
    check('finite_half_absolute_sum_equals_excess', 'finite_half_absolute_sum_equals_excess' in kernel.verified and not kernel.verified['finite_half_absolute_sum_equals_excess'].assumptions)
    check('finite_normalized_variance_zero_iff', 'finite_normalized_variance_zero_iff' in kernel.verified and not kernel.verified['finite_normalized_variance_zero_iff'].assumptions)
    check('finite_squared_deviations_zero_iff', 'finite_squared_deviations_zero_iff' in kernel.verified and not kernel.verified['finite_squared_deviations_zero_iff'].assumptions)
    check('positive_division_zero_iff_general', 'positive_division_zero_iff_general' in kernel.verified and not kernel.verified['positive_division_zero_iff_general'].assumptions)
    check('square_nonnegative_general', 'square_nonnegative_general' in kernel.verified and not kernel.verified['square_nonnegative_general'].assumptions)
    check('square_zero_iff_general', 'square_zero_iff_general' in kernel.verified and not kernel.verified['square_zero_iff_general'].assumptions)
    return {'backend': 'Python 3 typed proof kernel', 'passed': True, 'results': [{'id': name, 'passed': True} for name in kernel.verified], 'axioms': list(kernel.axioms), 'scope': 'Arbitrary finite lists of real observations, both directions of zero variance and zero absolute dispersion; all recursions and quantifier discharge checked.'}


if __name__ == '__main__':
    print(json.dumps(verify()))
