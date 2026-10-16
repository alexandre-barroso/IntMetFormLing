from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from capitulo_01.somas_finitas import *
from capitulo_07.probabilidade_geral import Or, Lt, BOTTOM, eq_trans
from capitulo_07.gram_geral import foundations


def neg(p):
    return Imp(p, BOTTOM)


def real_axioms():
    x, y, d = V('ratio_x', 'R'), V('ratio_y', 'R'), V('ratio_d', 'R')
    return foundations() | {
        'one_positive': Lt(RZERO, RONE),
        'ratio_zero_product': alls((x, y), Imp(Eq(Mul(x, y), RZERO), Or(Eq(x, RZERO), Eq(y, RZERO)))),
        'division_reconstruction_nonzero': alls((x, d), Imp(neg(Eq(d, RZERO)), Eq(Mul(Div(x, d), d), x))),
        'division_uniqueness_nonzero': alls((x, y, d), imps((neg(Eq(d, RZERO)), Eq(Mul(y, d), x)), Eq(y, Div(x, d)))),
        'positive_quotient': alls((x, d), imps((Lt(RZERO, x), Lt(RZERO, d)), Lt(RZERO, Div(x, d)))),
        'strict_positive_division_order': alls((d, x, y), Imp(Lt(RZERO, d), Iff(Lt(Div(x, d), y), Lt(x, Mul(y, d))))),
    }


def derive_nonzero(kernel):
    x, y = V('nonzero_x', 'R'), V('nonzero_y', 'R')
    hx = Lt(RZERO, x)
    hz = Eq(x, RZERO)
    nonpositive = transformed(kernel, Le(x, RZERO), [('assume', hz)], lambda _: ax('real_order_reflexive', RZERO))
    contradiction = apply(ax('real_strict_nonstrict_inconsistent', RZERO, x), ('assume', hx), nonpositive)
    kernel.theorem('positive_is_nonzero', All(x, Imp(hx, neg(hz))), close(contradiction, (x,), (hx, hz)))
    nx, ny, product_zero = neg(Eq(x, RZERO)), neg(Eq(y, RZERO)), Eq(Mul(x, y), RZERO)
    choices = apply(ax('ratio_zero_product', x, y), ('assume', product_zero))
    badx = apply(('assume', nx), ('assume', Eq(x, RZERO)))
    bady = apply(('assume', ny), ('assume', Eq(y, RZERO)))
    proof = ('or_e', choices, badx, bady)
    kernel.theorem('product_of_nonzero_is_nonzero', alls((x, y), imps((nx, ny), neg(product_zero))), close(proof, (x, y), (nx, ny, product_zero)))


def derive_normalization(kernel):
    x, y, k = V('order_x', 'R'), V('order_y', 'R'), V('positive_scale', 'R')
    hk = Lt(RZERO, k)
    scaled, ordinary = Le(Mul(k, x), Mul(k, y)), Le(x, y)
    forward = apply(ax('positive_division_forward', k, x, Mul(k, y)), ('assume', hk), ('assume', scaled))
    forward = rewrite(kernel, forward, apply(ax('gram_positive_cancel', k, y), ('assume', hk)))
    backward = apply(ax('nonnegative_multiplication_monotone', k, x, y), apply(ax('positive_implies_nonnegative', k), ('assume', hk)), ('assume', ordinary))
    proof = both((close(forward, assumptions=(scaled,)), close(backward, assumptions=(ordinary,))))
    kernel.theorem('positive_scaling_order_equivalence', alls((k, x, y), Imp(hk, Iff(scaled, ordinary))), close(proof, (k, x, y), (hk,)))
    c, n, scale, base = (V('normalize_' + name, 'R') for name in ('count', 'denominator', 'scale', 'base'))
    hn, hs = Lt(RZERO, n), neg(Eq(scale, RZERO))
    nn = apply(instantiate(('ref', 'positive_is_nonzero'), n), ('assume', hn))
    product_nonzero = apply(instantiate(('ref', 'product_of_nonzero_is_nonzero'), scale, n), ('assume', hs), nn)
    reconstructed = apply(ax('division_reconstruction_nonzero', c, n), nn)
    multiplied = polynomial(kernel, Eq(Mul(Div(c, n), Mul(scale, n)), Mul(scale, c)), [ring(Mul(Div(c, n), Mul(scale, n)), Mul(scale, Mul(Div(c, n), n))), reconstructed])
    unique = apply(ax('division_uniqueness_nonzero', Mul(scale, c), Div(c, n), Mul(scale, n)), product_nonzero, multiplied)
    same_ratio = symmetric(Div(c, n), Div(Mul(scale, c), Mul(scale, n)), unique)
    target = Eq(Mul(Div(Mul(scale, c), Mul(scale, n)), base), Mul(Div(c, n), base))
    proof = polynomial(kernel, target, [same_ratio])
    kernel.theorem('ratio_normalization_scaling', alls((c, n, scale, base), imps((hn, hs), target)), close(proof, (c, n, scale, base), (hn, hs)))
    c1, c2, n1, n2 = (V('compare_' + name, 'R') for name in ('c1', 'c2', 'n1', 'n2'))
    hb = Lt(RZERO, base)
    formula = Iff(Le(Mul(Div(c1, n1), base), Mul(Div(c2, n2), base)), Le(Div(c1, n1), Div(c2, n2)))
    proof = apply(instantiate(('ref', 'positive_scaling_order_equivalence'), base, Div(c1, n1), Div(c2, n2)), ('assume', hb))
    proof = rewrite(kernel, proof, ring(Mul(base, Div(c1, n1)), Mul(Div(c1, n1), base)))
    proof = rewrite(kernel, proof, ring(Mul(base, Div(c2, n2)), Mul(Div(c2, n2), base)))
    hypotheses = (Lt(RZERO, n1), Lt(RZERO, n2), hb)
    kernel.theorem('ratio_normalization_order', alls((c1, c2, n1, n2, base), imps(hypotheses, formula)), close(proof, (c1, c2, n1, n2, base), hypotheses))


def derive_ttr(kernel):
    v, n = V('type_count', 'R'), V('token_count', 'R')
    hn, hv, upper = Lt(RZERO, n), Le(RZERO, v), Le(v, n)
    nn = apply(instantiate(('ref', 'positive_is_nonzero'), n), ('assume', hn))
    reconstruction = apply(ax('division_reconstruction_nonzero', v, n), nn)
    ratio = Div(v, n)
    ratio_nonnegative = apply(ax('positive_division_forward', n, RZERO, v), ('assume', hn), rewrite(kernel, ('assume', hv), ring(Mul(n, RZERO), RZERO), reverse=True))
    ratio_upper = apply(('and_r', apply(ax('gram_division_order', n, v, RONE), ('assume', hn))), rewrite(kernel, ('assume', upper), ring(Mul(RONE, n), n), reverse=True))
    kernel.theorem('ttr_ratio_bounds', alls((v, n), imps((hn, hv, upper), And(Le(RZERO, ratio), Le(ratio, RONE)))), close(both((ratio_nonnegative, ratio_upper)), (v, n), (hn, hv, upper)))
    next_n = Add(n, RONE)
    positive_next = apply(ax('gram_strict_addition', RZERO, n, RONE), ('assume', hn))
    positive_next = rewrite(kernel, positive_next, ring(Add(RZERO, RONE), RONE))
    positive_next = apply(ax('gram_strict_transitive', RZERO, RONE, next_n), ax('one_positive'), positive_next)
    identity = polynomial(kernel, Eq(Mul(ratio, next_n), Add(v, ratio)), [ring(Mul(ratio, next_n), Add(Mul(ratio, n), ratio)), reconstruction])
    summed = apply(ax('addition_monotone', v, v, RZERO, ratio), ax('real_order_reflexive', v), ratio_nonnegative)
    summed = rewrite(kernel, summed, ring(Add(v, RZERO), v))
    summed = rewrite(kernel, summed, identity, reverse=True)
    repeated = apply(('and_r', apply(ax('gram_division_order', next_n, v, ratio), positive_next)), summed)
    target = Le(Div(v, next_n), ratio)
    kernel.theorem('ttr_repeated_type_general', alls((v, n), imps((hn, hv), target)), close(repeated, (v, n), (hn, hv)))
    strictly_positive = Lt(RZERO, v)
    ratio_positive = apply(ax('positive_quotient', v, n), ('assume', strictly_positive), ('assume', hn))
    strict = apply(ax('gram_strict_addition', RZERO, ratio, v), ratio_positive)
    strict = rewrite(kernel, strict, ring(Add(RZERO, v), v))
    strict = rewrite(kernel, strict, ring(Add(ratio, v), Add(v, ratio)))
    strict = rewrite(kernel, strict, identity, reverse=True)
    strict = apply(('and_r', apply(ax('strict_positive_division_order', next_n, v, ratio), positive_next)), strict)
    kernel.theorem('ttr_repeated_type_strict_general', alls((v, n), imps((hn, strictly_positive), Lt(Div(v, next_n), ratio))), close(strict, (v, n), (hn, strictly_positive)))
    summed = apply(ax('addition_monotone', v, v, ratio, RONE), ax('real_order_reflexive', v), ratio_upper)
    summed = rewrite(kernel, summed, identity, reverse=True)
    summed = rewrite(kernel, summed, ring(Mul(ratio, next_n), Mul(next_n, ratio)))
    newtype = apply(ax('positive_division_forward', next_n, ratio, Add(v, RONE)), positive_next, summed)
    kernel.theorem('ttr_new_type_general', alls((v, n), imps((hn, upper), Le(ratio, Div(Add(v, RONE), next_n)))), close(newtype, (v, n), (hn, upper)))


def certificates():
    kernel = Kernel(field_axioms() | real_axioms())
    derive_nonzero(kernel)
    derive_normalization(kernel)
    derive_ttr(kernel)
    return kernel


def check(name, value):
    if not value:
        raise AssertionError(name)


def verify():
    kernel = certificates()
    check('positive_is_nonzero', 'positive_is_nonzero' in kernel.verified and not kernel.verified['positive_is_nonzero'].assumptions)
    check('positive_scaling_order_equivalence', 'positive_scaling_order_equivalence' in kernel.verified and not kernel.verified['positive_scaling_order_equivalence'].assumptions)
    check('product_of_nonzero_is_nonzero', 'product_of_nonzero_is_nonzero' in kernel.verified and not kernel.verified['product_of_nonzero_is_nonzero'].assumptions)
    check('ratio_normalization_order', 'ratio_normalization_order' in kernel.verified and not kernel.verified['ratio_normalization_order'].assumptions)
    check('ratio_normalization_scaling', 'ratio_normalization_scaling' in kernel.verified and not kernel.verified['ratio_normalization_scaling'].assumptions)
    check('ttr_new_type_general', 'ttr_new_type_general' in kernel.verified and not kernel.verified['ttr_new_type_general'].assumptions)
    check('ttr_ratio_bounds', 'ttr_ratio_bounds' in kernel.verified and not kernel.verified['ttr_ratio_bounds'].assumptions)
    check('ttr_repeated_type_general', 'ttr_repeated_type_general' in kernel.verified and not kernel.verified['ttr_repeated_type_general'].assumptions)
    check('ttr_repeated_type_strict_general', 'ttr_repeated_type_strict_general' in kernel.verified and not kernel.verified['ttr_repeated_type_strict_general'].assumptions)
    return {'backend': 'Python 3 typed ordered-field proof kernel', 'passed': True, 'results': [{'id': name, 'passed': True} for name in kernel.verified], 'axioms': list(kernel.axioms)}


if __name__ == '__main__':
    print(json.dumps(verify()))
