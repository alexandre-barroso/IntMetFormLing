from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from capitulo_01.somas_finitas import *
from capitulo_07.probabilidade_geral import Or, Lt, BOTTOM, eq_trans
from capitulo_01 import listas_finitas as lists
from capitulo_01 import razoes as ratios
from capitulo_01.triplice import sum_of_pointwise_equality
from capitulo_05 import triplice as variance
from capitulo_07 import gram_geral as gram

SQRT = C('nonnegative_square_root', FT('R', 'R'))


def neg(p):
    return Imp(p, BOTTOM)


def merge(kernel, other):
    for name, formula in other.axioms.items():
        if name in kernel.axioms and not same(kernel.axioms[name], formula):
            raise ValueError(('axiom collision', name))
        kernel.axioms[name] = formula
    for name, formula, proof in other.records:
        if name in kernel.verified:
            if not same(kernel.verified[name].conclusion, formula):
                raise ValueError(('theorem collision', name))
        else:
            kernel.theorem(name, formula, proof)


def scaled(a, f):
    i = V('scaling_coordinate', INDEX)
    return Lam(i, Mul(a, A(f, i)))


def norm(xs, f):
    return A(SQRT, total(xs, gram.squared(f)))


def cosine(xs, f, g):
    return Div(total(xs, gram.product(f, g)), Mul(norm(xs, f), norm(xs, g)))


def nonzero(xs, f):
    i = V('nonzero_coordinate', INDEX)
    return neg(every(xs, Lam(i, Eq(A(f, i), RZERO))))


def sqrt_axioms():
    x, r = V('sqrt_input', 'R'), V('sqrt_candidate', 'R')
    return {
        'sqrt_nonnegative': All(x, Imp(Le(RZERO, x), Le(RZERO, A(SQRT, x)))),
        'sqrt_reconstruction': All(x, Imp(Le(RZERO, x), Eq(Mul(A(SQRT, x), A(SQRT, x)), x))),
        'sqrt_unique_nonnegative': alls((x, r), imps((Le(RZERO, x), Le(RZERO, r), Eq(Mul(r, r), x)), Eq(A(SQRT, x), r))),
    }


def derive_adjacency(kernel):
    xs = V('vertex_list', LIST)
    i, j, k = V('source', INDEX), V('target', INDEX), V('intermediate', INDEX)
    relation = V('edge_relation', FT(INDEX, PREDICATE))
    entry = Lam(k, Mul(A(lists.IND, A(relation, i, k)), A(lists.IND, A(relation, k, j))))
    predicate = Lam(k, And(A(relation, i, k), A(relation, k, j)))
    indicator = Lam(k, A(lists.IND, A(predicate, k)))
    pointwise = close(instantiate(('ref', 'indicator_conjunction_product'), A(relation, i, k), A(relation, k, j)), (k,))
    equality = sum_of_pointwise_equality(kernel, xs, entry, indicator, pointwise)
    equality = rewrite(kernel, equality, instantiate(('ref', 'finite_indicator_sum_counts_filter'), xs, predicate))
    formula = alls((xs, relation, i, j), kernel.infer(equality).conclusion)
    kernel.theorem('finite_adjacency_square_counts_intermediates', formula, close(equality, (xs, relation, i, j)))


def derive_norm_basics(kernel):
    xs = V('norm_list', LIST)
    f = V('norm_vector', FUNCTION)
    i = V('norm_index', INDEX)
    ss = total(xs, gram.squared(f))
    pointwise = close(instantiate(('ref', 'square_nonnegative_general'), A(f, i)), (i,))
    predicate = Lam(i, Le(RZERO, Mul(A(f, i), A(f, i))))
    every_positive = apply(instantiate(('ref', 'finite_every_from_all'), xs, predicate), pointwise)
    ss_nonnegative = apply(instantiate(('ref', 'finite_sum_nonnegative'), xs, gram.squared(f)), every_positive)
    kernel.theorem('finite_squared_norm_nonnegative', alls((xs, f), Le(RZERO, ss)), close(ss_nonnegative, (xs, f)))
    zero_variance = instantiate(('ref', 'finite_squared_deviations_zero_iff'), xs, f, RZERO)
    shifted = Lam(i, Mul(Sub(A(f, i), RZERO), Sub(A(f, i), RZERO)))
    equality = sum_of_pointwise_equality(kernel, xs, shifted, gram.squared(f), close(ring(A(shifted, i), Mul(A(f, i), A(f, i))), (i,)))
    zero_variance = rewrite(kernel, zero_variance, equality)
    zero_ss = Eq(ss, RZERO)
    bad = apply(('and_l', zero_variance), ('assume', zero_ss))
    bad = apply(('assume', nonzero(xs, f)), bad)
    choice = apply(ax('nonnegative_zero_or_positive', ss), ss_nonnegative)
    positive = ('or_e', choice, ('false_e', Lt(RZERO, ss), bad), ('assume', Lt(RZERO, ss)))
    kernel.theorem('finite_nonzero_squared_norm_positive', alls((xs, f), Imp(nonzero(xs, f), Lt(RZERO, ss))), close(positive, (xs, f), (nonzero(xs, f),)))
    n = norm(xs, f)
    sqrt_nonnegative = apply(ax('sqrt_nonnegative', ss), ss_nonnegative)
    reconstructed = apply(ax('sqrt_reconstruction', ss), ss_nonnegative)
    zero_n = Eq(n, RZERO)
    forced_zero = rewrite(kernel, reconstructed, ('assume', zero_n))
    forced_zero = rewrite(kernel, forced_zero, ring(Mul(RZERO, RZERO), RZERO))
    ss_nonpositive = transformed(kernel, Le(ss, RZERO), [symmetric(RZERO, ss, forced_zero)], lambda _: ax('real_order_reflexive', RZERO))
    contradiction = apply(ax('real_strict_nonstrict_inconsistent', RZERO, ss), positive, ss_nonpositive)
    choice = apply(ax('nonnegative_zero_or_positive', n), sqrt_nonnegative)
    norm_positive = ('or_e', choice, ('false_e', Lt(RZERO, n), contradiction), ('assume', Lt(RZERO, n)))
    kernel.theorem('finite_nonzero_norm_positive', alls((xs, f), Imp(nonzero(xs, f), Lt(RZERO, n))), close(norm_positive, (xs, f), (nonzero(xs, f),)))
    kernel.theorem('finite_norm_square_identity', alls((xs, f), Eq(Mul(n, n), ss)), close(reconstructed, (xs, f)))


def derive_scaling(kernel):
    xs = V('scale_list', LIST)
    f, g = V('scale_f', FUNCTION), V('scale_g', FUNCTION)
    a, b, i = V('scale_a', 'R'), V('scale_b', 'R'), V('scale_i', INDEX)
    sf, sg = scaled(a, f), scaled(b, g)
    for name, left, original, scalar in [('finite_scaled_squared_norm', gram.squared(sf), gram.squared(f), Mul(a, a)), ('finite_scaled_dot_product', gram.product(sf, sg), gram.product(f, g), Mul(a, b))]:
        combined = scaled(scalar, original)
        pointwise = close(ring(A(left, i), A(combined, i)), (i,))
        equality = sum_of_pointwise_equality(kernel, xs, left, combined, pointwise)
        equality = rewrite(kernel, equality, instantiate(('ref', 'finite_sum_scale'), xs, original, scalar))
        variables = (xs, f, a) if name == 'finite_scaled_squared_norm' else (xs, f, g, a, b)
        kernel.theorem(name, alls(variables, kernel.infer(equality).conclusion), close(equality, variables))
    ha = Lt(RZERO, a)
    old_sum, new_sum = total(xs, gram.squared(f)), total(xs, gram.squared(sf))
    old_n, new_n = norm(xs, f), norm(xs, sf)
    old_nonnegative = instantiate(('ref', 'finite_squared_norm_nonnegative'), xs, f)
    norm_nonnegative = apply(ax('sqrt_nonnegative', old_sum), old_nonnegative)
    a_nonnegative = apply(ax('positive_implies_nonnegative', a), ('assume', ha))
    product_nonnegative = apply(ax('nonnegative_multiplication_monotone', a, RZERO, old_n), a_nonnegative, norm_nonnegative)
    product_nonnegative = rewrite(kernel, product_nonnegative, ring(Mul(a, RZERO), RZERO))
    sq_identity = instantiate(('ref', 'finite_scaled_squared_norm'), xs, f, a)
    old_identity = instantiate(('ref', 'finite_norm_square_identity'), xs, f)
    candidate_square = polynomial(kernel, Eq(Mul(Mul(a, old_n), Mul(a, old_n)), new_sum), [ring(Mul(Mul(a, old_n), Mul(a, old_n)), Mul(Mul(a, a), Mul(old_n, old_n))), old_identity, sq_identity])
    new_nonnegative = instantiate(('ref', 'finite_squared_norm_nonnegative'), xs, sf)
    unique = apply(ax('sqrt_unique_nonnegative', new_sum, Mul(a, old_n)), new_nonnegative, product_nonnegative, candidate_square)
    kernel.theorem('finite_positive_scaling_norm', alls((xs, f, a), Imp(ha, Eq(new_n, Mul(a, old_n)))), close(unique, (xs, f, a), (ha,)))
    hb, hf, hg = Lt(RZERO, b), nonzero(xs, f), nonzero(xs, g)
    nf = apply(instantiate(('ref', 'finite_nonzero_norm_positive'), xs, f), ('assume', hf))
    ng = apply(instantiate(('ref', 'finite_nonzero_norm_positive'), xs, g), ('assume', hg))
    denom = Mul(norm(xs, f), norm(xs, g))
    denom_positive = apply(ax('gram_positive_product', norm(xs, f), norm(xs, g)), nf, ng)
    ab_positive = apply(ax('gram_positive_product', a, b), ('assume', ha), ('assume', hb))
    ab_nonzero = apply(instantiate(('ref', 'positive_is_nonzero'), Mul(a, b)), ab_positive)
    dot = total(xs, gram.product(f, g))
    ratio = apply(instantiate(('ref', 'ratio_normalization_scaling'), dot, denom, Mul(a, b), RONE), denom_positive, ab_nonzero)
    ratio = rewrite(kernel, ratio, ring(Mul(Div(Mul(Mul(a, b), dot), Mul(Mul(a, b), denom)), RONE), Div(Mul(Mul(a, b), dot), Mul(Mul(a, b), denom))))
    ratio = rewrite(kernel, ratio, ring(Mul(Div(dot, denom), RONE), Div(dot, denom)))
    sf_norm = apply(instantiate(('ref', 'finite_positive_scaling_norm'), xs, f, a), ('assume', ha))
    sg_norm = apply(instantiate(('ref', 'finite_positive_scaling_norm'), xs, g, b), ('assume', hb))
    dot_eq = instantiate(('ref', 'finite_scaled_dot_product'), xs, f, g, a, b)
    target = Eq(cosine(xs, sf, sg), cosine(xs, f, g))
    eqs = [dot_eq, sf_norm, sg_norm, ring(Mul(Mul(a, norm(xs, f)), Mul(b, norm(xs, g))), Mul(Mul(a, b), denom))]
    proof = transformed(kernel, target, eqs, lambda _: ratio)
    conditions = (ha, hb, hf, hg)
    kernel.theorem('finite_cosine_positive_biscaling', alls((xs, f, g, a, b), imps(conditions, target)), close(proof, (xs, f, g, a, b), conditions))


def derive_range(kernel):
    xs = V('cosine_list', LIST)
    f, g = V('cosine_f', FUNCTION), V('cosine_g', FUNCTION)
    i = V('cosine_index', INDEX)
    positive_coordinates = every(xs, Lam(i, And(Le(RZERO, A(f, i)), Le(RZERO, A(g, i)))))
    hf, hg = nonzero(xs, f), nonzero(xs, g)
    point_p = Lam(i, And(Le(RZERO, A(f, i)), Le(RZERO, A(g, i))))
    point_q = Lam(i, Le(RZERO, Mul(A(f, i), A(g, i))))
    hypothesis = And(Le(RZERO, A(f, i)), Le(RZERO, A(g, i)))
    product_positive = apply(ax('nonnegative_multiplication_monotone', A(f, i), RZERO, A(g, i)), ('and_l', ('assume', hypothesis)), ('and_r', ('assume', hypothesis)))
    product_positive = rewrite(kernel, product_positive, ring(Mul(A(f, i), RZERO), RZERO))
    implication = close(product_positive, (i,), (hypothesis,))
    dot_positive = apply(instantiate(('ref', 'finite_every_implication'), xs, point_p, point_q), implication, ('assume', positive_coordinates))
    dot_positive = apply(instantiate(('ref', 'finite_sum_nonnegative'), xs, gram.product(f, g)), dot_positive)
    nf = apply(instantiate(('ref', 'finite_nonzero_norm_positive'), xs, f), ('assume', hf))
    ng = apply(instantiate(('ref', 'finite_nonzero_norm_positive'), xs, g), ('assume', hg))
    d = Mul(norm(xs, f), norm(xs, g))
    dp = apply(ax('gram_positive_product', norm(xs, f), norm(xs, g)), nf, ng)
    c = total(xs, gram.product(f, g))
    lower = apply(ax('positive_division_forward', d, RZERO, c), dp, rewrite(kernel, dot_positive, ring(Mul(d, RZERO), RZERO), reverse=True))
    aa, bb = total(xs, gram.squared(f)), total(xs, gram.squared(g))
    d_square = polynomial(kernel, Eq(Mul(d, d), Mul(aa, bb)), [ring(Mul(d, d), Mul(Mul(norm(xs, f), norm(xs, f)), Mul(norm(xs, g), norm(xs, g)))), instantiate(('ref', 'finite_norm_square_identity'), xs, f), instantiate(('ref', 'finite_norm_square_identity'), xs, g)])
    ap = apply(instantiate(('ref', 'finite_nonzero_squared_norm_positive'), xs, f), ('assume', hf))
    bp = apply(instantiate(('ref', 'finite_nonzero_squared_norm_positive'), xs, g), ('assume', hg))
    upper = ('and_r', apply(instantiate(('ref', 'finite_normalized_dot_range'), xs, f, g, d), ap, bp, dp, d_square))
    target = And(Le(RZERO, cosine(xs, f, g)), Le(cosine(xs, f, g), RONE))
    assumptions = (hf, hg, positive_coordinates)
    kernel.theorem('finite_nonnegative_cosine_range', alls((xs, f, g), imps(assumptions, target)), close(both((lower, upper)), (xs, f, g), assumptions))


def derive_single_scaling(kernel):
    xs = V('single_scale_list', LIST)
    f, g = V('single_scale_f', FUNCTION), V('single_scale_g', FUNCTION)
    a, i = V('single_scale_factor', 'R'), V('single_scale_index', INDEX)
    ha, hf, hg = Lt(RZERO, a), nonzero(xs, f), nonzero(xs, g)
    sf = scaled(a, f)
    source = gram.product(sf, g)
    target_function = scaled(a, gram.product(f, g))
    pointwise = close(ring(A(source, i), A(target_function, i)), (i,))
    dot_eq = sum_of_pointwise_equality(kernel, xs, source, target_function, pointwise)
    dot_eq = rewrite(kernel, dot_eq, instantiate(('ref', 'finite_sum_scale'), xs, gram.product(f, g), a))
    sf_norm = apply(instantiate(('ref', 'finite_positive_scaling_norm'), xs, f, a), ('assume', ha))
    nf = apply(instantiate(('ref', 'finite_nonzero_norm_positive'), xs, f), ('assume', hf))
    ng = apply(instantiate(('ref', 'finite_nonzero_norm_positive'), xs, g), ('assume', hg))
    denom = Mul(norm(xs, f), norm(xs, g))
    denom_positive = apply(ax('gram_positive_product', norm(xs, f), norm(xs, g)), nf, ng)
    an = apply(instantiate(('ref', 'positive_is_nonzero'), a), ('assume', ha))
    c = total(xs, gram.product(f, g))
    ratio = apply(instantiate(('ref', 'ratio_normalization_scaling'), c, denom, a, RONE), denom_positive, an)
    ratio = rewrite(kernel, ratio, ring(Mul(Div(Mul(a, c), Mul(a, denom)), RONE), Div(Mul(a, c), Mul(a, denom))))
    ratio = rewrite(kernel, ratio, ring(Mul(Div(c, denom), RONE), Div(c, denom)))
    target = Eq(cosine(xs, sf, g), cosine(xs, f, g))
    proof = transformed(kernel, target, [dot_eq, sf_norm, ring(Mul(Mul(a, norm(xs, f)), norm(xs, g)), Mul(a, denom))], lambda _: ratio)
    kernel.theorem('finite_cosine_positive_scaling', alls((xs, f, g, a), imps((ha, hf, hg), target)), close(proof, (xs, f, g, a), (ha, hf, hg)))


def derive_normalization(kernel):
    xs = V('unit_list', LIST)
    f, g = V('unit_f', FUNCTION), V('unit_g', FUNCTION)
    hf, hg = nonzero(xs, f), nonzero(xs, g)
    nf, ng = norm(xs, f), norm(xs, g)
    fp = apply(instantiate(('ref', 'finite_nonzero_norm_positive'), xs, f), ('assume', hf))
    gp = apply(instantiate(('ref', 'finite_nonzero_norm_positive'), xs, g), ('assume', hg))
    af, ag = Div(RONE, nf), Div(RONE, ng)
    afp = apply(ax('positive_quotient', RONE, nf), ax('one_positive'), fp)
    agp = apply(ax('positive_quotient', RONE, ng), ax('one_positive'), gp)
    sf, sg = scaled(af, f), scaled(ag, g)
    scaling = apply(instantiate(('ref', 'finite_positive_scaling_norm'), xs, f, af), afp)
    nn = apply(instantiate(('ref', 'positive_is_nonzero'), nf), fp)
    reconstruction = apply(ax('division_reconstruction_nonzero', RONE, nf), nn)
    norm_one = rewrite(kernel, scaling, reconstruction)
    kernel.theorem('finite_normalized_vector_unit_norm', alls((xs, f), Imp(hf, Eq(norm(xs, sf), RONE))), close(norm_one, (xs, f), (hf,)))
    self_ratio = apply(ax('division_uniqueness_nonzero', nf, RONE, nf), nn, ring(Mul(RONE, nf), nf))
    chain = eq_trans(norm(xs, sf), RONE, Div(nf, nf), norm_one, self_ratio)
    chain_goal = And(Eq(norm(xs, sf), Div(nf, nf)), Eq(Div(nf, nf), RONE))
    kernel.theorem('finite_normalization_norm_chain', alls((xs, f), Imp(hf, chain_goal)), close(both((chain, symmetric(RONE, Div(nf, nf), self_ratio))), (xs, f), (hf,)))
    same_cosine = apply(instantiate(('ref', 'finite_cosine_positive_biscaling'), xs, f, g, af, ag), afp, agp, ('assume', hf), ('assume', hg))
    target = Eq(cosine(xs, sf, sg), cosine(xs, f, g))
    kernel.theorem('finite_normalization_preserves_cosine', alls((xs, f, g), imps((hf, hg), target)), close(same_cosine, (xs, f, g), (hf, hg)))


def certificates():
    kernel = gram.certificates()
    merge(kernel, lists.certificates())
    merge(kernel, variance.certificates())
    merge(kernel, ratios.certificates())
    kernel.axioms.update(sqrt_axioms())
    derive_adjacency(kernel)
    derive_norm_basics(kernel)
    derive_scaling(kernel)
    derive_range(kernel)
    derive_single_scaling(kernel)
    derive_normalization(kernel)
    return kernel


def check(name, value):
    if not value:
        raise AssertionError(name)


def verify():
    kernel = certificates()
    check('finite_adjacency_square_counts_intermediates', 'finite_adjacency_square_counts_intermediates' in kernel.verified and not kernel.verified['finite_adjacency_square_counts_intermediates'].assumptions)
    check('finite_cosine_positive_biscaling', 'finite_cosine_positive_biscaling' in kernel.verified and not kernel.verified['finite_cosine_positive_biscaling'].assumptions)
    check('finite_cosine_positive_scaling', 'finite_cosine_positive_scaling' in kernel.verified and not kernel.verified['finite_cosine_positive_scaling'].assumptions)
    check('finite_nonnegative_cosine_range', 'finite_nonnegative_cosine_range' in kernel.verified and not kernel.verified['finite_nonnegative_cosine_range'].assumptions)
    check('finite_nonzero_norm_positive', 'finite_nonzero_norm_positive' in kernel.verified and not kernel.verified['finite_nonzero_norm_positive'].assumptions)
    check('finite_nonzero_squared_norm_positive', 'finite_nonzero_squared_norm_positive' in kernel.verified and not kernel.verified['finite_nonzero_squared_norm_positive'].assumptions)
    check('finite_norm_square_identity', 'finite_norm_square_identity' in kernel.verified and not kernel.verified['finite_norm_square_identity'].assumptions)
    check('finite_normalization_norm_chain', 'finite_normalization_norm_chain' in kernel.verified and not kernel.verified['finite_normalization_norm_chain'].assumptions)
    check('finite_normalization_preserves_cosine', 'finite_normalization_preserves_cosine' in kernel.verified and not kernel.verified['finite_normalization_preserves_cosine'].assumptions)
    check('finite_normalized_vector_unit_norm', 'finite_normalized_vector_unit_norm' in kernel.verified and not kernel.verified['finite_normalized_vector_unit_norm'].assumptions)
    check('finite_positive_scaling_norm', 'finite_positive_scaling_norm' in kernel.verified and not kernel.verified['finite_positive_scaling_norm'].assumptions)
    check('finite_squared_norm_nonnegative', 'finite_squared_norm_nonnegative' in kernel.verified and not kernel.verified['finite_squared_norm_nonnegative'].assumptions)
    names = ['finite_adjacency_square_counts_intermediates', 'finite_positive_scaling_norm', 'finite_cosine_positive_scaling', 'finite_cosine_positive_biscaling', 'finite_nonnegative_cosine_range', 'finite_normalized_vector_unit_norm', 'finite_normalization_norm_chain', 'finite_normalization_preserves_cosine']
    return {'backend': 'Python 3 typed finite-vector proof kernel', 'passed': True, 'results': [{'id': name, 'passed': name in kernel.verified} for name in names], 'axioms': list(kernel.axioms)}


if __name__ == '__main__':
    print(json.dumps(verify()))
