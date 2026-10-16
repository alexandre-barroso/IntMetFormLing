from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from capitulo_01.somas_finitas import *
from capitulo_07.probabilidade_geral import OMEGA, EVENT, Or, BOTTOM, event_union, event_difference, event_disjoint, empty_event, universe_event, MEASURE, MEASURABLE, measure_axioms, simple_function_axioms
import capitulo_01.somas_finitas as sums

FAMILY = FT(INDEX, EVENT)
SIGMA = FT(EVENT, 'Prop')
MEASURE_FUNCTION = FT(EVENT, 'R')
UNION = C('list_event_union', FT(LIST, FT(FAMILY, EVENT)))
DISJOINT = C('list_disjoint_events', FT(LIST, FT(FAMILY, 'Prop')))


def union(xs, family):
    return A(UNION, xs, family)


def disjoint(xs, family):
    return A(DISJOINT, xs, family)


def measurable(xs, family, sigma):
    i = V('measurable_family_index', INDEX)
    return every(xs, Lam(i, A(sigma, A(family, i))))


def assumptions(mu, sigma):
    a, b = V('measure_set_a', EVENT), V('measure_set_b', EVENT)
    return (
        A(sigma, empty_event()),
        A(sigma, universe_event()),
        alls((a, b), imps((A(sigma, a), A(sigma, b)), A(sigma, event_union(a, b)))),
        alls((a, b), imps((A(sigma, a), A(sigma, b)), A(sigma, event_difference(a, b)))),
        All(a, Imp(A(sigma, a), Le(RZERO, A(mu, a)))),
        Eq(A(mu, empty_event()), RZERO),
        Eq(A(mu, universe_event()), RONE),
        alls((a, b), imps((A(sigma, a), A(sigma, b), event_disjoint(a, b)), Eq(A(mu, event_union(a, b)), Add(A(mu, a), A(mu, b)))))
    )


def definitions():
    xs = V('measure_def_list', LIST)
    h = V('measure_def_head', INDEX)
    f = V('measure_def_family', FAMILY)
    a, b = V('measure_extensional_a', EVENT), V('measure_extensional_b', EVENT)
    x = V('measure_extensional_point', OMEGA)
    return {
        'event_function_extensionality': alls((a, b), Imp(All(x, Iff(A(a, x), A(b, x))), Eq(a, b))),
        'list_union_nil': All(f, Eq(union(NIL, f), empty_event())),
        'list_union_cons': alls((f, h, xs), Eq(union(A(CONS, h, xs), f), event_union(A(f, h), union(xs, f)))),
        'list_disjoint_nil': All(f, Eq(disjoint(NIL, f), TRUE)),
        'list_disjoint_cons': alls((f, h, xs), Eq(disjoint(A(CONS, h, xs), f), And(event_disjoint(A(f, h), union(xs, f)), disjoint(xs, f))))
    }


def derive_measurability(kernel):
    xs, tail = V('union_list', LIST), V('union_tail', LIST)
    h = V('union_head', INDEX)
    f = V('union_family', FAMILY)
    sigma, mu = V('union_sigma', SIGMA), V('unused_measure', MEASURE_FUNCTION)
    cond = assumptions(mu, sigma)
    required = (cond[0], cond[2])
    result = lambda ys: A(sigma, union(ys, f))
    body = alls((f, sigma), imps(required + (measurable(xs, f, sigma),), result(xs)))
    base = transformed(kernel, result(NIL), [ax('list_union_nil', f)], lambda _: ('assume', cond[0]))
    base = close(base, (f, sigma), required + (measurable(NIL, f, sigma),))
    ih = substitute(body, xs, tail)
    whole = measurable(A(CONS, h, tail), f, sigma)
    i = V('measurable_family_index', INDEX)
    split = rewrite(kernel, ('assume', whole), ax('every_cons', Lam(i, A(sigma, A(f, i))), h, tail))
    tail_meas = apply(instantiate(('assume', ih), f, sigma), *[('assume', p) for p in required], ('and_r', split))
    pair_meas = apply(instantiate(('assume', cond[2]), A(f, h), union(tail, f)), ('and_l', split), tail_meas)
    step = transformed(kernel, result(A(CONS, h, tail)), [ax('list_union_cons', f, h, tail)], lambda _: pair_meas)
    step = close(close(step, (f, sigma), required + (whole,)), (h, tail), (ih,))
    kernel.theorem('finite_union_measurable', All(xs, body), ('list_induction', xs, h, tail, body, base, step))


def derive_additivity(kernel):
    xs, tail = V('additive_list', LIST), V('additive_tail', LIST)
    h, i = V('additive_head', INDEX), V('additive_index', INDEX)
    f = V('additive_family', FAMILY)
    sigma, mu = V('additive_sigma', SIGMA), V('additive_measure', MEASURE_FUNCTION)
    cond = assumptions(mu, sigma)
    required = (cond[0], cond[2], cond[5], cond[7])
    mass = Lam(i, A(mu, A(f, i)))
    result = lambda ys: Eq(A(mu, union(ys, f)), total(ys, mass))
    body = alls((f, sigma, mu), imps(required + (measurable(xs, f, sigma), disjoint(xs, f)), result(xs)))
    base = polynomial(kernel, result(NIL), [ax('list_union_nil', f), ('assume', cond[5]), ax('sum_nil', mass)])
    base = close(base, (f, sigma, mu), required + (measurable(NIL, f, sigma), disjoint(NIL, f)))
    ih = substitute(body, xs, tail)
    whole = measurable(A(CONS, h, tail), f, sigma)
    p = V('measurable_family_index', INDEX)
    split_meas = rewrite(kernel, ('assume', whole), ax('every_cons', Lam(p, A(sigma, A(f, p))), h, tail))
    whole_disjoint = disjoint(A(CONS, h, tail), f)
    split_disjoint = rewrite(kernel, ('assume', whole_disjoint), ax('list_disjoint_cons', f, h, tail))
    tail_meas = apply(instantiate(('ref', 'finite_union_measurable'), tail, f, sigma), ('assume', cond[0]), ('assume', cond[2]), ('and_r', split_meas))
    pair = apply(instantiate(('assume', cond[7]), A(f, h), union(tail, f)), ('and_l', split_meas), tail_meas, ('and_l', split_disjoint))
    tail_result = apply(instantiate(('assume', ih), f, sigma, mu), *[('assume', q) for q in required], ('and_r', split_meas), ('and_r', split_disjoint))
    step = polynomial(kernel, result(A(CONS, h, tail)), [ax('list_union_cons', f, h, tail), pair, tail_result, ax('sum_cons', mass, h, tail)])
    step = close(close(step, (f, sigma, mu), required + (whole, whole_disjoint)), (h, tail), (ih,))
    kernel.theorem('finite_disjoint_measure_additivity', All(xs, body), ('list_induction', xs, h, tail, body, base, step))


def derive_bounds(kernel):
    sigma, mu = V('bound_sigma', SIGMA), V('bound_measure', MEASURE_FUNCTION)
    a = V('bound_event', EVENT)
    point = V('bound_point', OMEGA)
    cond = assumptions(mu, sigma)
    ha = A(sigma, a)
    complement = event_difference(universe_event(), a)
    partition = event_union(a, complement)
    partition_equal = apply(ax('event_function_extensionality', partition, universe_event()), close(('tautology', normalize(Iff(A(partition, point), A(universe_event(), point)))), (point,)))
    pair_disjoint = close(('tautology', normalize(Imp(And(A(a, point), A(complement, point)), BOTTOM))), (point,))
    pair_disjoint = ('conversion', event_disjoint(a, complement), pair_disjoint)
    complement_meas = apply(instantiate(('assume', cond[3]), universe_event(), a), ('assume', cond[1]), ('assume', ha))
    nonnegative = apply(instantiate(('assume', cond[4]), a), ('assume', ha))
    complement_nonnegative = apply(instantiate(('assume', cond[4]), complement), complement_meas)
    pair = apply(instantiate(('assume', cond[7]), a, complement), ('assume', ha), complement_meas, pair_disjoint)
    pair = polynomial(kernel, Eq(Add(A(mu, a), A(mu, complement)), RONE), [symmetric(A(mu, partition), Add(A(mu, a), A(mu, complement)), pair), partition_equal, ('assume', cond[6])])
    upper = apply(ax('addition_monotone', A(mu, a), A(mu, a), RZERO, A(mu, complement)), ax('real_order_reflexive', A(mu, a)), complement_nonnegative)
    upper = rewrite(kernel, upper, ring(Add(A(mu, a), RZERO), A(mu, a)))
    upper = rewrite(kernel, upper, pair)
    result = And(Le(RZERO, A(mu, a)), Le(A(mu, a), RONE))
    kernel.theorem('normalized_measure_event_bounds', alls((sigma, mu, a), imps(cond + (ha,), result)), close(both((nonnegative, upper)), (sigma, mu, a), cond + (ha,)))
    xs, f, i = V('bounded_union_list', LIST), V('bounded_union_family', FAMILY), V('bounded_union_index', INDEX)
    hm, hd = measurable(xs, f, sigma), disjoint(xs, f)
    measurable_union = apply(instantiate(('ref', 'finite_union_measurable'), xs, f, sigma), ('assume', cond[0]), ('assume', cond[2]), ('assume', hm))
    bounds = apply(instantiate(('ref', 'normalized_measure_event_bounds'), sigma, mu, union(xs, f)), *[('assume', p) for p in cond], measurable_union)
    identity = apply(instantiate(('ref', 'finite_disjoint_measure_additivity'), xs, f, sigma, mu), *[('assume', cond[k]) for k in (0,2,5,7)], ('assume', hm), ('assume', hd))
    sum_bounds = rewrite(kernel, bounds, identity)
    result = And(Eq(A(mu, union(xs, f)), total(xs, Lam(i, A(mu, A(f, i))))), And(Le(RZERO, total(xs, Lam(i, A(mu, A(f, i))))), Le(total(xs, Lam(i, A(mu, A(f, i)))), RONE)))
    proof = both((identity, sum_bounds))
    kernel.theorem('finite_probability_union_and_sum_bounds', alls((sigma, mu, xs, f), imps(cond + (hm, hd), result)), close(proof, (sigma, mu, xs, f), cond + (hm, hd)))


def derive_probability_instance(kernel):
    selected = {
        'sigma_algebra_empty', 'sigma_algebra_finite_union', 'sigma_algebra_difference',
        'measure_nonnegative', 'measure_empty', 'measure_finite_additivity'
    }
    kernel.axioms.update({key: value for key, value in measure_axioms().items() if key in selected})
    kernel.axioms.update({key: value for key, value in simple_function_axioms().items() if key in {'sigma_algebra_universe', 'probability_of_universe'}})
    premises = [('axiom', name) for name in (
        'sigma_algebra_empty', 'sigma_algebra_universe', 'sigma_algebra_finite_union',
        'sigma_algebra_difference', 'measure_nonnegative', 'measure_empty',
        'probability_of_universe', 'measure_finite_additivity'
    )]
    xs, f = V('probability_list', LIST), V('probability_family', FAMILY)
    hm, hd = measurable(xs, f, MEASURABLE), disjoint(xs, f)
    result = apply(instantiate(('ref', 'finite_probability_union_and_sum_bounds'), MEASURABLE, MEASURE, xs, f), *premises, ('assume', hm), ('assume', hd))
    statement = alls((xs, f), imps((hm, hd), kernel.infer(result).conclusion))
    kernel.theorem('probability_finite_disjoint_union', statement, close(result, (xs, f), (hm, hd)))


def certificates():
    kernel = sums.certificates()
    kernel.axioms.update(definitions())
    derive_measurability(kernel)
    derive_additivity(kernel)
    derive_bounds(kernel)
    derive_probability_instance(kernel)
    return kernel


def check(name, value):
    if not value:
        raise AssertionError(name)


def verify():
    kernel = certificates()
    check('finite_disjoint_measure_additivity', 'finite_disjoint_measure_additivity' in kernel.verified and not kernel.verified['finite_disjoint_measure_additivity'].assumptions)
    check('finite_probability_union_and_sum_bounds', 'finite_probability_union_and_sum_bounds' in kernel.verified and not kernel.verified['finite_probability_union_and_sum_bounds'].assumptions)
    check('finite_union_measurable', 'finite_union_measurable' in kernel.verified and not kernel.verified['finite_union_measurable'].assumptions)
    check('normalized_measure_event_bounds', 'normalized_measure_event_bounds' in kernel.verified and not kernel.verified['normalized_measure_event_bounds'].assumptions)
    check('probability_finite_disjoint_union', 'probability_finite_disjoint_union' in kernel.verified and not kernel.verified['probability_finite_disjoint_union'].assumptions)
    return {'backend': 'Python 3 typed proof kernel', 'passed': True, 'results': [{'id': n, 'passed': True} for n in kernel.verified], 'scope': 'Arbitrary finite measurable disjoint family for a nonnegative normalized measure; finite sum and union are linked by structural induction.', 'axioms': list(kernel.axioms)}


if __name__ == '__main__':
    print(json.dumps(verify()))
