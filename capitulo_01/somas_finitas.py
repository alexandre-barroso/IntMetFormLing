from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from capitulo_07.probabilidade_geral import V, C, FT, A, Lam, All, Imp, And, Eq, Iff, Kernel, instantiate, apply, close, alls, imps, RZERO, RONE, Le, Add, Sub, Mul, Div, field_axioms, ax, ring, rewrite, symmetric, replace_subterm, substitute, sort_of, same, normalize, rejects

INDEX = 'FiniteIndex'
LIST = ('List', INDEX)
FUNCTION = FT(INDEX, 'R')
PREDICATE = FT(INDEX, 'Prop')
NIL = C('list_nil', LIST)
CONS = C('list_cons', FT(INDEX, FT(LIST, LIST)))
SUM = C('finite_sum', FT(LIST, FT(FUNCTION, 'R')))
EVERY = C('finite_every', FT(LIST, FT(PREDICATE, 'Prop')))
TRUE = Eq(RZERO, RZERO)


def total(xs, f):
    return A(SUM, xs, f)


def every(xs, p):
    return A(EVERY, xs, p)


def both(proofs):
    left, right = proofs
    return ('and_i', left, right)


def transformed(kernel, target, equalities, leaf):
    target = normalize(target)
    steps = []
    for number, equality in enumerate(equalities):
        normalized = normalize(kernel.infer(equality).conclusion)
        equality = ('conversion', normalized, equality)
        left, right = normalized[1:]
        variable = V('fold_rewrite_' + str(number), sort_of(left))
        pattern = replace_subterm(target, left, variable)
        if pattern == target:
            continue
        steps.append((left, right, equality, variable, pattern))
        target = substitute(pattern, variable, right)
    proof = leaf(target)
    if not same(kernel.infer(proof).conclusion, target):
        raise ValueError(('leaf mismatch', target, kernel.infer(proof).conclusion))
    for left, right, equality, variable, pattern in reversed(steps):
        proof = ('eq_e', symmetric(left, right, equality), variable, pattern, proof)
    return proof


def polynomial(kernel, target, equalities):
    return transformed(kernel, target, equalities, lambda formula: ('ring', formula))


def definition_axioms():
    f = V('fold_function', FUNCTION)
    p = V('fold_predicate', PREDICATE)
    h = V('fold_head', INDEX)
    t = V('fold_tail', LIST)
    return {
        'sum_nil': alls((f,), Eq(total(NIL, f), RZERO)),
        'sum_cons': alls((f, h, t), Eq(total(A(CONS, h, t), f), Add(A(f, h), total(t, f)))),
        'every_nil': alls((p,), Eq(every(NIL, p), TRUE)),
        'every_cons': alls((p, h, t), Eq(every(A(CONS, h, t), p), And(A(p, h), every(t, p)))),
    }


def derive_scalar_zero(kernel):
    a, b = V('sum_left', 'R'), V('sum_right', 'R')
    ha, hb = Le(RZERO, a), Le(RZERO, b)
    hz = Eq(Add(a, b), RZERO)
    a_le_sum = apply(ax('addition_monotone', a, a, RZERO, b), ax('real_order_reflexive', a), ('assume', hb))
    a_le_sum = rewrite(kernel, a_le_sum, ring(Add(a, RZERO), a))
    a_le_zero = rewrite(kernel, a_le_sum, ('assume', hz))
    az = apply(ax('real_order_antisymmetric', a, RZERO), a_le_zero, ('assume', ha))
    b_le_sum = apply(ax('addition_monotone', RZERO, a, b, b), ('assume', ha), ax('real_order_reflexive', b))
    b_le_sum = rewrite(kernel, b_le_sum, ring(Add(RZERO, b), b))
    bz = apply(ax('real_order_antisymmetric', b, RZERO), rewrite(kernel, b_le_sum, ('assume', hz)), ('assume', hb))
    pair = And(Eq(a, RZERO), Eq(b, RZERO))
    back = polynomial(kernel, hz, [('and_l', ('assume', pair)), ('and_r', ('assume', pair))])
    proof = both((close(both((az, bz)), assumptions=(hz,)), close(back, assumptions=(pair,))))
    statement = alls((a, b), imps((ha, hb), Iff(hz, pair)))
    kernel.theorem('nonnegative_add_zero_iff', statement, close(proof, (a, b), (ha, hb)))


def derive_linear(kernel):
    xs, t = V('linear_list', LIST), V('linear_tail', LIST)
    h = V('linear_head', INDEX)
    f, g = V('linear_f', FUNCTION), V('linear_g', FUNCTION)
    a, b, i = V('linear_a', 'R'), V('linear_b', 'R'), V('linear_index', INDEX)
    comb = Lam(i, Add(Mul(a, A(f, i)), Mul(b, A(g, i))))
    result = lambda ys: Eq(total(ys, comb), Add(Mul(a, total(ys, f)), Mul(b, total(ys, g))))
    body = alls((f, g, a, b), result(xs))
    base = close(polynomial(kernel, result(NIL), [ax('sum_nil', fun) for fun in (comb, f, g)]), (f, g, a, b))
    ih = substitute(body, xs, t)
    step = polynomial(kernel, result(A(CONS, h, t)), [ax('sum_cons', fun, h, t) for fun in (comb, f, g)] + [instantiate(('assume', ih), f, g, a, b)])
    step = close(close(step, (f, g, a, b)), (h, t), (ih,))
    kernel.theorem('finite_sum_linear', All(xs, body), ('list_induction', xs, h, t, body, base, step))


def derive_nonnegative(kernel):
    xs, t = V('positive_list', LIST), V('positive_tail', LIST)
    h, i = V('positive_head', INDEX), V('positive_index', INDEX)
    f = V('positive_f', FUNCTION)
    p = Lam(i, Le(RZERO, A(f, i)))
    result = lambda ys: Imp(every(ys, p), Le(RZERO, total(ys, f)))
    body = All(f, result(xs))
    base = transformed(kernel, Le(RZERO, total(NIL, f)), [ax('sum_nil', f)], lambda _: ax('real_order_reflexive', RZERO))
    base = close(base, (f,), (every(NIL, p),))
    ih = substitute(body, xs, t)
    whole = every(A(CONS, h, t), p)
    split = rewrite(kernel, ('assume', whole), ax('every_cons', p, h, t))
    tail = apply(instantiate(('assume', ih), f), ('and_r', split))
    positive = apply(ax('addition_monotone', RZERO, A(f, h), RZERO, total(t, f)), ('and_l', split), tail)
    positive = rewrite(kernel, positive, ring(Add(RZERO, RZERO), RZERO))
    positive = rewrite(kernel, positive, ax('sum_cons', f, h, t), reverse=True)
    step = close(close(positive, (f,), (whole,)), (h, t), (ih,))
    kernel.theorem('finite_sum_nonnegative', All(xs, body), ('list_induction', xs, h, t, body, base, step))


def derive_zero(kernel):
    xs, t = V('zero_list', LIST), V('zero_tail', LIST)
    h, i = V('zero_head', INDEX), V('zero_index', INDEX)
    f = V('zero_f', FUNCTION)
    positive = Lam(i, Le(RZERO, A(f, i)))
    zero = Lam(i, Eq(A(f, i), RZERO))
    result = lambda ys: Iff(Eq(total(ys, f), RZERO), every(ys, zero))
    body = All(f, Imp(every(xs, positive), result(xs)))
    base = transformed(kernel, result(NIL), [ax('sum_nil', f), ax('every_nil', zero)], lambda formula: ('tautology', normalize(formula)))
    base = close(base, (f,), (every(NIL, positive),))
    ih = substitute(body, xs, t)
    whole_positive = every(A(CONS, h, t), positive)
    split_positive = rewrite(kernel, ('assume', whole_positive), ax('every_cons', positive, h, t))
    tail_positive = ('and_r', split_positive)
    tail_nonnegative = apply(instantiate(('ref', 'finite_sum_nonnegative'), t, f), tail_positive)
    scalar = apply(instantiate(('ref', 'nonnegative_add_zero_iff'), A(f, h), total(t, f)), ('and_l', split_positive), tail_nonnegative)
    tail_equivalence = apply(instantiate(('assume', ih), f), tail_positive)
    sum_zero = Eq(total(A(CONS, h, t), f), RZERO)
    expanded_zero = rewrite(kernel, ('assume', sum_zero), ax('sum_cons', f, h, t))
    scalar_zeros = apply(('and_l', scalar), expanded_zero)
    tail_zeros = apply(('and_l', tail_equivalence), ('and_r', scalar_zeros))
    all_zeros = both((('and_l', scalar_zeros), tail_zeros))
    all_zeros = rewrite(kernel, all_zeros, ax('every_cons', zero, h, t), reverse=True)
    forward = close(all_zeros, assumptions=(sum_zero,))
    whole_zero = every(A(CONS, h, t), zero)
    split_zero = rewrite(kernel, ('assume', whole_zero), ax('every_cons', zero, h, t))
    tail_zero = apply(('and_r', tail_equivalence), ('and_r', split_zero))
    back = apply(('and_r', scalar), both((('and_l', split_zero), tail_zero)))
    back = rewrite(kernel, back, ax('sum_cons', f, h, t), reverse=True)
    backward = close(back, assumptions=(whole_zero,))
    step = close(close(both((forward, backward)), (f,), (whole_positive,)), (h, t), (ih,))
    kernel.theorem('finite_nonnegative_sum_zero_iff', All(xs, body), ('list_induction', xs, h, t, body, base, step))


def derive_congruence(kernel):
    xs, t = V('congr_list', LIST), V('congr_tail', LIST)
    h, i = V('congr_head', INDEX), V('congr_index', INDEX)
    f, g = V('congr_f', FUNCTION), V('congr_g', FUNCTION)
    p = Lam(i, Eq(A(f, i), A(g, i)))
    result = lambda ys: Imp(every(ys, p), Eq(total(ys, f), total(ys, g)))
    body = alls((f, g), result(xs))
    base = close(polynomial(kernel, Eq(total(NIL, f), total(NIL, g)), [ax('sum_nil', f), ax('sum_nil', g)]), (f, g), (every(NIL, p),))
    ih = substitute(body, xs, t)
    whole = every(A(CONS, h, t), p)
    split = rewrite(kernel, ('assume', whole), ax('every_cons', p, h, t))
    tail = apply(instantiate(('assume', ih), f, g), ('and_r', split))
    step = polynomial(kernel, Eq(total(A(CONS, h, t), f), total(A(CONS, h, t), g)), [ax('sum_cons', f, h, t), ax('sum_cons', g, h, t), ('and_l', split), tail])
    step = close(close(step, (f, g), (whole,)), (h, t), (ih,))
    kernel.theorem('finite_sum_congruence', All(xs, body), ('list_induction', xs, h, t, body, base, step))


def derive_every(kernel):
    xs, t = V('every_list', LIST), V('every_tail', LIST)
    h, i = V('every_head', INDEX), V('every_index', INDEX)
    p, q = V('every_p', PREDICATE), V('every_q', PREDICATE)
    premise = All(i, A(p, i))
    body = All(p, Imp(premise, every(xs, p)))
    base = transformed(kernel, every(NIL, p), [ax('every_nil', p)], lambda _: ('eq_i', RZERO))
    base = close(base, (p,), (premise,))
    ih = substitute(body, xs, t)
    head = instantiate(('assume', premise), h)
    tail = apply(instantiate(('assume', ih), p), ('assume', premise))
    step = rewrite(kernel, both((head, tail)), ax('every_cons', p, h, t), reverse=True)
    step = close(close(step, (p,), (premise,)), (h, t), (ih,))
    kernel.theorem('finite_every_from_all', All(xs, body), ('list_induction', xs, h, t, body, base, step))
    implication = All(i, Imp(A(p, i), A(q, i)))
    body = alls((p, q), imps((implication, every(xs, p)), every(xs, q)))
    base = transformed(kernel, every(NIL, q), [ax('every_nil', q)], lambda _: ('eq_i', RZERO))
    base = close(base, (p, q), (implication, every(NIL, p)))
    ih = substitute(body, xs, t)
    whole = every(A(CONS, h, t), p)
    split = rewrite(kernel, ('assume', whole), ax('every_cons', p, h, t))
    head = apply(instantiate(('assume', implication), h), ('and_l', split))
    tail = apply(instantiate(('assume', ih), p, q), ('assume', implication), ('and_r', split))
    step = rewrite(kernel, both((head, tail)), ax('every_cons', q, h, t), reverse=True)
    step = close(close(step, (p, q), (implication, whole)), (h, t), (ih,))
    kernel.theorem('finite_every_implication', All(xs, body), ('list_induction', xs, h, t, body, base, step))


def derive_elementary_sums(kernel):
    xs, t = V('elementary_list', LIST), V('elementary_tail', LIST)
    h, i = V('elementary_head', INDEX), V('elementary_index', INDEX)
    f, g = V('elementary_f', FUNCTION), V('elementary_g', FUNCTION)
    a = V('elementary_scalar', 'R')
    one = Lam(i, RONE)
    specifications = [
        ('finite_sum_add', (f, g), Lam(i, Add(A(f, i), A(g, i))), (f, g), lambda ys: Add(total(ys, f), total(ys, g))),
        ('finite_sum_subtract', (f, g), Lam(i, Sub(A(f, i), A(g, i))), (f, g), lambda ys: Sub(total(ys, f), total(ys, g))),
        ('finite_sum_scale', (f, a), Lam(i, Mul(a, A(f, i))), (f,), lambda ys: Mul(a, total(ys, f))),
        ('finite_sum_constant', (a,), Lam(i, a), (one,), lambda ys: Mul(a, total(ys, one))),
    ]
    for name, variables, combined, parts, right in specifications:
        result = lambda ys: Eq(total(ys, combined), right(ys))
        body = alls(variables, result(xs))
        base = close(polynomial(kernel, result(NIL), [ax('sum_nil', fun) for fun in (combined, *parts)]), variables)
        ih = substitute(body, xs, t)
        step = polynomial(kernel, result(A(CONS, h, t)), [ax('sum_cons', fun, h, t) for fun in (combined, *parts)] + [instantiate(('assume', ih), *variables)])
        step = close(close(step, variables), (h, t), (ih,))
        kernel.theorem(name, All(xs, body), ('list_induction', xs, h, t, body, base, step))


def certificates():
    kernel = Kernel(field_axioms() | definition_axioms())
    derive_scalar_zero(kernel)
    derive_linear(kernel)
    derive_nonnegative(kernel)
    derive_zero(kernel)
    derive_congruence(kernel)
    derive_every(kernel)
    derive_elementary_sums(kernel)
    return kernel


def check(name, value):
    if not value:
        raise AssertionError(name)


def verify():
    kernel = certificates()
    check('finite_every_from_all', 'finite_every_from_all' in kernel.verified and not kernel.verified['finite_every_from_all'].assumptions)
    check('finite_every_implication', 'finite_every_implication' in kernel.verified and not kernel.verified['finite_every_implication'].assumptions)
    check('finite_nonnegative_sum_zero_iff', 'finite_nonnegative_sum_zero_iff' in kernel.verified and not kernel.verified['finite_nonnegative_sum_zero_iff'].assumptions)
    check('finite_sum_congruence', 'finite_sum_congruence' in kernel.verified and not kernel.verified['finite_sum_congruence'].assumptions)
    check('finite_sum_linear', 'finite_sum_linear' in kernel.verified and not kernel.verified['finite_sum_linear'].assumptions)
    check('finite_sum_nonnegative', 'finite_sum_nonnegative' in kernel.verified and not kernel.verified['finite_sum_nonnegative'].assumptions)
    check('nonnegative_add_zero_iff', 'nonnegative_add_zero_iff' in kernel.verified and not kernel.verified['nonnegative_add_zero_iff'].assumptions)
    check('finite_sum_add', 'finite_sum_add' in kernel.verified and not kernel.verified['finite_sum_add'].assumptions)
    check('finite_sum_subtract', 'finite_sum_subtract' in kernel.verified and not kernel.verified['finite_sum_subtract'].assumptions)
    check('finite_sum_scale', 'finite_sum_scale' in kernel.verified and not kernel.verified['finite_sum_scale'].assumptions)
    check('finite_sum_constant', 'finite_sum_constant' in kernel.verified and not kernel.verified['finite_sum_constant'].assumptions)
    mutated = list(kernel.records[-1][2])
    mutated[-1] = mutated[-2]
    rejected = rejects(lambda: Kernel(kernel.axioms).infer(tuple(mutated)))
    if not rejected:
        raise AssertionError('invalid induction accepted')
    return {'backend': 'Python 3 finite-sum proof kernel', 'passed': True, 'results': [{'id': name, 'passed': True} for name in kernel.verified] + [{'id': 'reject_wrong_induction_step', 'passed': rejected}], 'axioms': list(kernel.axioms), 'scope': 'Arbitrary finite lists of indices and arbitrary real functions; sum linearity, nonnegativity, zero characterization and congruence are replayed from recursive definitions by checked list induction.'}


if __name__ == '__main__':
    print(json.dumps(verify()))
