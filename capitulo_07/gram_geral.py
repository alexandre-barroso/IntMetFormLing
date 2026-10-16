from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from capitulo_01 import somas_finitas as s
from capitulo_07.probabilidade_geral import *


def square(x):
    return Mul(x, x)


def squared(f):
    i = V('squared_index', s.INDEX)
    return Lam(i, square(A(f, i)))


def product(f, g):
    i = V('product_index', s.INDEX)
    return Lam(i, Mul(A(f, i), A(g, i)))


def foundations():
    x, y, z, d = (V('gram_' + n, 'R') for n in ('x', 'y', 'z', 'd'))
    return {
        'gram_total_order': alls((x, y), Or(Le(x, y), Le(y, x))),
        'gram_strict_transitive': alls((x, y, z), imps((Lt(x, y), Lt(y, z)), Lt(x, z))),
        'gram_positive_product': alls((x, y), imps((Lt(RZERO, x), Lt(RZERO, y)), Lt(RZERO, Mul(x, y)))),
        'gram_strict_difference': alls((x, y), Iff(Lt(x, y), Lt(RZERO, Sub(y, x)))),
        'gram_strict_addition': alls((x, y, z), Imp(Lt(x, y), Lt(Add(x, z), Add(y, z)))),
        'gram_positive_cancel': alls((d, x), Imp(Lt(RZERO, d), Eq(Div(Mul(d, x), d), x))),
        'gram_division_order': alls((d, x, y), Imp(Lt(RZERO, d), Iff(Le(Div(x, d), y), Le(x, Mul(y, d))))),
        'gram_order_division': alls((d, x, y), Imp(Lt(RZERO, d), Iff(Le(y, Div(x, d)), Le(Mul(y, d), x)))),
    }


def derive_squares(kernel):
    x = V('square_value', 'R')
    positive, negative = Le(RZERO, x), Le(x, RZERO)
    pos = apply(ax('nonnegative_multiplication_monotone', x, RZERO, x), hyp(positive), hyp(positive))
    pos = rewrite(kernel, pos, ring(Mul(x, RZERO), RZERO))
    nx = Sub(RZERO, x)
    neg = apply(ax('addition_right_forward', RZERO, x, RZERO), rewrite(kernel, hyp(negative), ring(Add(RZERO, x), x), True))
    npos = apply(ax('nonnegative_multiplication_monotone', nx, RZERO, nx), neg, neg)
    npos = rewrite(kernel, npos, ring(Mul(nx, RZERO), RZERO))
    npos = rewrite(kernel, npos, ring(square(nx), square(x)))
    result = ('or_e', ax('gram_total_order', RZERO, x), pos, npos)
    kernel.theorem('gram_real_square_nonnegative', All(x, Le(RZERO, square(x))), close(result, (x,)))


def derive_quadratic(kernel):
    xs, t = V('quad_list', s.LIST), V('quad_tail', s.LIST)
    h, i = V('quad_head', s.INDEX), V('quad_index', s.INDEX)
    f, g = V('quad_f', s.FUNCTION), V('quad_g', s.FUNCTION)
    a, b = V('quad_a', 'R'), V('quad_b', 'R')
    comb = Lam(i, square(Add(Mul(a, A(f, i)), Mul(b, A(g, i)))))
    fs, gs, fg = squared(f), squared(g), product(f, g)
    rhs = lambda ys: Add(Add(Mul(square(a), s.total(ys, fs)), Mul(Mul(Add(RONE, RONE), Mul(a, b)), s.total(ys, fg))), Mul(square(b), s.total(ys, gs)))
    result = lambda ys: Eq(s.total(ys, comb), rhs(ys))
    body = alls((f, g, a, b), result(xs))
    base = close(s.polynomial(kernel, result(s.NIL), [ax('sum_nil', fun) for fun in (comb, fs, gs, fg)]), (f, g, a, b))
    ih = substitute(body, xs, t)
    step = s.polynomial(kernel, result(A(s.CONS, h, t)), [ax('sum_cons', fun, h, t) for fun in (comb, fs, gs, fg)] + [instantiate(hyp(ih), f, g, a, b)])
    step = close(close(step, (f, g, a, b)), (h, t), (ih,))
    kernel.theorem('finite_gram_quadratic_identity', All(xs, body), ('list_induction', xs, h, t, body, base, step))
    pointwise = close(ref('gram_real_square_nonnegative', Add(Mul(a, A(f, i)), Mul(b, A(g, i)))), (i,))
    p = Lam(i, Le(RZERO, A(comb, i)))
    all_positive = apply(ref('finite_every_from_all', xs, p), ('conversion', All(i, A(p, i)), pointwise))
    nonnegative = apply(ref('finite_sum_nonnegative', xs, comb), all_positive)
    nonnegative = rewrite(kernel, nonnegative, ref('finite_gram_quadratic_identity', xs, f, g, a, b))
    kernel.theorem('finite_gram_quadratic_nonnegative', alls((xs, f, g, a, b), Le(RZERO, rhs(xs))), close(nonnegative, (xs, f, g, a, b)))
    aa, bb, cc = s.total(xs, fs), s.total(xs, gs), s.total(xs, fg)
    positive = Lt(RZERO, aa)
    q = ref('finite_gram_quadratic_nonnegative', xs, f, g, Sub(RZERO, cc), aa)
    factor = Mul(aa, Sub(Mul(aa, bb), square(cc)))
    q = rewrite(kernel, q, ring(kernel.infer(q).conclusion[2], factor))
    q = rewrite(kernel, q, ring(Mul(aa, RZERO), RZERO), True)
    divided = apply(ax('positive_division_forward', aa, RZERO, factor), hyp(positive), q)
    divided = rewrite(kernel, divided, apply(ax('gram_positive_cancel', aa, Sub(Mul(aa, bb), square(cc))), hyp(positive)))
    ordered = apply(ax('addition_left_backward', square(cc), RZERO, Mul(aa, bb)), divided)
    ordered = rewrite(kernel, ordered, ring(Add(square(cc), RZERO), square(cc)))
    statement = alls((xs, f, g), Imp(positive, Le(square(cc), Mul(aa, bb))))
    kernel.theorem('finite_gram_nonnegative', statement, close(ordered, (xs, f, g), (positive,)))


def derive_normalized(kernel):
    c, d = V('norm_c', 'R'), V('norm_d', 'R')
    pd, bound = Lt(RZERO, d), Le(square(c), square(d))
    upper_opposite = Lt(d, c)
    pc = apply(ax('gram_strict_transitive', RZERO, d, c), hyp(pd), hyp(upper_opposite))
    diff = apply(('and_l', ax('gram_strict_difference', d, c)), hyp(upper_opposite))
    psum = apply(ax('gram_strict_addition', RZERO, d, c), hyp(pd))
    psum = rewrite(kernel, psum, ring(Add(RZERO, c), c))
    psum = apply(ax('gram_strict_transitive', RZERO, c, Add(d, c)), pc, psum)
    prod = apply(ax('gram_positive_product', Sub(c, d), Add(d, c)), diff, psum)
    prod = rewrite(kernel, prod, ring(Mul(Sub(c, d), Add(d, c)), Sub(square(c), square(d))))
    too_big = apply(('and_r', ax('gram_strict_difference', square(d), square(c))), prod)
    contradiction = apply(ax('real_strict_nonstrict_inconsistent', square(d), square(c)), too_big, hyp(bound))
    upper = apply(ax('real_order_not_reverse_strict', c, d), close(contradiction, assumptions=(upper_opposite,)))
    kernel.theorem('square_bound_upper', alls((c, d), imps((pd, bound), Le(c, d))), close(upper, (c, d), (pd, bound)))
    negc = Sub(RZERO, c)
    negative_bound = rewrite(kernel, hyp(bound), ring(square(negc), square(c)), True)
    negative_upper = apply(ref('square_bound_upper', negc, d), hyp(pd), negative_bound)
    shifted = apply(ax('addition_monotone', negc, d, c, c), negative_upper, ax('real_order_reflexive', c))
    shifted = rewrite(kernel, shifted, ring(Add(negc, c), RZERO))
    add_negd = apply(ax('addition_monotone', RZERO, Add(d, c), Sub(RZERO, d), Sub(RZERO, d)), shifted, ax('real_order_reflexive', Sub(RZERO, d)))
    lower = rewrite(kernel, add_negd, ring(Add(RZERO, Sub(RZERO, d)), Sub(RZERO, d)))
    lower = rewrite(kernel, lower, ring(Add(Add(d, c), Sub(RZERO, d)), c))
    minus_one = Sub(RZERO, RONE)
    up = apply(('and_r', apply(ax('gram_division_order', d, c, RONE), hyp(pd))), rewrite(kernel, upper, ring(Mul(RONE, d), d), True))
    lo = apply(('and_r', apply(ax('gram_order_division', d, c, minus_one), hyp(pd))), rewrite(kernel, lower, ring(Mul(minus_one, d), Sub(RZERO, d)), True))
    kernel.theorem('positive_normalized_square_range', alls((c, d), imps((pd, bound), And(Le(minus_one, Div(c, d)), Le(Div(c, d), RONE)))), close(('and_i', lo, up), (c, d), (pd, bound)))
    xs = V('range_list', s.LIST)
    f, g = V('range_f', s.FUNCTION), V('range_g', s.FUNCTION)
    aa, bb, cc = s.total(xs, squared(f)), s.total(xs, squared(g)), s.total(xs, product(f, g))
    conditions = (Lt(RZERO, aa), Lt(RZERO, bb), pd, Eq(square(d), Mul(aa, bb)))
    gram = apply(ref('finite_gram_nonnegative', xs, f, g), hyp(conditions[0]))
    gram = rewrite(kernel, gram, hyp(conditions[3]), True)
    result = apply(ref('positive_normalized_square_range', cc, d), hyp(pd), gram)
    statement = alls((xs, f, g, d), imps(conditions, And(Le(minus_one, Div(cc, d)), Le(Div(cc, d), RONE))))
    kernel.theorem('finite_normalized_dot_range', statement, close(result, (xs, f, g, d), conditions))


def certificates():
    kernel = s.certificates()
    add_axioms(kernel, foundations())
    derive_squares(kernel)
    derive_quadratic(kernel)
    derive_normalized(kernel)
    return kernel


def verify():
    kernel = certificates()
    results = []
    def check(name, condition):
        if not condition:
            raise AssertionError(name)
        results.append({'id': name, 'passed': True})
    check('finite_gram_nonnegative', 'finite_gram_nonnegative' in kernel.verified)
    check('finite_normalized_dot_range', 'finite_normalized_dot_range' in kernel.verified)
    check('reject_missing_positive_denominator', rejects(lambda: kernel.infer(apply(ref('positive_normalized_square_range', RONE, RZERO), ax('real_order_reflexive', RZERO)))))
    return {'passed': True, 'results': results, 'scope': 'Arbitrary finite real vectors, checked induction on recursive finite sums and ordered-field deduction; positive norm and square-root denominator hypotheses are explicit.', 'axioms': list(kernel.axioms)}


if __name__ == '__main__':
    print(json.dumps(verify()))
