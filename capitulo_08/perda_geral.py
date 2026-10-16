from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from capitulo_05 import triplice as d
from capitulo_08 import medias_gerais as m
from capitulo_01 import somas_finitas as s
from capitulo_07.probabilidade_geral import *


def certificates():
    kernel = d.certificates()
    add_axioms(kernel, m.foundations())
    u, v = V('loss_u', 'R'), V('loss_v', 'R')
    three = Add(Add(RONE, RONE), RONE)
    q1, q2 = Mul(u, u), Mul(Add(u, v), Add(u, v))
    squares = Add(q1, q2)
    loss = Add(Mul(three, q1), Mul(three, q2))
    one_nonneg = apply(ax('positive_implies_nonnegative', RONE), ax('average_one_positive'))
    two_positive = apply(ax('average_positive_sum', RONE, RONE), ax('average_one_positive'), one_nonneg)
    three_positive = apply(ax('average_positive_sum', Add(RONE, RONE), RONE), two_positive, one_nonneg)
    three_nonneg = apply(ax('positive_implies_nonnegative', three), three_positive)
    nn1, nn2 = ref('square_nonnegative_general', u), ref('square_nonnegative_general', Add(u, v))
    nn = apply(ax('addition_monotone', RZERO, q1, RZERO, q2), nn1, nn2)
    nn = rewrite(kernel, nn, ring(Add(RZERO, RZERO), RZERO))
    positive = apply(ax('nonnegative_multiplication_monotone', three, RZERO, squares), three_nonneg, nn)
    positive = rewrite(kernel, positive, ring(Mul(three, RZERO), RZERO))
    positive = rewrite(kernel, positive, ring(Mul(three, squares), loss))
    kernel.theorem('quadratic_loss_nonnegative_general', alls((u, v), Le(RZERO, loss)), close(positive, (u, v)))
    zero = Eq(loss, RZERO)
    factored = rewrite(kernel, hyp(zero), ring(loss, Mul(three, squares)))
    choices = apply(ax('field_zero_product', three, squares), factored)
    impossible = rewrite(kernel, three_positive, hyp(Eq(three, RZERO)))
    impossible = apply(ax('real_strict_nonstrict_inconsistent', RZERO, RZERO), impossible, ax('real_order_reflexive', RZERO))
    sumzero = ('or_e', choices, ('false_e', Eq(squares, RZERO), impossible), hyp(Eq(squares, RZERO)))
    split = apply(('and_l', apply(ref('nonnegative_add_zero_iff', q1, q2), nn1, nn2)), sumzero)
    uz = apply(('and_l', ref('square_zero_iff_general', u)), ('and_l', split))
    uvz = apply(('and_l', ref('square_zero_iff_general', Add(u, v))), ('and_r', split))
    vz = s.polynomial(kernel, Eq(Sub(Add(u, v), u), RZERO), [uvz, uz])
    vz = rewrite(kernel, vz, ring(Sub(Add(u, v), u), v))
    zeros = And(Eq(u, RZERO), Eq(v, RZERO))
    backward = s.polynomial(kernel, zero, [('and_l', hyp(zeros)), ('and_r', hyp(zeros))])
    result = ('and_i', close(('and_i', uz, vz), assumptions=(zero,)), close(backward, assumptions=(zeros,)))
    kernel.theorem('quadratic_loss_unique_zero_general', alls((u, v), Iff(zero, zeros)), close(result, (u, v)))
    eta, a, b = V('descent_eta', 'R'), V('descent_a', 'R'), V('descent_b', 'R')
    conditions = (Lt(RZERO, eta), Lt(Mul(eta, b), a))
    gap = apply(('and_l', ax('gram_strict_difference', Mul(eta, b), a)), hyp(conditions[1]))
    product = apply(ax('gram_positive_product', eta, Sub(a, Mul(eta, b))), hyp(conditions[0]), gap)
    delta = Add(Sub(RZERO, Mul(eta, a)), Mul(Mul(eta, eta), b))
    product = rewrite(kernel, product, ring(Mul(eta, Sub(a, Mul(eta, b))), Sub(RZERO, delta)))
    descends = apply(('and_r', ax('gram_strict_difference', delta, RZERO)), product)
    kernel.theorem('quadratic_descent_exact_bound_general', alls((eta, a, b), imps(conditions, Lt(delta, RZERO))), close(descends, (eta, a, b), conditions))
    return kernel


def verify():
    kernel = certificates()
    results = []
    def check(name, condition):
        if not condition:
            raise AssertionError(name)
        results.append({'id': name, 'passed': True})
    check('quadratic_loss_nonnegative_general', 'quadratic_loss_nonnegative_general' in kernel.verified)
    check('quadratic_loss_unique_zero_general', 'quadratic_loss_unique_zero_general' in kernel.verified)
    check('quadratic_descent_exact_bound_general', 'quadratic_descent_exact_bound_general' in kernel.verified)
    check('reject_descent_without_strict_bound', rejects(lambda: kernel.infer(apply(ref('quadratic_descent_exact_bound_general', RONE, RONE, RONE), ax('average_one_positive'), ax('real_order_reflexive', RONE)))))
    return {'passed': True, 'results': results, 'scope': 'All real offsets u,v; quadratic loss is nonnegative and zero exactly at the unique optimum. For every positive step satisfying the exact strict bound, the quadratic update strictly decreases loss.'}


if __name__ == '__main__':
    print(json.dumps(verify()))
