from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from capitulo_01.somas_finitas import *
from capitulo_07.probabilidade_geral import Or, Lt, BOTTOM, eq_trans
import capitulo_01.somas_finitas as sums


def sum_of_pointwise_equality(kernel, xs, f, g, pointwise):
    i = V('pointwise_sum_index', INDEX)
    premise = Lam(i, Eq(A(f, i), A(g, i)))
    local = apply(instantiate(('ref', 'finite_every_from_all'), xs, premise), pointwise)
    return apply(instantiate(('ref', 'finite_sum_congruence'), xs, f, g), local)


def derive_expectation(kernel):
    xs, t, ys = V('opportunities', LIST), V('opportunity_tail', LIST), V('outcomes', LIST)
    h, i, j = V('opportunity_head', INDEX), V('opportunity_index', INDEX), V('outcome_index', INDEX)
    w = V('outcome_weight', FUNCTION)
    f = V('indicator', FT(INDEX, FUNCTION))
    q = V('common_expectation', 'R')
    count = lambda zs: total(zs, Lam(i, RONE))
    expected_indicator = lambda a: total(ys, Lam(j, Mul(A(w, j), A(f, a, j))))
    means = Lam(i, Eq(expected_indicator(i), q))
    outcome_sum = lambda zs: Lam(j, Mul(A(w, j), total(zs, Lam(i, A(f, i, j)))))
    expected = lambda zs: total(ys, outcome_sum(zs))
    result = lambda zs: Eq(expected(zs), Mul(q, count(zs)))
    variables = (ys, w, f, q)
    body = alls(variables, Imp(every(xs, means), result(xs)))
    zero = Lam(j, RZERO)
    pointwise = polynomial(kernel, Eq(A(outcome_sum(NIL), j), RZERO), [ax('sum_nil', Lam(i, A(f, i, j)))])
    base_eq = sum_of_pointwise_equality(kernel, ys, outcome_sum(NIL), zero, close(pointwise, (j,)))
    base = polynomial(kernel, result(NIL), [base_eq, instantiate(('ref', 'finite_sum_constant'), ys, RZERO), ax('sum_nil', Lam(i, RONE))])
    base = close(base, variables, (every(NIL, means),))
    ih = substitute(body, xs, t)
    whole = every(A(CONS, h, t), means)
    split = rewrite(kernel, ('assume', whole), ax('every_cons', means, h, t))
    tail = apply(instantiate(('assume', ih), *variables), ('and_r', split))
    head_function = Lam(j, Mul(A(w, j), A(f, h, j)))
    tail_function = outcome_sum(t)
    combined = Lam(j, Add(A(head_function, j), A(tail_function, j)))
    pointwise = polynomial(kernel, Eq(A(outcome_sum(A(CONS, h, t)), j), A(combined, j)), [ax('sum_cons', Lam(i, A(f, i, j)), h, t)])
    step_eq = sum_of_pointwise_equality(kernel, ys, outcome_sum(A(CONS, h, t)), combined, close(pointwise, (j,)))
    step = polynomial(kernel, result(A(CONS, h, t)), [step_eq, instantiate(('ref', 'finite_sum_add'), ys, head_function, tail_function), ('and_l', split), tail, ax('sum_cons', Lam(i, RONE), h, t)])
    step = close(close(step, variables, (whole,)), (h, t), (ih,))
    kernel.theorem('finite_expected_count_from_equal_marginals', All(xs, body), ('list_induction', xs, h, t, body, base, step))


def certificates():
    kernel = sums.certificates()
    derive_expectation(kernel)
    return kernel


def check(name, value):
    if not value:
        raise AssertionError(name)


def verify():
    kernel = certificates()
    check('finite_expected_count_from_equal_marginals', 'finite_expected_count_from_equal_marginals' in kernel.verified and not kernel.verified['finite_expected_count_from_equal_marginals'].assumptions)
    return {'backend': 'Python 3 typed proof kernel', 'passed': True, 'results': [{'id': name, 'passed': True} for name in kernel.verified], 'scope': 'Finite weighted expectation from actual nested sums, no independence premise and no fixed number of opportunities.', 'axioms': list(kernel.axioms)}


if __name__ == '__main__':
    print(json.dumps(verify()))
