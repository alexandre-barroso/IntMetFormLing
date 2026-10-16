from pathlib import Path
import json
import sys
import itertools

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from capitulo_01.somas_finitas import *
from capitulo_07.probabilidade_geral import Or, BOTTOM, eq_trans
import capitulo_01.somas_finitas as sums

IND = C('proposition_indicator', FT('Prop', 'R'))
MEM = C('list_membership', FT(INDEX, FT(LIST, 'Prop')))
SNOC = C('list_append_one', FT(LIST, FT(INDEX, LIST)))
LENGTH = C('list_length_real', FT(LIST, 'R'))
DISTINCT = C('list_distinct_count', FT(LIST, 'R'))
COUNT = C('list_filter_count', FT(LIST, FT(PREDICATE, 'R')))


def neg(p):
    return Imp(p, BOTTOM)


def logical(target, premises=()):
    formula = imps(tuple(p for p, _ in premises), target)
    return apply(('tautology', normalize(formula)), *(proof for _, proof in premises))


def indicator_axioms():
    p, q = V('indicator_p', 'Prop'), V('indicator_q', 'Prop')
    return {
        'indicator_true': All(p, Imp(p, Eq(A(IND, p), RONE))),
        'indicator_false': All(p, Imp(neg(p), Eq(A(IND, p), RZERO))),
        'propositional_extensionality': alls((p, q), Imp(Iff(p, q), Eq(p, q))),
    }


def definition_axioms():
    h, a, b = V('list_head', INDEX), V('list_added', INDEX), V('list_searched', INDEX)
    t = V('list_tail', LIST)
    p = V('filter_predicate', PREDICATE)
    return indicator_axioms() | {
        'membership_nil': All(a, Eq(A(MEM, a, NIL), BOTTOM)),
        'membership_cons': alls((a, h, t), Eq(A(MEM, a, A(CONS, h, t)), Or(Eq(a, h), A(MEM, a, t)))),
        'append_nil': All(a, Eq(A(SNOC, NIL, a), A(CONS, a, NIL))),
        'append_cons': alls((h, t, a), Eq(A(SNOC, A(CONS, h, t), a), A(CONS, h, A(SNOC, t, a)))),
        'length_nil': Eq(A(LENGTH, NIL), RZERO),
        'length_cons': alls((h, t), Eq(A(LENGTH, A(CONS, h, t)), Add(RONE, A(LENGTH, t)))),
        'distinct_nil': Eq(A(DISTINCT, NIL), RZERO),
        'distinct_cons': alls((h, t), Eq(A(DISTINCT, A(CONS, h, t)), Sub(Add(A(DISTINCT, t), RONE), A(IND, A(MEM, h, t))))),
        'filter_count_nil': All(p, Eq(A(COUNT, NIL, p), RZERO)),
        'filter_count_cons': alls((h, t, p), Eq(A(COUNT, A(CONS, h, t), p), Add(A(IND, A(p, h)), A(COUNT, t, p)))),
    }


def case_split(propositions, leaf, assumptions=()):
    if not propositions:
        return leaf(assumptions)
    p, *rest = propositions
    left = case_split(rest, leaf, assumptions + ((p, True),))
    right = case_split(rest, leaf, assumptions + ((p, False),))
    return ('or_e', ('tautology', Or(p, neg(p))), left, right)


def case_premises(assumptions):
    return tuple((p if value else neg(p), ('assume', p if value else neg(p))) for p, value in assumptions)


def derive_indicators(kernel):
    p, q, r = (V('boolean_' + name, 'Prop') for name in ('p', 'q', 'r'))
    goal = Eq(Mul(A(IND, p), A(IND, q)), A(IND, And(p, q)))
    def leaf(assumptions):
        values = dict(assumptions)
        premises = case_premises(assumptions)
        equalities = []
        for prop, value in [(p, values[p]), (q, values[q]), (And(p, q), values[p] and values[q])]:
            truth = logical(prop if value else neg(prop), premises)
            equalities.append(apply(ax('indicator_true' if value else 'indicator_false', prop), truth))
        return polynomial(kernel, goal, equalities)
    kernel.theorem('indicator_conjunction_product', alls((p, q), goal), close(case_split((p, q), leaf), (p, q)))
    compatibility = Imp(p, Iff(q, r))
    goal = Eq(Add(A(IND, r), A(IND, Or(p, q))), Add(A(IND, q), A(IND, Or(r, p))))
    def leaf(assumptions):
        values = dict(assumptions)
        premises = case_premises(assumptions) + ((compatibility, ('assume', compatibility)),)
        if values[p] and values[q] != values[r]:
            return ('false_e', goal, logical(BOTTOM, premises))
        equalities = []
        for prop, value in [(r, values[r]), (q, values[q]), (Or(p, q), values[p] or values[q]), (Or(r, p), values[r] or values[p])]:
            equalities.append(apply(ax('indicator_true' if value else 'indicator_false', prop), logical(prop if value else neg(prop), premises)))
        return polynomial(kernel, goal, equalities)
    kernel.theorem('indicator_inventory_balance', alls((p, q, r), Imp(compatibility, goal)), close(case_split((p, q, r), leaf), (p, q, r), (compatibility,)))


def derive_membership(kernel):
    xs, t = V('membership_list', LIST), V('membership_tail', LIST)
    h, a, b = V('membership_head', INDEX), V('membership_added', INDEX), V('membership_searched', INDEX)
    left = lambda ys: A(MEM, b, A(SNOC, ys, a))
    right = lambda ys: Or(A(MEM, b, ys), Eq(b, a))
    result = lambda ys: Iff(left(ys), right(ys))
    body = alls((a, b), result(xs))
    base = transformed(kernel, result(NIL), [ax('append_nil', a), ax('membership_cons', b, a, NIL), ax('membership_nil', b)], lambda f: ('tautology', normalize(f)))
    base = close(base, (a, b))
    ih = substitute(body, xs, t)
    ih_iff = instantiate(('assume', ih), a, b)
    ih_eq = apply(ax('propositional_extensionality', left(t), right(t)), ih_iff)
    step = transformed(kernel, result(A(CONS, h, t)), [ax('append_cons', h, t, a), ax('membership_cons', b, h, A(SNOC, t, a)), ax('membership_cons', b, h, t), ih_eq], lambda f: ('tautology', normalize(f)))
    step = close(close(step, (a, b)), (h, t), (ih,))
    kernel.theorem('finite_membership_append', All(xs, body), ('list_induction', xs, h, t, body, base, step))
    xs = V('membership_equality_list', LIST)
    a, b = V('membership_equal_a', INDEX), V('membership_equal_b', INDEX)
    equality = Eq(a, b)
    var = V('membership_equality_placeholder', INDEX)
    formula = Eq(A(MEM, a, xs), A(MEM, b, xs))
    proof = ('eq_e', ('assume', equality), var, Eq(A(MEM, a, xs), A(MEM, var, xs)), ('eq_i', A(MEM, a, xs)))
    kernel.theorem('equal_forms_equal_membership', alls((xs, a, b), Imp(equality, formula)), close(proof, (xs, a, b), (equality,)))


def derive_counts(kernel):
    xs, t = V('count_list', LIST), V('count_tail', LIST)
    h, a = V('count_head', INDEX), V('count_added', INDEX)
    result = lambda ys: Eq(A(LENGTH, A(SNOC, ys, a)), Add(A(LENGTH, ys), RONE))
    body = All(a, result(xs))
    base = polynomial(kernel, result(NIL), [ax('append_nil', a), ax('length_cons', a, NIL), ax('length_nil')])
    base = close(base, (a,))
    ih = substitute(body, xs, t)
    step = polynomial(kernel, result(A(CONS, h, t)), [ax('append_cons', h, t, a), ax('length_cons', h, A(SNOC, t, a)), ax('length_cons', h, t), instantiate(('assume', ih), a)])
    step = close(close(step, (a,)), (h, t), (ih,))
    kernel.theorem('finite_token_count_append', All(xs, body), ('list_induction', xs, h, t, body, base, step))
    result = lambda ys: Eq(A(DISTINCT, A(SNOC, ys, a)), Sub(Add(A(DISTINCT, ys), RONE), A(IND, A(MEM, a, ys))))
    body = All(a, result(xs))
    base = polynomial(kernel, result(NIL), [ax('append_nil', a), ax('distinct_cons', a, NIL), ax('distinct_nil')])
    base = close(base, (a,))
    ih = substitute(body, xs, t)
    eqsym = Iff(Eq(h, a), Eq(a, h))
    forward = close(symmetric(h, a, ('assume', Eq(h, a))), assumptions=(Eq(h, a),))
    backward = close(symmetric(a, h, ('assume', Eq(a, h))), assumptions=(Eq(a, h),))
    eqsym = apply(ax('propositional_extensionality', Eq(h, a), Eq(a, h)), both((forward, backward)))
    membership_iff = instantiate(('ref', 'finite_membership_append'), t, a, h)
    membership_eq = apply(ax('propositional_extensionality', A(MEM, h, A(SNOC, t, a)), Or(A(MEM, h, t), Eq(h, a))), membership_iff)
    p, q, r = Eq(a, h), A(MEM, a, t), A(MEM, h, t)
    same_mem = apply(instantiate(('ref', 'equal_forms_equal_membership'), t, a, h), ('assume', p))
    equivalence = transformed(kernel, Iff(q, r), [same_mem], lambda f: ('tautology', normalize(f)))
    compatibility = close(equivalence, assumptions=(p,))
    balance = apply(instantiate(('ref', 'indicator_inventory_balance'), p, q, r), compatibility)
    equalities = [ax('append_cons', h, t, a), ax('distinct_cons', h, A(SNOC, t, a)), ax('distinct_cons', h, t), instantiate(('assume', ih), a), ax('membership_cons', a, h, t), membership_eq, eqsym]
    def leaf(formula):
        eq = kernel.infer(balance).conclusion
        difference = Sub(eq[1], eq[2])
        zero = polynomial(kernel, Eq(difference, RZERO), [balance])
        left, right = formula[1:]
        proof = eq_trans(Sub(left, right), difference, RZERO, ring(Sub(left, right), difference), zero)
        variable = V('inventory_difference', 'R')
        restored = ('eq_e', symmetric(Sub(left, right), RZERO, proof), variable, Eq(Add(variable, right), right), ring(Add(RZERO, right), right))
        return rewrite(kernel, restored, ring(Add(Sub(left, right), right), left))
    step = transformed(kernel, result(A(CONS, h, t)), equalities, leaf)
    step = close(close(step, (a,)), (h, t), (ih,))
    kernel.theorem('finite_type_count_append', All(xs, body), ('list_induction', xs, h, t, body, base, step))
    old = A(MEM, a, xs)
    general = instantiate(('ref', 'finite_type_count_append'), xs, a)
    for name, condition, value in [('finite_repeated_type_inventory', old, RZERO), ('finite_new_type_inventory', neg(old), RONE)]:
        branch = apply(ax('indicator_true' if condition == old else 'indicator_false', old), ('assume', condition))
        target = Eq(A(DISTINCT, A(SNOC, xs, a)), Add(A(DISTINCT, xs), value))
        proof = polynomial(kernel, target, [general, branch])
        kernel.theorem(name, alls((xs, a), Imp(condition, target)), close(proof, (xs, a), (condition,)))


def derive_filter_count(kernel):
    xs, t = V('filter_list', LIST), V('filter_tail', LIST)
    h, i = V('filter_head', INDEX), V('filter_index', INDEX)
    p = V('filter_p', PREDICATE)
    indicator = Lam(i, A(IND, A(p, i)))
    result = lambda ys: Eq(total(ys, indicator), A(COUNT, ys, p))
    body = All(p, result(xs))
    base = close(polynomial(kernel, result(NIL), [ax('sum_nil', indicator), ax('filter_count_nil', p)]), (p,))
    ih = substitute(body, xs, t)
    step = polynomial(kernel, result(A(CONS, h, t)), [ax('sum_cons', indicator, h, t), ax('filter_count_cons', h, t, p), instantiate(('assume', ih), p)])
    step = close(close(step, (p,)), (h, t), (ih,))
    kernel.theorem('finite_indicator_sum_counts_filter', All(xs, body), ('list_induction', xs, h, t, body, base, step))


def certificates():
    kernel = sums.certificates()
    kernel.axioms.update(definition_axioms())
    derive_indicators(kernel)
    derive_membership(kernel)
    derive_counts(kernel)
    derive_filter_count(kernel)
    return kernel


def check(name, value):
    if not value:
        raise AssertionError(name)


def verify():
    kernel = certificates()
    check('finite_new_type_inventory', 'finite_new_type_inventory' in kernel.verified and not kernel.verified['finite_new_type_inventory'].assumptions)
    check('finite_repeated_type_inventory', 'finite_repeated_type_inventory' in kernel.verified and not kernel.verified['finite_repeated_type_inventory'].assumptions)
    check('equal_forms_equal_membership', 'equal_forms_equal_membership' in kernel.verified and not kernel.verified['equal_forms_equal_membership'].assumptions)
    check('finite_indicator_sum_counts_filter', 'finite_indicator_sum_counts_filter' in kernel.verified and not kernel.verified['finite_indicator_sum_counts_filter'].assumptions)
    check('finite_membership_append', 'finite_membership_append' in kernel.verified and not kernel.verified['finite_membership_append'].assumptions)
    check('finite_token_count_append', 'finite_token_count_append' in kernel.verified and not kernel.verified['finite_token_count_append'].assumptions)
    check('finite_type_count_append', 'finite_type_count_append' in kernel.verified and not kernel.verified['finite_type_count_append'].assumptions)
    check('indicator_conjunction_product', 'indicator_conjunction_product' in kernel.verified and not kernel.verified['indicator_conjunction_product'].assumptions)
    check('indicator_inventory_balance', 'indicator_inventory_balance' in kernel.verified and not kernel.verified['indicator_inventory_balance'].assumptions)
    return {'backend': 'Python 3 typed proof kernel', 'passed': True, 'results': [{'id': name, 'passed': True} for name in kernel.verified], 'axioms': list(kernel.axioms)}


if __name__ == '__main__':
    print(json.dumps(verify()))
