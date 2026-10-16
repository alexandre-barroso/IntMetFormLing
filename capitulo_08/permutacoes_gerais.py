from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from capitulo_01 import somas_finitas as s
from capitulo_07.probabilidade_geral import *

APPEND = C('list_append', FT(s.LIST, FT(s.LIST, s.LIST)))
SELECTION = 'FiniteOccurrenceSelection'
SELECTIONS = ('List', SELECTION)
NIL = C('list_nil', SELECTIONS)
CONS = C('list_cons', FT(SELECTION, FT(SELECTIONS, SELECTIONS)))
VALUE = C('selected_occurrence', FT(SELECTION, s.INDEX))
PREFIX = C('selection_prefix', FT(SELECTION, s.LIST))
SUFFIX = C('selection_suffix', FT(SELECTION, s.LIST))
SOURCE = C('permutation_source', FT(SELECTIONS, s.LIST))
TARGET = C('permutation_target', FT(SELECTIONS, s.LIST))
VALID = C('valid_occurrence_bijection', FT(SELECTIONS, 'Prop'))
MAKE = C('occurrence_selection', FT(s.INDEX, FT(s.LIST, FT(s.LIST, SELECTION))))
PAIRING = C('finite_occurrence_pairing', FT(s.LIST, FT(s.LIST, 'Prop')))


def append(a, b):
    return A(APPEND, a, b)


def foundations():
    xs, ys = V('append_xs', s.LIST), V('append_ys', s.LIST)
    h = V('append_head', s.INDEX)
    op, tail = V('selection', SELECTION), V('selection_tail', SELECTIONS)
    cons = A(CONS, op, tail)
    return {
        'append_nil': All(ys, Eq(append(s.NIL, ys), ys)),
        'append_cons': alls((h, xs, ys), Eq(append(A(s.CONS, h, xs), ys), A(s.CONS, h, append(xs, ys)))),
        'permutation_source_nil': Eq(A(SOURCE, NIL), s.NIL),
        'permutation_target_nil': Eq(A(TARGET, NIL), s.NIL),
        'permutation_valid_nil': Eq(A(VALID, NIL), s.TRUE),
        'permutation_source_cons': alls((op, tail), Eq(A(SOURCE, cons), A(s.CONS, A(VALUE, op), A(SOURCE, tail)))),
        'permutation_target_cons': alls((op, tail), Eq(A(TARGET, cons), append(A(PREFIX, op), A(s.CONS, A(VALUE, op), A(SUFFIX, op))))),
        'permutation_valid_cons': alls((op, tail), Eq(A(VALID, cons), And(A(VALID, tail), Eq(A(TARGET, tail), append(A(PREFIX, op), A(SUFFIX, op)))))),
    }


def derive_append(kernel):
    xs, tail, head = V('append_list', s.LIST), V('append_tail', s.LIST), V('append_index', s.INDEX)
    ys, f = V('append_right', s.LIST), V('append_function', s.FUNCTION)
    result = lambda zs: Eq(s.total(append(zs, ys), f), Add(s.total(zs, f), s.total(ys, f)))
    body = alls((ys, f), result(xs))
    base = s.polynomial(kernel, result(s.NIL), [ax('append_nil', ys), ax('sum_nil', f)])
    base = close(base, (ys, f))
    ih = substitute(body, xs, tail)
    step = s.polynomial(kernel, result(A(s.CONS, head, tail)), [ax('append_cons', head, tail, ys), ax('sum_cons', f, head, append(tail, ys)), ax('sum_cons', f, head, tail), instantiate(hyp(ih), ys, f)])
    step = close(close(step, (ys, f)), (head, tail), (ih,))
    kernel.theorem('finite_sum_append_general', All(xs, body), ('list_induction', xs, head, tail, body, base, step))
    before, after, value = V('insertion_prefix', s.LIST), V('insertion_suffix', s.LIST), V('insertion_value', s.INDEX)
    inserted = append(before, A(s.CONS, value, after))
    deleted = append(before, after)
    result = Eq(s.total(inserted, f), Add(A(f, value), s.total(deleted, f)))
    proof = s.polynomial(kernel, result, [ref('finite_sum_append_general', before, A(s.CONS, value, after), f), ref('finite_sum_append_general', before, after, f), ax('sum_cons', f, value, after)])
    kernel.theorem('finite_sum_selected_occurrence_general', alls((before, after, value, f), result), close(proof, (before, after, value, f)))


def derive_permutation(kernel):
    xs, tail, op = V('bijection_code', SELECTIONS), V('bijection_tail', SELECTIONS), V('bijection_selection', SELECTION)
    f = V('bijection_values', s.FUNCTION)
    result = lambda zs: Imp(A(VALID, zs), Eq(s.total(A(SOURCE, zs), f), s.total(A(TARGET, zs), f)))
    body = All(f, result(xs))
    base = s.polynomial(kernel, result(NIL)[2], [ax('permutation_source_nil'), ax('permutation_target_nil')])
    base = close(base, (f,), (A(VALID, NIL),))
    ih = substitute(body, xs, tail)
    cons = A(CONS, op, tail)
    valid = A(VALID, cons)
    split = rewrite(kernel, hyp(valid), ax('permutation_valid_cons', op, tail))
    tail_eq = apply(instantiate(hyp(ih), f), ('and_l', split))
    source = A(SOURCE, cons)
    target = A(TARGET, cons)
    v, pre, suf = A(VALUE, op), A(PREFIX, op), A(SUFFIX, op)
    equation = Eq(s.total(source, f), s.total(target, f))
    step = s.polynomial(kernel, equation, [ax('permutation_source_cons', op, tail), ax('permutation_target_cons', op, tail), ax('sum_cons', f, v, A(SOURCE, tail)), tail_eq, ('and_r', split), ref('finite_sum_selected_occurrence_general', pre, suf, v, f)])
    step = close(close(step, (f,), (valid,)), (op, tail), (ih,))
    kernel.theorem('finite_bijection_sum_invariance', All(xs, body), ('list_induction', xs, op, tail, body, base, step))
    i = V('bijection_count_index', s.INDEX)
    ones = Lam(i, RONE)
    valid = A(VALID, xs)
    numerator = apply(ref('finite_bijection_sum_invariance', xs, f), hyp(valid))
    denominator = apply(ref('finite_bijection_sum_invariance', xs, ones), hyp(valid))
    source_mean = Div(s.total(A(SOURCE, xs), f), s.total(A(SOURCE, xs), ones))
    target_mean = Div(s.total(A(TARGET, xs), f), s.total(A(TARGET, xs), ones))
    equal_means = s.transformed(kernel, Eq(source_mean, target_mean), [numerator, denominator], lambda q: ('eq_i', q[1]))
    count_positive = Lt(RZERO, s.total(A(SOURCE, xs), ones))
    formula = alls((xs, f), imps((valid, count_positive), Eq(source_mean, target_mean)))
    kernel.theorem('cbow_finite_bijection_mean_invariance', formula, close(equal_means, (xs, f), (valid, count_positive)))


def derive_representation(kernel):
    xs, ys, pre, suf = (V('pairing_' + name, s.LIST) for name in ('source', 'target', 'prefix', 'suffix'))
    h = V('pairing_head', s.INDEX)
    choice = A(MAKE, h, pre, suf)
    decomposition = Ex(pre, Ex(suf, And(Eq(ys, append(pre, A(s.CONS, h, suf))), A(PAIRING, xs, append(pre, suf)))))
    add_axioms(kernel, {
        'selection_value': alls((h, pre, suf), Eq(A(VALUE, choice), h)),
        'selection_prefix': alls((h, pre, suf), Eq(A(PREFIX, choice), pre)),
        'selection_suffix': alls((h, pre, suf), Eq(A(SUFFIX, choice), suf)),
        'finite_pairing_empty': All(ys, Iff(A(PAIRING, s.NIL, ys), Eq(ys, s.NIL))),
        'finite_pairing_cons': alls((h, xs, ys), Iff(A(PAIRING, A(s.CONS, h, xs), ys), decomposition)),
    })
    tail = V('pairing_tail', s.LIST)
    code = V('pairing_code', SELECTIONS)
    def represents(code, left, right):
        return And(A(VALID, code), And(Eq(A(SOURCE, code), left), Eq(A(TARGET, code), right)))
    def existence(left, right):
        return Ex(code, represents(code, left, right))
    body = All(ys, Imp(A(PAIRING, xs, ys), existence(xs, ys)))
    base_hyp = A(PAIRING, s.NIL, ys)
    target_nil = apply(('and_l', ax('finite_pairing_empty', ys)), hyp(base_hyp))
    valid_nil = rewrite(kernel, ('eq_i', RZERO), ax('permutation_valid_nil'), True)
    target_eq = eq_trans(A(TARGET, NIL), s.NIL, ys, ax('permutation_target_nil'), symmetric(ys, s.NIL, target_nil))
    base_rep = ('and_i', valid_nil, ('and_i', ax('permutation_source_nil'), target_eq))
    base = ('ex_i', existence(s.NIL, ys), NIL, base_rep)
    base = close(base, (ys,), (base_hyp,))
    ih = substitute(body, xs, tail)
    pair = A(PAIRING, A(s.CONS, h, tail), ys)
    split = apply(('and_l', ax('finite_pairing_cons', h, tail, ys)), hyp(pair))
    outer = kernel.infer(split).conclusion
    prefix_var = V('chosen_prefix', s.LIST)
    inner = substitute(outer[2], outer[1], prefix_var)
    suffix_var = V('chosen_suffix', s.LIST)
    payload = substitute(inner[2], inner[1], suffix_var)
    remaining = append(prefix_var, suffix_var)
    rest_exists = apply(instantiate(hyp(ih), remaining), ('and_r', hyp(payload)))
    rest_code = V('remaining_pairing_code', SELECTIONS)
    rest_payload = represents(rest_code, tail, remaining)
    instruction = A(MAKE, h, prefix_var, suffix_var)
    newcode = A(CONS, instruction, rest_code)
    definitions = [ax('selection_value', h, prefix_var, suffix_var), ax('selection_prefix', h, prefix_var, suffix_var), ax('selection_suffix', h, prefix_var, suffix_var)]
    valid = s.transformed(kernel, A(VALID, newcode), [ax('permutation_valid_cons', instruction, rest_code)] + definitions, lambda _: ('and_i', ('and_l', hyp(rest_payload)), ('and_r', ('and_r', hyp(rest_payload)))))
    source_eq = s.transformed(kernel, Eq(A(SOURCE, newcode), A(s.CONS, h, tail)), [ax('permutation_source_cons', instruction, rest_code)] + definitions + [('and_l', ('and_r', hyp(rest_payload)))], lambda q: ('eq_i', q[1]))
    target_eq = s.transformed(kernel, Eq(A(TARGET, newcode), ys), [ax('permutation_target_cons', instruction, rest_code)] + definitions, lambda _: symmetric(ys, append(prefix_var, A(s.CONS, h, suffix_var)), ('and_l', hyp(payload))))
    constructed = ('ex_i', existence(A(s.CONS, h, tail), ys), newcode, ('and_i', valid, ('and_i', source_eq, target_eq)))
    constructed = ('ex_e', rest_exists, rest_code, constructed)
    constructed = ('ex_e', hyp(inner), suffix_var, constructed)
    constructed = ('ex_e', split, prefix_var, constructed)
    step = close(close(constructed, (ys,), (pair,)), (h, tail), (ih,))
    kernel.theorem('finite_bijection_encoding_complete', All(xs, body), ('list_induction', xs, h, tail, body, base, step))
    assumption = A(PAIRING, xs, ys)
    exists = apply(ref('finite_bijection_encoding_complete', xs, ys), hyp(assumption))
    chosen = V('arbitrary_pairing_code', SELECTIONS)
    representation = represents(chosen, xs, ys)
    f = V('arbitrary_coordinate_function', s.FUNCTION)
    invariant = apply(ref('finite_bijection_sum_invariance', chosen, f), ('and_l', hyp(representation)))
    invariant = rewrite(kernel, invariant, ('and_l', ('and_r', hyp(representation))))
    invariant = rewrite(kernel, invariant, ('and_r', ('and_r', hyp(representation))))
    result = ('ex_e', exists, chosen, invariant)
    statement = alls((xs, ys, f), Imp(assumption, Eq(s.total(xs, f), s.total(ys, f))))
    kernel.theorem('arbitrary_finite_bijection_sum_invariance', statement, close(result, (xs, ys, f), (assumption,)))
    i = V('arbitrary_mean_index', s.INDEX)
    one = Lam(i, RONE)
    num = apply(ref('arbitrary_finite_bijection_sum_invariance', xs, ys, f), hyp(assumption))
    den = apply(ref('arbitrary_finite_bijection_sum_invariance', xs, ys, one), hyp(assumption))
    target = Eq(Div(s.total(xs, f), s.total(xs, one)), Div(s.total(ys, f), s.total(ys, one)))
    mean_eq = s.transformed(kernel, target, [num, den], lambda q: ('eq_i', q[1]))
    count_positive = Lt(RZERO, s.total(xs, one))
    kernel.theorem('cbow_arbitrary_finite_bijection_mean', alls((xs, ys, f), imps((assumption, count_positive), target)), close(mean_eq, (xs, ys, f), (assumption, count_positive)))


def encode_bijection(source, target):
    if len(source) != len(target) or len(set(source)) != len(source) or set(source) != set(target):
        raise ValueError('A bijection of distinct occurrence labels is required')
    if not source:
        return []
    position = target.index(source[0])
    before, after = target[:position], target[position + 1:]
    return [(source[0], tuple(before), tuple(after))] + encode_bijection(source[1:], before + after)


def decode_bijection(code):
    if not code:
        return (), ()
    value, before, after = code[0]
    source, target = decode_bijection(code[1:])
    if target != before + after:
        raise ValueError('Invalid recursive occurrence correspondence')
    return (value,) + source, before + (value,) + after


def certificates():
    kernel = s.certificates()
    add_axioms(kernel, foundations())
    derive_append(kernel)
    derive_permutation(kernel)
    derive_representation(kernel)
    return kernel


def verify():
    kernel = certificates()
    results = []
    def check(name, condition):
        if not condition:
            raise AssertionError(name)
        results.append({'id': name, 'passed': True})
    check('finite_bijection_encoding_complete', 'finite_bijection_encoding_complete' in kernel.verified)
    check('cbow_arbitrary_finite_bijection_mean', 'cbow_arbitrary_finite_bijection_mean' in kernel.verified)
    check('finite_bijection_sum_invariance', 'finite_bijection_sum_invariance' in kernel.verified)
    check('cbow_finite_bijection_mean_invariance', 'cbow_finite_bijection_mean_invariance' in kernel.verified)
    bad = list(next(row for row in kernel.records if row[0] == 'finite_bijection_sum_invariance')[2])
    bad[-1] = bad[-2]
    check('reject_missing_bijection_induction_step', rejects(lambda: kernel.infer(tuple(bad))))
    check('reject_duplicated_occurrence', rejects(lambda: encode_bijection((0, 1), (0, 0))))
    return {'passed': True, 'results': results, 'scope': 'Arbitrary finite occurrence bijections encoded by recursive selection of the image of the first remaining occurrence; all prefixes, suffixes, list lengths and real coordinate functions are universally quantified. Selection removes exactly one occurrence and recurses on the restricted bijection; no permutation is sampled.'}


if __name__ == '__main__':
    print(json.dumps(verify()))
