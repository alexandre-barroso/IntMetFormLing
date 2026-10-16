from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from capitulo_01 import somas_finitas as s
from capitulo_07.probabilidade_geral import *

CHAR = 'Character'
WORD = ('List', CHAR)
OP = 'BoundaryOperation'
OPS = ('List', OP)
EMPTY = C('list_nil', WORD)
NIL = C('list_nil', OPS)
CONS = C('list_cons', FT(OP, FT(OPS, OPS)))
PREPEND = C('list_cons', FT(CHAR, FT(WORD, WORD)))
MARKER = C('boundary_marker', CHAR)
INSERT = C('insert_boundary', OP)
KEEP = C('keep_character', FT(CHAR, OP))
SOURCE = C('boundary_source', FT(OPS, WORD))
TARGET = C('boundary_target', FT(OPS, WORD))
ERASE = C('erase_boundaries', FT(WORD, WORD))
PREFIX = C('filtered_prefix', FT(CHAR, FT(WORD, WORD)))


def invariant(ops):
    return Eq(A(ERASE, A(SOURCE, ops)), A(ERASE, A(TARGET, ops)))


def foundations():
    c, op, tail, word = V('boundary_character', CHAR), V('boundary_operation', OP), V('boundary_tail', OPS), V('boundary_word', WORD)
    return {
        'operation_cases': All(op, Or(Eq(op, INSERT), Ex(c, Eq(op, A(KEEP, c))))),
        'source_nil': Eq(A(SOURCE, NIL), EMPTY),
        'target_nil': Eq(A(TARGET, NIL), EMPTY),
        'source_insert': All(tail, Eq(A(SOURCE, A(CONS, INSERT, tail)), A(SOURCE, tail))),
        'target_insert': All(tail, Eq(A(TARGET, A(CONS, INSERT, tail)), A(PREPEND, MARKER, A(TARGET, tail)))),
        'source_keep': alls((c, tail), Eq(A(SOURCE, A(CONS, A(KEEP, c), tail)), A(PREPEND, c, A(SOURCE, tail)))),
        'target_keep': alls((c, tail), Eq(A(TARGET, A(CONS, A(KEEP, c), tail)), A(PREPEND, c, A(TARGET, tail)))),
        'erase_nil': Eq(A(ERASE, EMPTY), EMPTY),
        'erase_cons': alls((c, word), Eq(A(ERASE, A(PREPEND, c, word)), A(PREFIX, c, A(ERASE, word)))),
        'erase_marker': All(word, Eq(A(ERASE, A(PREPEND, MARKER, word)), A(ERASE, word))),
    }


def certificates():
    kernel = Kernel(foundations())
    xs, tail, op, c = V('operations', OPS), V('operations_tail', OPS), V('operation_head', OP), V('kept_character', CHAR)
    body = invariant(xs)
    base = s.transformed(kernel, invariant(NIL), [ax('source_nil'), ax('target_nil'), ax('erase_nil')], lambda q: ('eq_i', q[1]))
    ih = invariant(tail)
    keep = A(KEEP, c)
    branch_keep = s.transformed(kernel, invariant(A(CONS, keep, tail)), [ax('source_keep', c, tail), ax('target_keep', c, tail), ax('erase_cons', c, A(SOURCE, tail)), ax('erase_cons', c, A(TARGET, tail)), hyp(ih)], lambda q: ('eq_i', q[1]))
    branch_insert = s.transformed(kernel, invariant(A(CONS, INSERT, tail)), [ax('source_insert', tail), ax('target_insert', tail), ax('erase_marker', A(TARGET, tail))], lambda q: hyp(ih))
    variable = V('operation_replacement', OP)
    pattern = invariant(A(CONS, variable, tail))
    insert_hyp = Eq(op, INSERT)
    branch_insert = ('eq_e', symmetric(op, INSERT, hyp(insert_hyp)), variable, pattern, branch_insert)
    keep_hyp = Eq(op, keep)
    branch_keep = ('eq_e', symmetric(op, keep, hyp(keep_hyp)), variable, pattern, branch_keep)
    existence = kernel.infer(ax('operation_cases', op)).conclusion[2]
    keep_case = ('ex_e', hyp(existence), c, branch_keep)
    step = ('or_e', ax('operation_cases', op), branch_insert, keep_case)
    step = close(step, (op, tail), (ih,))
    kernel.theorem('boundary_insertion_preserves_erasure_general', All(xs, body), ('list_induction', xs, op, tail, body, base, step))
    return kernel


def verify():
    kernel = certificates()
    results = []
    def check(name, condition):
        if not condition:
            raise AssertionError(name)
        results.append({'id': name, 'passed': True})
    check('boundary_insertion_preserves_erasure_general', 'boundary_insertion_preserves_erasure_general' in kernel.verified)
    proof = list(kernel.records[-1][2])
    proof[-1] = proof[-2]
    check('reject_omitted_boundary_constructor', rejects(lambda: kernel.infer(tuple(proof))))
    check('canonical_segmentation_erasure_counterexample', 'Cylindrically'.replace('-', '') != 'Cylinder-ical-ly'.replace('-', ''))
    return {'passed': True, 'results': results, 'scope': 'Every finite sequence of the keep-character and insert-boundary constructors; arbitrary characters include existing boundaries. Source and target erase to exactly the same sequence.', 'axioms': list(kernel.axioms)}


if __name__ == '__main__':
    print(json.dumps(verify()))
