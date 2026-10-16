from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from capitulo_01 import somas_finitas as s
from capitulo_07.probabilidade_geral import *

LEX = C('lexicographic_less', FT(s.LIST, FT(s.FUNCTION, FT(s.FUNCTION, 'Prop'))))


def lex(xs, f, g):
    return A(LEX, xs, f, g)


def equal(xs, f, g):
    i = V('equal_coordinate', s.INDEX)
    return s.every(xs, Lam(i, Eq(A(f, i), A(g, i))))


def foundations():
    f, g = V('lex_f', s.FUNCTION), V('lex_g', s.FUNCTION)
    h, t = V('lex_head', s.INDEX), V('lex_tail', s.LIST)
    x, y, z = (V('order_' + v, 'R') for v in ('x', 'y', 'z'))
    return {
        'lex_nil': alls((f, g), Eq(lex(s.NIL, f, g), BOTTOM)),
        'lex_cons': alls((f, g, h, t), Eq(lex(A(s.CONS, h, t), f, g), Or(Lt(A(f, h), A(g, h)), And(Eq(A(f, h), A(g, h)), lex(t, f, g))))),
        'order_trichotomy': alls((x, y), Or(Lt(x, y), Or(Eq(x, y), Lt(y, x)))),
        'order_strict_transitive': alls((x, y, z), imps((Lt(x, y), Lt(y, z)), Lt(x, z))),
        'order_strict_irreflexive': All(x, Imp(Lt(x, x), BOTTOM)),
    }


def scalar_facts(kernel, name, x, y, z):
    if 'irreflexive' in name:
        return [ax('order_strict_irreflexive', x)]
    if 'trichotomy' in name:
        return [ax('order_trichotomy', x, y), close(symmetric(x, y, hyp(Eq(x, y))), assumptions=(Eq(x, y),))]
    eqxy, eqyz = Eq(x, y), Eq(y, z)
    variable = V('lex_scalar_replacement', 'R')
    if 'transitive' in name:
        a = ('eq_e', symmetric(x, y, hyp(eqxy)), variable, Lt(variable, z), hyp(Lt(y, z)))
        b = ('eq_e', hyp(eqyz), variable, Lt(x, variable), hyp(Lt(x, y)))
        c = ('eq_e', hyp(eqyz), variable, Eq(x, variable), hyp(eqxy))
        return [ax('order_strict_transitive', x, y, z), close(a, assumptions=(eqxy, Lt(y, z))), close(b, assumptions=(eqyz, Lt(x, y))), close(c, assumptions=(eqxy, eqyz))]
    reverse = Eq(y, x)
    symmetry = ('and_i', close(symmetric(x, y, hyp(eqxy)), assumptions=(eqxy,)), close(symmetric(y, x, hyp(reverse)), assumptions=(reverse,)))
    self_less = ('eq_e', hyp(eqxy), variable, Lt(variable, y), hyp(Lt(x, y)))
    impossible_left = close(apply(ax('order_strict_irreflexive', y), self_less), assumptions=(eqxy, Lt(x, y)))
    self_less = ('eq_e', hyp(eqxy), variable, Lt(y, variable), hyp(Lt(y, x)))
    impossible_right = close(apply(ax('order_strict_irreflexive', y), self_less), assumptions=(eqxy, Lt(y, x)))
    cycle = apply(ax('order_strict_transitive', x, y, x), hyp(Lt(x, y)), hyp(Lt(y, x)))
    asymmetric = close(apply(ax('order_strict_irreflexive', x), cycle), assumptions=(Lt(x, y), Lt(y, x)))
    return [ax('order_trichotomy', x, y), symmetry, impossible_left, impossible_right, asymmetric]


def proposition_from(kernel, target, proofs):
    formulas = [kernel.infer(p).conclusion for p in proofs]
    return apply(logical(imps(formulas, target)), *proofs)


def derive(kernel, name, relation, variables):
    xs, t = V(name + '_list', s.LIST), V(name + '_tail', s.LIST)
    head = V(name + '_head', s.INDEX)
    body = alls(variables, relation(xs))
    def rewrites(ys, is_nil):
        facts = []
        for f in variables:
            for g in variables:
                facts.append(ax('lex_nil', f, g) if is_nil else ax('lex_cons', f, g, head, t))
                i = V('equal_coordinate', s.INDEX)
                p = Lam(i, Eq(A(f, i), A(g, i)))
                facts.append(ax('every_nil', p) if is_nil else ax('every_cons', p, head, t))
        return facts
    base = s.transformed(kernel, relation(s.NIL), rewrites(s.NIL, True), lambda formula: proposition_from(kernel, normalize(formula), [('eq_i', RZERO)]))
    base = close(base, variables)
    ih = substitute(body, xs, t)
    ih_instances = []
    if len(variables) == 1:
        ih_instances.append(instantiate(hyp(ih), *variables))
    else:
        ih_instances.append(instantiate(hyp(ih), *variables))
    vals = [A(v, head) for v in variables]
    while len(vals) < 3:
        vals.append(vals[-1])
    facts = scalar_facts(kernel, name, *vals[:3]) + ih_instances
    step = s.transformed(kernel, relation(A(s.CONS, head, t)), rewrites(t, False), lambda formula: proposition_from(kernel, normalize(formula), facts))
    step = close(close(step, variables), (head, t), (ih,))
    kernel.theorem(name, All(xs, body), ('list_induction', xs, head, t, body, base, step))


def certificates():
    kernel = s.certificates()
    add_axioms(kernel, foundations())
    f, g, h = V('profile_f', s.FUNCTION), V('profile_g', s.FUNCTION), V('profile_h', s.FUNCTION)
    derive(kernel, 'lexicographic_irreflexive_general', lambda xs: Imp(lex(xs, f, f), BOTTOM), (f,))
    derive(kernel, 'lexicographic_transitive_general', lambda xs: imps((lex(xs, f, g), lex(xs, g, h)), lex(xs, f, h)), (f, g, h))
    derive(kernel, 'lexicographic_trichotomy_general', lambda xs: Or(lex(xs, f, g), Or(equal(xs, f, g), lex(xs, g, f))), (f, g))
    derive(kernel, 'lexicographic_equal_tie_general', lambda xs: Iff(equal(xs, f, g), And(Imp(lex(xs, f, g), BOTTOM), Imp(lex(xs, g, f), BOTTOM))), (f, g))
    xs = V('asym_list', s.LIST)
    fg, gf = lex(xs, f, g), lex(xs, g, f)
    cycle = apply(ref('lexicographic_transitive_general', xs, f, g, f), hyp(fg), hyp(gf))
    contra = apply(ref('lexicographic_irreflexive_general', xs, f), cycle)
    kernel.theorem('lexicographic_asymmetric_general', alls((xs, f, g), imps((fg, gf), BOTTOM)), close(contra, (xs, f, g), (fg, gf)))
    return kernel


def verify():
    kernel = certificates()
    results = []
    def check(name, condition):
        if not condition:
            raise AssertionError(name)
        results.append({'id': name, 'passed': True})
    check('lexicographic_irreflexive_general', 'lexicographic_irreflexive_general' in kernel.verified)
    check('lexicographic_transitive_general', 'lexicographic_transitive_general' in kernel.verified)
    check('lexicographic_trichotomy_general', 'lexicographic_trichotomy_general' in kernel.verified)
    check('lexicographic_equal_tie_general', 'lexicographic_equal_tie_general' in kernel.verified)
    check('lexicographic_asymmetric_general', 'lexicographic_asymmetric_general' in kernel.verified)
    record = next(row for row in kernel.records if row[0] == 'lexicographic_transitive_general')
    invalid = list(record[2])
    invalid[-1] = invalid[-2]
    check('reject_incomplete_lexicographic_induction', rejects(lambda: kernel.infer(tuple(invalid))))
    return {'passed': True, 'results': results, 'scope': 'Arbitrary finite equally indexed real profiles with strict priority order; recursive first-difference comparison, strict-order laws, total comparison and ties proved by checked list induction.', 'axioms': list(kernel.axioms)}


if __name__ == '__main__':
    print(json.dumps(verify()))
