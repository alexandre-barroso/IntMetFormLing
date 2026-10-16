from pathlib import Path
import sys
import json

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from capitulo_02 import analise_geral as a


def h(formula):
    return a.assumption('|- ' + formula)


def imp(formula, proof):
    result = ('imp_intro', '|- ' + formula, proof)
    a.infer(result)
    return result


def exponential_series_decomposition():
    f = '( n e. NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) )'
    value = f'( {f} ` k )'
    ac = h('A e. CC')
    mn = h('M e. NN')
    mn0 = a.mp(a.mm('nnnn0', {'A': 'M'}), mn)
    cond = '( T. /\\ k e. NN0 )'
    kn = ('and_elim', h(cond), 1)
    term_cc = a.mp(a.mm('eftcl', {'A': 'A', 'K': 'k'}), a.both(ac, kn))
    value_eq = a.mp(a.mm('eftval', {'F': f, 'N': 'k'}, (a.eqref(f),)), kn)
    value_cc = a.rewrite(a.eqsym(value_eq), term_cc)
    converges = a.mp(a.mm('efcllem', {'F': f}, (a.eqref(f),)), ac)
    split = a.unlift(a.mm('isumsplit', {
        'ph': 'T.', 'k': 'k', 'M': '0', 'N': 'M', 'Z': 'NN0',
        'W': '( ZZ>= ` M )', 'F': f, 'A': value
    }, (
        a.mm('nn0uz'), a.eqref('( ZZ>= ` M )'), a.lift(mn0),
        imp(cond, a.eqref(value)), imp(cond, value_cc), a.lift(converges)
    )))
    expansion = a.mp(a.mm('efval2', {'F': f}, (a.eqref(f),)), ac)
    result = a.rewrite(split, expansion)
    expected = f'|- ( exp ` A ) = ( sum_ k e. ( 0 ... ( M - 1 ) ) {value} + sum_ k e. ( ZZ>= ` M ) {value} )'
    if a.infer(result) != (expected, frozenset({'|- A e. CC', '|- M e. NN'})):
        raise a.ProofError(('exponential_series_decomposition_scope', a.infer(result)))
    return result


def exponential_series_tail_bound():
    f = '( n e. NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) )'
    g = '( n e. NN0 |-> ( ( ( abs ` A ) ^ n ) / ( ! ` n ) ) )'
    hfun = '( n e. NN0 |-> ( ( ( ( abs ` A ) ^ M ) / ( ! ` M ) ) x. ( ( 1 / ( M + 1 ) ) ^ n ) ) )'
    ac, mn, bound = h('A e. CC'), h('M e. NN'), h('( abs ` A ) <_ 1')
    result = a.unlift(a.mm('eftlub', {'ph': 'T.', 'F': f, 'G': g, 'H': hfun}, (
        a.eqref(f), a.eqref(g), a.eqref(hfun), a.lift(mn), a.lift(ac), a.lift(bound)
    )))
    expected = f'|- ( abs ` sum_ k e. ( ZZ>= ` M ) ( {f} ` k ) ) <_ ( ( ( abs ` A ) ^ M ) x. ( ( M + 1 ) / ( ( ! ` M ) x. M ) ) )'
    if a.infer(result) != (expected, frozenset({'|- A e. CC', '|- M e. NN', '|- ( abs ` A ) <_ 1'})):
        raise a.ProofError(('exponential_series_tail_bound_scope', a.infer(result)))
    return result


def certificates():
    return {
        'exponential_series_decomposition': exponential_series_decomposition(),
        'exponential_series_tail_bound': exponential_series_tail_bound()
    }


if __name__ == '__main__':
    results = []
    for name, proof in certificates().items():
        formula, hypotheses = a.infer(proof)
        results.append({'id': name, 'formula': formula, 'hypotheses': sorted(hypotheses), 'passed': True})
    print(json.dumps({'backend': 'Python/independent-Metamath-kernel', 'passed': True, 'results': results}))
