import json
import analise_geral as a
from triplice import as_complex

def h(formula):
    return a.assumption('|- ' + formula)

def values_real():
    context = '|- ( T. /\\ x e. A )'
    member = ('and_elim', a.assumption(context), 1)
    result = ('rall_elim', h('A. x e. A ( F ` x ) e. RR'), member)
    proof = ('imp_intro', context, result)
    a.infer(proof)
    return proof

def scale_integrable():
    return a.unlift(a.mm('iblmulc2', {'ph': 'T.', 'x': 'x', 'A': 'A', 'B': '( F ` x )', 'C': 'C', 'V': 'RR'}, (a.lift(as_complex('C', h('C e. RR'))), values_real(), a.lift(h('( x e. A |-> ( F ` x ) ) e. L^1')))))

def scale_integral():
    return a.unlift(a.mm('itgmulc2', {'ph': 'T.', 'x': 'x', 'A': 'A', 'B': '( F ` x )', 'C': 'C', 'V': 'RR'}, (a.lift(as_complex('C', h('C e. RR'))), values_real(), a.lift(h('( x e. A |-> ( F ` x ) ) e. L^1')))))

def zero_integrable():
    zero = a.mp(a.mm('ibl0', {'A': 'A'}), h('A e. dom vol'))
    return a.rewrite(a.mm('fconstmpt', {'A': 'A', 'B': '0', 'x': 'x'}), zero)

def checks():
    candidates = [('profile_integrable_scaling', scale_integrable(), '|- ( x e. A |-> ( C x. ( F ` x ) ) ) e. L^1', {'|- C e. RR', '|- A. x e. A ( F ` x ) e. RR', '|- ( x e. A |-> ( F ` x ) ) e. L^1'}), ('profile_integral_scaling', scale_integral(), '|- ( C x. S. A ( F ` x ) _d x ) = S. A ( C x. ( F ` x ) ) _d x', {'|- C e. RR', '|- A. x e. A ( F ` x ) e. RR', '|- ( x e. A |-> ( F ` x ) ) e. L^1'}), ('profile_zero_integrable', zero_integrable(), '|- ( x e. A |-> 0 ) e. L^1', {'|- A e. dom vol'}), ('profile_zero_integral', a.mm('itgz', {'A': 'A', 'x': 'x'}), '|- S. A 0 _d x = 0', set())]
    results = []
    for name, proof, formula, premises in candidates:
        observed = a.infer(proof)
        if observed != (formula, frozenset(premises)):
            raise a.ProofError((name, observed, formula, premises))
        results.append({'id': name, 'proof': proof, 'formula': formula, 'assumptions': sorted(premises), 'passed': True})
    return results
if __name__ == '__main__':
    results = checks()
    print(json.dumps({'backend': 'Python Metamath kernel', 'passed': True, 'results': [{k: v for k, v in row.items() if k != 'proof'} for row in results]}))
