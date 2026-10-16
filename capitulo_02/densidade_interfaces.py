import json
import analise_geral as a

def h(formula):
    return a.assumption('|- ' + formula)

def implies(formula, proof):
    result = ('imp_intro', '|- ' + formula, proof)
    a.infer(result)
    return result

def point_condition(domain, condition, measurable):
    context = '( T. /\\ x e. ' + domain + ' )'
    member = ('and_elim', h(context), 1)
    subset = a.mp(a.mm('mblss', {'A': domain}), measurable)
    real_member = a.mp(a.mp(a.mm('ssel', {'A': domain, 'B': 'RR', 'C': 'x'}), subset), member)
    proof = ('rall_elim', h('A. x e. RR ' + condition), real_member)
    a.infer(proof)
    return implies(context, proof)

def real_point_condition():
    context = '( T. /\\ x e. RR )'
    proof = ('rall_elim', h('A. x e. RR ( F ` x ) e. RR'), ('and_elim', h(context), 1))
    a.infer(proof)
    return implies(context, proof)

def restriction(domain, measurable):
    subset = a.mp(a.mm('mblss', {'A': domain}), measurable)
    proof = a.unlift(a.mm('iblss', {'ph': 'T.', 'x': 'x', 'A': domain, 'B': 'RR', 'C': '( F ` x )', 'V': 'RR'}, (a.lift(subset), a.lift(measurable), real_point_condition(), a.lift(h('( x e. RR |-> ( F ` x ) ) e. L^1')))))
    return proof

def nonnegative(domain, measurable):
    proof = a.unlift(a.mm('itgge0', {'ph': 'T.', 'x': 'x', 'A': domain, 'B': '( F ` x )'}, (a.lift(restriction(domain, measurable)), point_condition(domain, '( F ` x ) e. RR', measurable), point_condition(domain, '0 <_ ( F ` x )', measurable))))
    return proof

def pair_union(left='A', right='B', left_measurable=None, right_measurable=None, disjoint=None):
    lm = h(left + ' e. dom vol') if left_measurable is None else left_measurable
    rm = h(right + ' e. dom vol') if right_measurable is None else right_measurable
    dj = h('( ' + left + ' i^i ' + right + ' ) = (/)') if disjoint is None else disjoint
    union = '( ' + left + ' u. ' + right + ' )'
    um = a.mp(a.mm('unmbl', {'A': left, 'B': right}), a.both(lm, rm))
    outer = a.rewrite(a.eqsym(dj), a.mm('ovol0'))
    proof = a.unlift(a.mm('itgsplit', {'ph': 'T.', 'x': 'x', 'A': left, 'B': right, 'U': union, 'C': '( F ` x )', 'V': 'RR'}, (a.lift(outer), a.lift(a.eqref(union)), point_condition(union, '( F ` x ) e. RR', um), a.lift(restriction(left, lm)), a.lift(restriction(right, rm)))))
    return proof

def complement_partition():
    am = h('A e. dom vol')
    complement = '( RR \\ A )'
    cm = a.mp(a.mm('cmmbl', {'A': 'A'}), am)
    dj = a.mm('disjdif', {'A': 'A', 'B': 'RR'})
    pair = pair_union('A', complement, am, cm, dj)
    subset = a.mp(a.mm('mblss', {'A': 'A'}), am)
    partition = ('iff_mp', a.mm('undif', {'A': 'A', 'B': 'RR'}), subset, 0)
    a.infer(partition)
    result = a.rewrite(partition, pair)
    return result

def checks():
    candidates = [('density_restriction_integrable', restriction('A', h('A e. dom vol')), '|- ( x e. A |-> ( F ` x ) ) e. L^1', {'|- A e. dom vol', '|- A. x e. RR ( F ` x ) e. RR', '|- ( x e. RR |-> ( F ` x ) ) e. L^1'}), ('density_event_nonnegative', nonnegative('A', h('A e. dom vol')), '|- 0 <_ S. A ( F ` x ) _d x', {'|- A e. dom vol', '|- A. x e. RR ( F ` x ) e. RR', '|- A. x e. RR 0 <_ ( F ` x )', '|- ( x e. RR |-> ( F ` x ) ) e. L^1'}), ('density_disjoint_union', pair_union(), '|- S. ( A u. B ) ( F ` x ) _d x = ( S. A ( F ` x ) _d x + S. B ( F ` x ) _d x )', {'|- A e. dom vol', '|- B e. dom vol', '|- ( A i^i B ) = (/)', '|- A. x e. RR ( F ` x ) e. RR', '|- ( x e. RR |-> ( F ` x ) ) e. L^1'}), ('density_complement_partition', complement_partition(), '|- S. RR ( F ` x ) _d x = ( S. A ( F ` x ) _d x + S. ( RR \\ A ) ( F ` x ) _d x )', {'|- A e. dom vol', '|- A. x e. RR ( F ` x ) e. RR', '|- ( x e. RR |-> ( F ` x ) ) e. L^1'}), ('density_empty_event', a.mm('itg0', {'x': 'x', 'A': '( F ` x )'}), '|- S. (/) ( F ` x ) _d x = 0', set()), ('density_sigma_empty', a.mm('0mbl'), '|- (/) e. dom vol', set()), ('density_sigma_universe', a.mm('rembl'), '|- RR e. dom vol', set()), ('density_sigma_union', a.mp(a.mm('unmbl'), a.both(h('A e. dom vol'), h('B e. dom vol'))), '|- ( A u. B ) e. dom vol', {'|- A e. dom vol', '|- B e. dom vol'}), ('density_sigma_difference', a.mp(a.mm('difmbl'), a.both(h('A e. dom vol'), h('B e. dom vol'))), '|- ( A \\ B ) e. dom vol', {'|- A e. dom vol', '|- B e. dom vol'})]
    results = []
    for name, proof, expected, premises in candidates:
        observed = a.infer(proof)
        if observed != (expected, frozenset(premises)):
            raise a.ProofError((name, observed, expected, premises))
        results.append({'id': name, 'proof': proof, 'formula': expected, 'assumptions': sorted(premises), 'passed': True})
    return results
if __name__ == '__main__':
    result = checks()
    print(json.dumps({'backend': 'Python Metamath kernel', 'passed': True, 'results': [{k: v for k, v in r.items() if k != 'proof'} for r in result]}))
