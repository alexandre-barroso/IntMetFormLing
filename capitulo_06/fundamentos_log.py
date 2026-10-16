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


def iff(proof, premise, side=0):
    result = ('iff_mp', proof, premise, side)
    a.infer(result)
    return result


def real_complex(term, proof):
    return a.unlift(a.mm('recnd', {'ph': 'T.', 'A': term}, (a.lift(proof),)))


def logarithm_series_bounds():
    qr, qn, qlt = h('A e. RR'), h('0 <_ A'), h('A < 1')
    mn = h('M e. NN')
    qc = real_complex('A', qr)
    abs_eq = a.mp(a.mm('absid'), a.both(qr, qn))
    abs_lt = a.rewrite(a.eqsym(abs_eq), qlt)
    f = '( n e. NN |-> ( ( A ^ n ) / n ) )'
    g = '( n e. NN |-> ( A ^ n ) )'
    term = '( ( A ^ k ) / k )'
    power = '( A ^ k )'
    tail = '( ZZ>= ` M )'
    mz = a.mp(a.mm('nnz', {'N': 'M'}), mn)
    mn0 = a.mp(a.mm('nnnn0', {'A': 'M'}), mn)
    muz = a.rewrite(a.mm('nnuz'), mn)
    subset = a.mp(a.mm('uzss', {'M': '1', 'N': 'M'}), muz)
    subset = a.rewrite(a.eqsym(a.mm('nnuz')), subset)

    def term_facts(kn):
        kn0 = a.mp(a.mm('nnnn0', {'A': 'k'}), kn)
        kr = a.mp(a.mm('nnre', {'A': 'k'}), kn)
        kc = a.mp(a.mm('nncn', {'A': 'k'}), kn)
        kne = a.mp(a.mm('nnne0', {'A': 'k'}), kn)
        kpos = a.mp(a.mm('rpgt0', {'A': 'k'}), a.mp(a.mm('nnrp', {'A': 'k'}), kn))
        kge1 = a.mp(a.mm('nnge1', {'A': 'k'}), kn)
        pr = a.mp(a.mm('reexpcl', {'N': 'k'}), a.both(qr, kn0))
        pc = real_complex(power, pr)
        pn = a.mp(a.mm('expge0', {'N': 'k'}), a.both(qr, kn0, qn))
        tr = a.mp(a.mm('redivcl', {'A': power, 'B': 'k'}), a.both(pr, kr, kne))
        tc = real_complex(term, tr)
        tn = a.mp(a.mm('divge0', {'A': power, 'B': 'k'}), a.both(a.both(pr, pn), a.both(kr, kpos)))
        growth = a.mp(a.mm('lemulge11', {'A': power, 'B': 'k'}), a.both(a.both(pr, kr), a.both(pn, kge1)))
        commutes = a.mp(a.mm('mulcom', {'A': power, 'B': 'k'}), a.both(pc, kc))
        growth = a.rewrite(commutes, growth)
        bound = iff(a.mp(a.mm('ledivmul', {'A': power, 'B': power, 'C': 'k'}), a.both(pr, pr, a.both(kr, kpos))), growth, 1)
        def value_at(function, body, exponent):
            substitution = a.mm('oveq2', {'A': 'n', 'B': 'k', 'C': 'A', 'F': '^'})
            if exponent:
                substitution = a.mm('oveq12d', {'ph': 'n = k', 'A': '( A ^ n )', 'B': power, 'C': 'n', 'D': 'k', 'F': '/'}, (substitution, imp('n = k', h('n = k'))))
            value = term if exponent else power
            vex = a.mm('ovex', {'A': power if exponent else 'A', 'B': 'k', 'F': '/' if exponent else '^'})
            entry = a.mm('fvmpt', {'x': 'n', 'A': 'k', 'D': 'NN', 'B': body, 'C': value, 'F': function}, (substitution, a.eqref(function), vex))
            return a.mp(entry, kn)
        fv = value_at(f, '( ( A ^ n ) / n )', True)
        gv = value_at(g, '( A ^ n )', False)
        return {'real': tr, 'complex': tc, 'nonnegative': tn, 'power_real': pr, 'bound': bound, 'f_value': fv, 'g_value': gv}

    base_condition = '( T. /\\ k e. NN )'
    base_kn = ('and_elim', h(base_condition), 1)
    base = term_facts(base_kn)
    conv = a.mp(a.mm('logtayl', {'k': 'n'}), a.both(qc, abs_lt))
    conv_domain = a.mp(a.mm('releldmi', {'A': f'seq 1 ( + , {f} )', 'B': '-u ( log ` ( 1 - A ) )', 'R': '~~>'}, (a.mm('climrel'),)), conv)
    base_value_complex = a.rewrite(a.eqsym(base['f_value']), base['complex'])
    tail_domain_equiv = a.unlift(a.mm('iserex', {'ph': 'T.', 'M': '1', 'N': 'M', 'Z': 'NN', 'F': f}, (a.mm('nnuz'), a.lift(mn), imp(base_condition, base_value_complex))))
    tail_domain = iff(tail_domain_equiv, conv_domain)
    split = a.unlift(a.mm('isumsplit', {'ph': 'T.', 'M': '1', 'N': 'M', 'Z': 'NN', 'W': tail, 'F': f, 'A': term}, (a.mm('nnuz'), a.eqref(tail), a.lift(mn), imp(base_condition, base['f_value']), imp(base_condition, base['complex']), a.lift(conv_domain))))
    log_sum = a.mp(a.mm('logtaylsum'), a.both(qc, abs_lt))
    decomposition = a.rewrite(split, a.eqsym(log_sum))

    condition = f'( T. /\\ k e. {tail} )'
    km = ('and_elim', h(condition), 1)
    kn = a.mm('sselii', {'A': tail, 'B': 'NN', 'C': 'k'}, (subset, km))
    facts = term_facts(kn)
    geometric_limit = a.unlift(a.mm('geolim2', {'ph': 'T.', 'F': g}, (a.lift(qc), a.lift(abs_lt), a.lift(mn0), imp(condition, facts['g_value']))))
    geometric_domain = a.mp(a.mm('releldmi', {'A': f'seq M ( + , {g} )', 'B': '( ( A ^ M ) / ( 1 - A ) )', 'R': '~~>'}, (a.mm('climrel'),)), geometric_limit)
    common = (a.eqref(tail), a.lift(mz), imp(condition, facts['f_value']), imp(condition, facts['real']), a.lift(tail_domain))
    lower = a.unlift(a.mm('isumge0', {'ph': 'T.', 'Z': tail, 'F': f, 'A': term}, common + (imp(condition, facts['nonnegative']),)))
    comparison = a.unlift(a.mm('isumle', {'ph': 'T.', 'Z': tail, 'F': f, 'G': g, 'A': term, 'B': power}, (
        a.eqref(tail), a.lift(mz), imp(condition, facts['f_value']), imp(condition, facts['real']),
        imp(condition, facts['g_value']), imp(condition, facts['power_real']), imp(condition, facts['bound']),
        a.lift(tail_domain), a.lift(geometric_domain)
    )))
    geometric_isum_limit = a.unlift(a.mm('isumclim2', {'ph': 'T.', 'Z': tail, 'F': g, 'A': power}, (
        a.eqref(tail), a.lift(mz), imp(condition, facts['g_value']),
        imp(condition, real_complex(power, facts['power_real'])), a.lift(geometric_domain)
    )))
    geometric_sum = a.mp(a.mm('climuni', {'F': f'seq M ( + , {g} )', 'A': f'sum_ k e. {tail} {power}', 'B': '( ( A ^ M ) / ( 1 - A ) )'}), a.both(geometric_isum_limit, geometric_limit))
    upper = a.rewrite(geometric_sum, comparison)
    results = {'logarithm_series_decomposition': decomposition, 'logarithm_series_tail_nonnegative': lower, 'logarithm_series_tail_bound': upper}
    hypotheses = frozenset({'|- A e. RR', '|- 0 <_ A', '|- A < 1', '|- M e. NN'})
    expected = {
        'logarithm_series_decomposition': f'|- -u ( log ` ( 1 - A ) ) = ( sum_ k e. ( 1 ... ( M - 1 ) ) {term} + sum_ k e. {tail} {term} )',
        'logarithm_series_tail_nonnegative': f'|- 0 <_ sum_ k e. {tail} {term}',
        'logarithm_series_tail_bound': f'|- sum_ k e. {tail} {term} <_ ( ( A ^ M ) / ( 1 - A ) )'
    }
    for name, proof in results.items():
        if a.infer(proof) != (expected[name], hypotheses):
            raise a.ProofError(('logarithm_series_scope', name, a.infer(proof)))
    return results


if __name__ == '__main__':
    results = []
    for name, proof in logarithm_series_bounds().items():
        formula, hypotheses = a.infer(proof)
        results.append({'id': name, 'formula': formula, 'hypotheses': sorted(hypotheses), 'passed': True})
    print(json.dumps({'backend': 'Python/independent-Metamath-kernel', 'passed': True, 'results': results}))
