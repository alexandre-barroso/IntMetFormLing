from pathlib import Path
import sys
import json

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'capitulo_02'))
import analise_geral as a
from triplice import iff, part, h, as_complex


def real_add(left, right, lp, rp):
    return a.mp(a.mm('readdcl', {'A': left, 'B': right}), a.both(lp, rp))


def real_complex(term, proof):
    return as_complex(term, proof)


def two_quarters():
    half = '( _pi / 2 )'
    hc = real_complex(half, a.mm('halfpire'))
    split = a.mp(a.mm('2halves', {'A': half}), hc)
    quarter = a.mp(a.mm('divdiv1', {'A': '_pi', 'B': '2', 'C': '2'}), a.both(real_complex('_pi', a.mm('pire')), a.mm('2cnne0'), a.mm('2cnne0')))
    quarter = a.rewrite(a.mm('2t2e4'), quarter)
    return a.rewrite(quarter, split)


def arctangent_addition_one():
    ar, br = h('A e. RR'), h('B e. RR')
    apos, bpos = h('0 < A'), h('0 < B')
    alt, blt = h('A < 1'), h('B < 1')
    product_not_one = h('( A x. B ) =/= 1')
    quotient_one = h('( ( A + B ) / ( 1 - ( A x. B ) ) ) = 1')
    at, bt = '( arctan ` A )', '( arctan ` B )'
    atr = a.mp(a.mm('atanrecl', {'A': 'A'}), ar)
    btr = a.mp(a.mm('atanrecl', {'A': 'B'}), br)
    atc, btc = real_complex(at, atr), real_complex(bt, btr)
    ap = iff(a.mp(a.mm('atanord', {'A': '0', 'B': 'A'}), a.both(a.mm('0re'), ar)), apos)
    bp = iff(a.mp(a.mm('atanord', {'A': '0', 'B': 'B'}), a.both(a.mm('0re'), br)), bpos)
    ap, bp = a.rewrite(a.mm('atan0'), ap), a.rewrite(a.mm('atan0'), bp)
    aq = iff(a.mp(a.mm('atanord', {'A': 'A', 'B': '1'}), a.both(ar, a.mm('1re'))), alt)
    bq = iff(a.mp(a.mm('atanord', {'A': 'B', 'B': '1'}), a.both(br, a.mm('1re'))), blt)
    aq, bq = a.rewrite(a.mm('atan1'), aq), a.rewrite(a.mm('atan1'), bq)
    q = '( _pi / 4 )'
    qr = a.rewrite(a.mm('atan1'), a.mp(a.mm('atanrecl', {'A': '1'}), a.mm('1re')))
    sum_term = '( ' + at + ' + ' + bt + ' )'
    sum_real = real_add(at, bt, atr, btr)
    sum_positive = a.mp(a.mp(a.mm('lt2add', {'A': '0', 'B': '0', 'C': at, 'D': bt}), a.both(a.both(a.mm('0re'), a.mm('0re')), a.both(atr, btr))), a.both(ap, bp))
    zero_plus_zero = a.mm('00id')
    sum_positive = a.rewrite(zero_plus_zero, sum_positive)
    sum_upper = a.mp(a.mp(a.mm('lt2add', {'A': at, 'B': bt, 'C': q, 'D': q}), a.both(a.both(atr, btr), a.both(qr, qr))), a.both(aq, bq))
    sum_upper = a.rewrite(two_quarters(), sum_upper)
    half = '( _pi / 2 )'
    half_positive = a.mp(a.mm('rphalfcl', {'A': '_pi'}), a.mm('pirp'))
    half_positive = a.mp(a.mm('rpgt0', {'A': half}), half_positive)
    negative_lower = iff(a.mp(a.mm('lt0neg2', {'A': half}), a.mm('halfpire')), half_positive)
    sum_lower = a.mp(a.mp(a.mm('lttr', {'A': '-u ' + half, 'B': '0', 'C': sum_term}), a.both(a.mm('neghalfpire'), a.mm('0re'), sum_real)), a.both(negative_lower, sum_positive))
    interval = '( -u ( _pi / 2 ) (,) ( _pi / 2 ) )'
    right_rx = a.mp(a.mm('rexr', {'A': half}), a.mm('halfpire'))
    member = iff(a.mp(a.mm('elioo2', {'A': '-u ' + half, 'B': half, 'C': sum_term}), a.both(a.mm('neghalfpirx'), right_rx)), a.both(sum_real, sum_lower, sum_upper), 1)
    cos_nonzero = []
    tangents = []
    for original, real, term, realterm, complexterm in [('A', ar, at, atr, atc), ('B', br, bt, btr, btc)]:
        bound = a.mp(a.mm('atanbnd', {'A': original}), real)
        realpart = a.mp(a.mm('rere', {'A': term}), realterm)
        bound = a.rewrite(a.eqsym(realpart), bound)
        cos_nonzero.append(a.mp(a.mm('cosne0', {'A': term}), a.both(complexterm, bound)))
        domain = a.mp(a.mm('atanre', {'A': original}), real)
        tangents.append(a.mp(a.mm('tanatan', {'A': original}), domain))
    cos_sum = a.mp(a.mm('tanaddlem', {'A': at, 'B': bt}), a.both(a.both(atc, btc), a.both(*cos_nonzero)))
    for tangent in tangents:
        cos_sum = a.rewrite(tangent, cos_sum)
    cos_sum = iff(cos_sum, product_not_one, 1)
    tan_sum = a.mp(a.mm('tanadd', {'A': at, 'B': bt}), a.both(a.both(atc, btc), a.both(*cos_nonzero, cos_sum)))
    for tangent in tangents:
        tan_sum = a.rewrite(tangent, tan_sum)
    tan_sum = a.rewrite(quotient_one, tan_sum)
    realpart = a.mp(a.mm('rere', {'A': sum_term}), sum_real)
    member = a.rewrite(a.eqsym(realpart), member)
    inverse = a.mp(a.mm('atantan', {'A': sum_term}), a.both(real_complex(sum_term, sum_real), member))
    inverse = a.rewrite(tan_sum, inverse)
    inverse = a.rewrite(a.mm('atan1'), inverse)
    result = a.eqsym(inverse)
    expected = '|- ' + sum_term + ' = ( _pi / 4 )'
    hypotheses = frozenset(a.infer(p)[0] for p in (ar, br, apos, bpos, alt, blt, product_not_one, quotient_one))
    if a.infer(result) != (expected, hypotheses):
        raise a.ProofError(('arctangent_addition_one_scope', a.infer(result)))
    return result


def reciprocal_facts(n):
    real_n, positive_n = a.mm(n + 're'), a.mm(n + 'pos')
    nonzero_n = a.mp(a.mm('gt0ne0', {'A': n}), a.both(real_n, positive_n))
    r = '( 1 / ' + n + ' )'
    real_r = a.mp(a.mm('redivcl', {'A': '1', 'B': n}), a.both(a.mm('1re'), real_n, nonzero_n))
    positive_r = a.mp(a.mm('recgt0', {'A': n}), a.both(real_n, positive_n))
    one_positive = a.both(a.mm('1re'), a.mm('0lt1'))
    comparison = a.mp(a.mm('ltdiv2', {'A': '1', 'B': n, 'C': '1'}), a.both(one_positive, a.both(real_n, positive_n), one_positive))
    below_one = iff(comparison, a.mm('1lt' + n))
    below_one = a.rewrite(a.mm('1div1e1'), below_one)
    return real_r, positive_r, below_one


def specialize(proof, substitution, discharge):
    def replace(text):
        return ' '.join(substitution.get(token, token) for token in text.split())
    rule = proof[0]
    if rule == 'assume':
        formula = replace(proof[1])
        if formula not in discharge:
            raise a.ProofError(('missing_rational_hypothesis', formula))
        return discharge[formula]
    if rule == 'mm':
        values = tuple((key, replace(value)) for key, value in proof[2])
        return ('mm', proof[1], values, proof[3], tuple(specialize(child, substitution, discharge) for child in proof[4]))
    if rule == 'and':
        return ('and', *(specialize(child, substitution, discharge) for child in proof[1:]))
    if rule in ('mp', 'rewrite', 'rall_elim'):
        return (rule, specialize(proof[1], substitution, discharge), specialize(proof[2], substitution, discharge))
    if rule in ('and_elim',):
        return (rule, specialize(proof[1], substitution, discharge), proof[2])
    if rule == 'eqsym':
        return (rule, specialize(proof[1], substitution, discharge))
    if rule == 'iff_mp':
        return (rule, specialize(proof[1], substitution, discharge), specialize(proof[2], substitution, discharge), proof[3])
    if rule == 'imp_intro':
        return (rule, replace(proof[1]), specialize(proof[2], substitution, discharge))
    raise a.ProofError(('unsupported_specialization_rule', rule))


def pi_two_arctangents():
    half, third, sixth = '( 1 / 2 )', '( 1 / 3 )', '( 1 / 6 )'
    hr, hp, hl = reciprocal_facts('2')
    tr, tp, tl = reciprocal_facts('3')
    sr, sp, sl = reciprocal_facts('6')
    product_term = '( ' + half + ' x. ' + third + ' )'
    product = a.mp(a.mm('divmuldiv', {'A': '1', 'B': '1', 'C': '2', 'D': '3'}), a.both(a.both(real_complex('1', a.mm('1re')), real_complex('1', a.mm('1re'))), a.both(a.mm('2cnne0'), a.both(a.mm('3cn'), a.mm('3ne0')))))
    product = a.rewrite(a.mm('1t1e1'), product)
    product = a.rewrite(a.mm('2t3e6'), product)
    one_not_sixth = a.mp(a.mm('ltne', {'A': sixth, 'B': '1'}), a.both(sr, sl))
    sixth_not_one = iff(a.mm('necom', {'A': '1', 'B': sixth}), one_not_sixth)
    product_not_one = a.rewrite(a.eqsym(product), sixth_not_one)
    denominator = a.mp(a.mm('subsub', {'A': '1', 'B': half, 'C': third}), a.both(real_complex('1', a.mm('1re')), real_complex(half, hr), real_complex(third, tr)))
    denominator = a.rewrite(a.mm('halfthird'), denominator)
    denominator = a.rewrite(a.mm('1mhlfehlf'), denominator)
    denominator = a.rewrite(a.eqsym(product), denominator)
    numerator = '( ' + half + ' + ' + third + ' )'
    num_real = real_add(half, third, hr, tr)
    num_positive = a.mp(a.mm('addgt0', {'A': half, 'B': third}), a.both(a.both(hr, tr), a.both(hp, tp)))
    num_nonzero = a.mp(a.mm('gt0ne0', {'A': numerator}), a.both(num_real, num_positive))
    quotient_self = a.mp(a.mm('divid', {'A': numerator}), a.both(real_complex(numerator, num_real), num_nonzero))
    den_term = '( 1 - ' + product_term + ' )'
    quotient = a.mp(a.mm('oveq2', {'A': den_term, 'B': numerator, 'C': numerator, 'F': '/'}), denominator)
    quotient = a.rewrite(quotient_self, quotient)
    facts = (hr, hp, hl, tr, tp, tl, product_not_one, quotient)
    discharge = {a.infer(proof)[0]: proof for proof in facts}
    sum_identity = specialize(arctangent_addition_one(), {'A': half, 'B': third}, discharge)
    expected_sum = '|- ( ( arctan ` ( 1 / 2 ) ) + ( arctan ` ( 1 / 3 ) ) ) = ( _pi / 4 )'
    if a.infer(sum_identity) != (expected_sum, frozenset()):
        raise a.ProofError(('arctangent_numeric_scope', a.infer(sum_identity)))
    multiply = a.mp(a.mm('divcan2', {'A': '_pi', 'B': '4'}), a.both(real_complex('_pi', a.mm('pire')), a.mm('4cn'), a.mm('4ne0')))
    result = a.rewrite(a.eqsym(sum_identity), multiply)
    expected = '|- ( 4 x. ( ( arctan ` ( 1 / 2 ) ) + ( arctan ` ( 1 / 3 ) ) ) ) = _pi'
    if a.infer(result) != (expected, frozenset()):
        raise a.ProofError(('pi_identity_scope', a.infer(result)))
    return result


def arctangent_series_bounds():
    from fundamentos_log import imp
    ar, an, alt, mn = h('A e. RR'), h('0 <_ A'), h('A < 1'), h('M e. NN0')
    ac = real_complex('A', ar)
    abs_a = a.mp(a.mm('absid'), a.both(ar, an))
    abs_lt = a.rewrite(a.eqsym(abs_a), alt)
    ale = a.mp(a.mp(a.mm('ltle', {'A':'A','B':'1'}), a.both(ar,a.mm('1re'))),alt)
    exponent = '( ( 2 x. k ) + 1 )'
    power = '( A ^ k )'
    high = '( A ^ ' + exponent + ' )'
    ratio = '( ' + high + ' / ' + exponent + ' )'
    sign = '( -u 1 ^ k )'
    term = '( ' + sign + ' x. ' + ratio + ' )'
    fbody = term.replace(' k ', ' n ')
    f = '( n e. NN0 |-> ' + fbody + ' )'
    g = '( n e. NN0 |-> ( A ^ n ) )'
    ng = '( n e. NN0 |-> -u ( A ^ n ) )'
    tail = '( ZZ>= ` M )'
    mz = a.mp(a.mm('nn0z',{'N':'M'}),mn)
    subset = a.mp(a.mm('uzss',{'M':'0','N':'M'}),a.rewrite(a.mm('nn0uz'),mn))
    subset = a.rewrite(a.eqsym(a.mm('nn0uz')),subset)

    def facts(kn):
        kr=a.mp(a.mm('nn0re',{'A':'k'}),kn)
        kc=real_complex('k',kr)
        kz=a.mp(a.mm('nn0z',{'N':'k'}),kn)
        k0=a.mp(a.mm('nn0ge0',{'N':'k'}),kn)
        twice='( 2 x. k )'
        tn=a.mp(a.mm('nn0mulcl',{'M':'2','N':'k'}),a.both(a.mm('2nn0'),kn))
        tr=a.mp(a.mm('nn0re',{'A':twice}),tn)
        en=a.mp(a.mm('nn0p1nn',{'N':twice}),tn)
        en0=a.mp(a.mm('nnnn0',{'A':exponent}),en)
        er=a.mp(a.mm('nnre',{'A':exponent}),en)
        ec=real_complex(exponent,er)
        ez=a.mp(a.mm('nnz',{'N':exponent}),en)
        ep=a.mp(a.mm('rpgt0',{'A':exponent}),a.mp(a.mm('nnrp',{'A':exponent}),en))
        ene=a.mp(a.mm('nnne0',{'A':exponent}),en)
        ege=a.mp(a.mm('nnge1',{'A':exponent}),en)
        two_ge=a.mp(a.mp(a.mm('ltle',{'A':'1','B':'2'}),a.both(a.mm('1re'),a.mm('2re'))),a.mm('1lt2'))
        k_le_twice=a.mp(a.mm('lemulge11',{'A':'k','B':'2'}),a.both(a.both(kr,a.mm('2re')),a.both(k0,two_ge)))
        k_le_twice=a.rewrite(a.mp(a.mm('mulcom',{'A':'k','B':'2'}),a.both(kc,a.mm('2cn'))),k_le_twice)
        twice_le_e=a.mp(a.mm('nn0addge1',{'A':twice,'N':'1'}),a.both(tr,a.mm('1nn0')))
        k_le_e=a.mp(a.mp(a.mm('letr',{'A':'k','B':twice,'C':exponent}),a.both(kr,tr,er)),a.both(k_le_twice,twice_le_e))
        euz=iff(a.mp(a.mm('eluz',{'M':'k','N':exponent}),a.both(kz,ez)),k_le_e,1)
        high_le=a.mp(a.mm('leexp2r',{'A':'A','M':'k','N':exponent}),a.both(a.both(ar,kn,euz),a.both(an,ale)))
        pr=a.mp(a.mm('reexpcl',{'A':'A','N':'k'}),a.both(ar,kn))
        pc=real_complex(power,pr)
        hr=a.mp(a.mm('reexpcl',{'A':'A','N':exponent}),a.both(ar,en0))
        hc=real_complex(high,hr)
        hn=a.mp(a.mm('expge0',{'A':'A','N':exponent}),a.both(ar,en0,an))
        rr=a.mp(a.mm('redivcl',{'A':high,'B':exponent}),a.both(hr,er,ene))
        rc=real_complex(ratio,rr)
        rn=a.mp(a.mm('divge0',{'A':high,'B':exponent}),a.both(a.both(hr,hn),a.both(er,ep)))
        growth=a.mp(a.mm('lemulge11',{'A':high,'B':exponent}),a.both(a.both(hr,er),a.both(hn,ege)))
        growth=a.rewrite(a.mp(a.mm('mulcom',{'A':high,'B':exponent}),a.both(hc,ec)),growth)
        ratio_le=iff(a.mp(a.mm('ledivmul',{'A':high,'B':high,'C':exponent}),a.both(hr,hr,a.both(er,ep))),growth,1)
        ratio_le=a.mp(a.mp(a.mm('letr',{'A':ratio,'B':high,'C':power}),a.both(rr,hr,pr)),a.both(ratio_le,high_le))
        neg_real=a.mp(a.mm('renegcl',{'A':'1'}),a.mm('1re'))
        sr=a.mp(a.mm('reexpcl',{'A':'-u 1','N':'k'}),a.both(neg_real,kn))
        sc=real_complex(sign,sr)
        term_real=a.mp(a.mm('remulcl',{'A':sign,'B':ratio}),a.both(sr,rr))
        sign_abs=a.mp(a.mm('absexp',{'A':'-u 1','N':'k'}),a.both(a.mm('neg1cn'),kn))
        sign_abs=a.rewrite(a.mp(a.mm('absneg',{'A':'1'}),real_complex('1',a.mm('1re'))),sign_abs)
        sign_abs=a.rewrite(a.mm('abs1'),sign_abs)
        sign_abs=a.rewrite(a.mp(a.mm('1exp',{'N':'k'}),kz),sign_abs)
        term_abs=a.mp(a.mm('absmul',{'A':sign,'B':ratio}),a.both(sc,rc))
        term_abs=a.rewrite(sign_abs,term_abs)
        term_abs=a.rewrite(a.mp(a.mm('absid',{'A':ratio}),a.both(rr,rn)),term_abs)
        term_abs=a.rewrite(a.mp(a.mm('mullid',{'A':ratio}),rc),term_abs)
        abs_bound=a.rewrite(a.eqsym(term_abs),ratio_le)
        bounds=iff(a.mp(a.mm('absle',{'A':term,'B':power}),a.both(term_real,pr)),abs_bound)
        def ov(op,left_n,left_k,right_n,right_k,lp,rp):
            return a.mm('oveq12d',{'ph':'n = k','A':left_n,'B':left_k,'C':right_n,'D':right_k,'F':op},(lp,rp))
        def reflex(t):
            return imp('n = k',a.eqref(t))
        nk=imp('n = k',h('n = k'))
        ep_sub=ov('+','( 2 x. n )',twice,'1','1',ov('x.','2','2','n','k',reflex('2'),nk),reflex('1'))
        high_sub=ov('^','A','A',exponent.replace(' k ',' n '),exponent,reflex('A'),ep_sub)
        ratio_sub=ov('/',high.replace(' k ',' n '),high,exponent.replace(' k ',' n '),exponent,high_sub,ep_sub)
        sign_sub=ov('^','-u 1','-u 1','n','k',reflex('-u 1'),nk)
        term_sub=ov('x.',sign.replace(' k ',' n '),sign,ratio.replace(' k ',' n '),ratio,sign_sub,ratio_sub)
        power_sub=ov('^','A','A','n','k',reflex('A'),nk)
        neg_sub=a.mm('negeqd',{'ph':'n = k','A':'( A ^ n )','B':power},(power_sub,))
        def value(function,body,result,substitution,exists):
            return a.mp(a.mm('fvmpt',{'x':'n','A':'k','D':'NN0','B':body,'C':result,'F':function},(substitution,a.eqref(function),exists)),kn)
        fv=value(f,fbody,term,term_sub,a.mm('ovex',{'A':sign,'B':ratio,'F':'x.'}))
        gv=value(g,'( A ^ n )',power,power_sub,a.mm('ovex',{'A':'A','B':'k','F':'^'}))
        ngv=value(ng,'-u ( A ^ n )','-u '+power,neg_sub,a.mm('negex',{'A':power}))
        return {'real':term_real,'complex':real_complex(term,term_real),'power_real':pr,'power_complex':pc,'lower':part(bounds,0),'upper':part(bounds,1),'f_value':fv,'g_value':gv,'ng_value':ngv}

    base_condition='( T. /\\ k e. NN0 )'
    base=facts(part(h(base_condition),1))
    conv=a.mp(a.mm('atantayl3',{'F':f},(a.eqref(f),)),a.both(ac,abs_lt))
    domain=a.mp(a.mm('releldmi',{'A':f'seq 0 ( + , {f} )','B':'( arctan ` A )','R':'~~>'},(a.mm('climrel'),)),conv)
    tail_equiv=a.unlift(a.mm('iserex',{'ph':'T.','M':'0','N':'M','Z':'NN0','F':f},(a.mm('nn0uz'),a.lift(mn),imp(base_condition,a.rewrite(a.eqsym(base['f_value']),base['complex'])))))
    tail_domain=iff(tail_equiv,domain)
    split=a.unlift(a.mm('isumsplit',{'ph':'T.','M':'0','N':'M','Z':'NN0','W':tail,'F':f,'A':term},(a.mm('nn0uz'),a.eqref(tail),a.lift(mn),imp(base_condition,base['f_value']),imp(base_condition,base['complex']),a.lift(domain))))
    sum_limit=a.unlift(a.mm('isumclim2',{'ph':'T.','M':'0','Z':'NN0','F':f,'A':term},(a.mm('nn0uz'),a.lift(a.mm('0z')),imp(base_condition,base['f_value']),imp(base_condition,base['complex']),a.lift(domain))))
    sum_value=a.mp(a.mm('climuni',{'F':f'seq 0 ( + , {f} )','A':'sum_ k e. NN0 '+term,'B':'( arctan ` A )'}),a.both(sum_limit,conv))
    decomposition=a.rewrite(split,a.eqsym(sum_value))
    condition=f'( T. /\\ k e. {tail} )'
    kn=a.mm('sselii',{'A':tail,'B':'NN0','C':'k'},(subset,part(h(condition),1)))
    fs=facts(kn)
    geom=a.unlift(a.mm('geolim2',{'ph':'T.','F':g},(a.lift(ac),a.lift(abs_lt),a.lift(mn),imp(condition,fs['g_value']))))
    bound='( ( A ^ M ) / ( 1 - A ) )'
    geom_domain=a.mp(a.mm('releldmi',{'A':f'seq M ( + , {g} )','B':bound,'R':'~~>'},(a.mm('climrel'),)),geom)
    geom_sumlim=a.unlift(a.mm('isumclim2',{'ph':'T.','Z':tail,'F':g,'A':power},(a.eqref(tail),a.lift(mz),imp(condition,fs['g_value']),imp(condition,fs['power_complex']),a.lift(geom_domain))))
    geom_value=a.mp(a.mm('climuni',{'F':f'seq M ( + , {g} )','A':f'sum_ k e. {tail} '+power,'B':bound}),a.both(geom_sumlim,geom))
    upper=a.unlift(a.mm('isumle',{'ph':'T.','Z':tail,'F':f,'G':g,'A':term,'B':power},(a.eqref(tail),a.lift(mz),imp(condition,fs['f_value']),imp(condition,fs['real']),imp(condition,fs['g_value']),imp(condition,fs['power_real']),imp(condition,fs['upper']),a.lift(tail_domain),a.lift(geom_domain))))
    upper=a.rewrite(geom_value,upper)
    negative_relation=a.mp(a.mm('mulm1',{'A':power}),fs['power_complex'])
    negative_relation=a.rewrite(a.eqsym(fs['ng_value']),negative_relation)
    negative_relation=a.rewrite(a.eqsym(fs['g_value']),negative_relation)
    ng_limit=a.unlift(a.mm('isermulc2',{'ph':'T.','Z':tail,'F':g,'G':ng,'C':'-u 1','A':bound},(a.eqref(tail),a.lift(mz),a.lift(a.mm('neg1cn')),a.lift(geom),imp(condition,a.rewrite(a.eqsym(fs['g_value']),fs['power_complex'])),imp(condition,a.eqsym(negative_relation)))))
    ng_domain=a.mp(a.mm('releldmi',{'A':f'seq M ( + , {ng} )','B':'( -u 1 x. '+bound+' )','R':'~~>'},(a.mm('climrel'),)),ng_limit)
    ngr=a.mp(a.mm('renegcl',{'A':power}),fs['power_real'])
    ng_sumlim=a.unlift(a.mm('isumclim2',{'ph':'T.','Z':tail,'F':ng,'A':'-u '+power},(a.eqref(tail),a.lift(mz),imp(condition,fs['ng_value']),imp(condition,real_complex('-u '+power,ngr)),a.lift(ng_domain))))
    ng_value=a.mp(a.mm('climuni',{'F':f'seq M ( + , {ng} )','A':f'sum_ k e. {tail} -u '+power,'B':'( -u 1 x. '+bound+' )'}),a.both(ng_sumlim,ng_limit))
    lower=a.unlift(a.mm('isumle',{'ph':'T.','Z':tail,'F':ng,'G':f,'A':'-u '+power,'B':term},(a.eqref(tail),a.lift(mz),imp(condition,fs['ng_value']),imp(condition,ngr),imp(condition,fs['f_value']),imp(condition,fs['real']),imp(condition,fs['lower']),a.lift(ng_domain),a.lift(tail_domain))))
    lower=a.rewrite(ng_value,lower)
    results={'arctangent_series_decomposition':decomposition,'arctangent_series_tail_lower':lower,'arctangent_series_tail_upper':upper}
    expected={
        'arctangent_series_decomposition':f'|- ( arctan ` A ) = ( sum_ k e. ( 0 ... ( M - 1 ) ) {term} + sum_ k e. {tail} {term} )',
        'arctangent_series_tail_lower':f'|- ( -u 1 x. {bound} ) <_ sum_ k e. {tail} {term}',
        'arctangent_series_tail_upper':f'|- sum_ k e. {tail} {term} <_ {bound}'
    }
    hypotheses=frozenset({'|- A e. RR','|- 0 <_ A','|- A < 1','|- M e. NN0'})
    for name,proof in results.items():
        if a.infer(proof)!=(expected[name],hypotheses):
            raise a.ProofError(('arctangent_series_scope',name,a.infer(proof)))
    return results


def gaussian_normalizer():
    x='( 2 x. _pi )'
    root='( sqrt ` '+x+' )'
    positive=a.mp(a.mm('rpmulcl',{'A':'2','B':'_pi'}),a.both(a.mm('2rp'),a.mm('pirp')))
    root_positive=a.mp(a.mm('rpsqrtcl',{'A':x}),positive)
    root_real=a.mp(a.mm('rpre',{'A':root}),root_positive)
    root_gt0=a.mp(a.mm('rpgt0',{'A':root}),root_positive)
    x_real=a.mp(a.mm('rpre',{'A':x}),positive)
    square=a.mp(a.mm('sqrtth',{'A':x}),real_complex(x,x_real))
    return {'gaussian_normalizer_positive':root_gt0,'gaussian_normalizer_real':root_real,'gaussian_normalizer_square':square}



def certificates():
    return {'arctangent_addition_one': arctangent_addition_one(), 'pi_two_arctangents': pi_two_arctangents(), **arctangent_series_bounds(), **gaussian_normalizer()}


if __name__ == '__main__':
    results = []
    for name, proof in certificates().items():
        formula, hypotheses = a.infer(proof)
        results.append({'id': name, 'passed': True, 'formula': formula, 'hypotheses': sorted(hypotheses)})
    print(json.dumps({'backend': 'Python/Metamath', 'passed': True, 'results': results}))
