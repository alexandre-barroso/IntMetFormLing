import json
import analise_geral as a
from triplice import iff, part, h, as_real, larger_positive


def implies(formula,proof):
    result=('imp_intro',formula,proof)
    a.infer(result)
    return result


def positive_interval():
    hp=h('A e. RR+');br=h('B e. RR');ar=as_real('A',hp)
    whole='( A [,] B )'
    membership=h('x e. '+whole)
    entries=iff(a.mp(a.mm('elicc2',{'A':'A','B':'B','C':'x'}),a.both(ar,br)),membership)
    xr=part(entries,0);ax=part(entries,1)
    apos=a.mp(a.mm('rpgt0',{'A':'A'}),hp)
    xpos=a.mp(a.mp(a.mm('ltletr',{'A':'0','B':'A','C':'x'}),a.both(a.mm('0re'),ar,xr)),a.both(apos,ax))
    xp=iff(a.mm('elrp',{'A':'x'}),a.both(xr,xpos),1)
    result=a.unlift(a.mm('ssrdv',{'ph':'T.','x':'x','A':whole,'B':'RR+'},(a.lift(implies('|- x e. '+whole,xp)),)))
    expected='|- ( A [,] B ) C_ RR+'
    if a.infer(result)!=(expected,frozenset({'|- A e. RR+','|- B e. RR'})):
        raise a.ProofError('positive_interval_scope')
    return result


def logarithm_mean_value():
    hp=h('A e. RR+');br=h('B e. RR');order=h('A < B');ar=as_real('A',hp)
    bp=larger_positive('A','B',hp,br,order)
    whole='( A [,] B )';inside='( A (,) B )'
    logf='( log |` RR+ )';restricted=f'( {logf} |` {whole} )'
    reciprocal=f'( x e. {inside} |-> ( 1 / x ) )'
    j='( TopOpen ` CCfld )';t='( topGen ` ran (,) )'
    css=positive_interval()
    inner_ss=a.mm('ioossicc')
    inner_rp=a.mm('sstri',{'A':inside,'B':whole,'C':'RR+'},(inner_ss,css))
    real_ss=a.mp(a.mm('iccssre'),a.both(ar,br))
    log_cn=a.mm('relogcn')
    cn=a.mp(a.mp(a.mm('rescncf',{'A':'RR+','B':'RR','C':whole,'F':logf}),css),log_cn)
    func=a.mp(a.mm('cncff',{'F':logf,'A':'RR+','B':'RR'}),log_cn)
    func_complex=a.mp(a.mm('fss',{'F':logf,'A':'RR+','B':'RR','C':'CC'}),a.both(func,a.mm('axresscn')))
    deriv=a.mp(a.mm('dvres',{'K':j,'T':t,'S':'RR','F':logf,'A':'RR+','B':whole},(a.eqref(j),a.mm('tgioo4'))),a.both(a.both(a.mm('axresscn'),func_complex),a.both(a.mm('rpssre'),real_ss)))
    deriv=a.rewrite(a.mm('dvrelog'),deriv)
    interior=a.mp(a.mm('iccntr'),a.both(ar,br))
    deriv=a.rewrite(interior,deriv)
    restriction=a.mp(a.mm('resmpt',{'x':'x','A':'RR+','B':inside,'C':'( 1 / x )'}),inner_rp)
    deriv=a.rewrite(restriction,deriv)
    rex=a.mm('ovex',{'A':'1','B':'x','F':'/'})
    all_set=a.mm('rgen',{'x':'x','A':inside,'ph':'( 1 / x ) e. _V'},(implies('|- x e. '+inside,rex),))
    domain=a.mp(a.mm('dmmptg',{'x':'x','A':inside,'B':'( 1 / x )','V':'_V'}),all_set)
    deriv_domain=a.mp(a.mm('dmeq',{'A':f'( RR _D {restricted} )','B':reciprocal}),deriv)
    deriv_domain=a.rewrite(domain,deriv_domain)
    mvt=a.unlift(a.mm('mvth',{'ph':'T.','x':'x','A':'A','B':'B','F':restricted},tuple(a.lift(p) for p in (ar,br,order,cn,deriv_domain))))
    mvt=a.rewrite(deriv,mvt)
    le=a.mp(a.mp(a.mm('ltle'),a.both(ar,br)),order)
    endpoints=a.both(a.mp(a.mm('rexr',{'A':'A'}),ar),a.mp(a.mm('rexr',{'A':'B'}),br),le)
    for value,hpoint,hpr in [('A',a.mp(a.mm('lbicc2'),endpoints),hp),('B',a.mp(a.mm('ubicc2'),endpoints),bp)]:
        outer=a.mp(a.mm('fvres',{'A':value,'B':whole,'F':logf}),hpoint)
        mvt=a.rewrite(outer,mvt)
        inner=a.mp(a.mm('fvres',{'A':value,'B':'RR+','F':'log'}),hpr)
        mvt=a.rewrite(inner,mvt)
    gx=f'( {reciprocal} ` x )'
    quotient='( ( ( log ` B ) - ( log ` A ) ) / ( B - A ) )'
    member=h('x e. '+inside)
    value=a.mp(a.mm('fvmpt2',{'x':'x','A':inside,'B':'( 1 / x )','C':'_V','F':reciprocal},(a.eqref(reciprocal),)),a.both(member,rex))
    value_condition=implies('|- x e. '+inside,value)
    eq_condition=a.mm('eqeq1d',{'ph':'x e. '+inside,'A':gx,'B':'( 1 / x )','C':quotient},(value_condition,))
    eq_exists=a.mm('rexbiia',{'x':'x','A':inside,'ph':gx+' = '+quotient,'ps':'( 1 / x ) = '+quotient},(eq_condition,))
    result=iff(eq_exists,mvt)
    expected=f'|- E. x e. {inside} ( 1 / x ) = {quotient}'
    hypotheses=frozenset({'|- A e. RR+','|- B e. RR','|- A < B'})
    if a.infer(result)!=(expected,hypotheses):
        raise a.ProofError(('logarithm_mean_value_scope',a.infer(result)))
    return result


def fundamental_calculus(derivative_proof=None):
    whole='( A [,] B )';inside='( A (,) B )';gvalue='( G ` x )'
    ar,br=h('A e. RR'),h('B e. RR')
    hab=h('A <_ B')
    fc=h(f'F e. ( {whole} -cn-> CC )');gc=h(f'G e. ( {whole} -cn-> CC )')
    restriction=f'( G |` {inside} )';derivative='( RR _D F )'
    hd=h(derivative+' = '+restriction) if derivative_proof is None else derivative_proof
    if a.infer(hd)[0]!='|- '+derivative+' = '+restriction:
        raise a.ProofError('derivative_graph_interface')
    ss=a.mm('ioossicc')
    gcn=a.mp(a.mp(a.mm('rescncf',{'A':whole,'B':'CC','C':inside,'F':'G'}),ss),gc)
    dcn=a.rewrite(a.eqsym(hd),gcn)
    gf=a.mp(a.mm('cncff',{'F':'G','A':whole,'B':'CC'}),gc)
    gmap=a.unlift(a.mm('feqmptd',{'ph':'T.','x':'x','F':'G','A':whole,'B':'CC'},(a.lift(gf),)))
    gi=a.mp(a.mm('cniccibl',{'A':'A','B':'B','F':'G'}),a.both(ar,br,gc))
    gmap_integrable=a.rewrite(gmap,gi)
    cond='|- ( T. /\\ x e. '+whole+' )'
    member=part(a.assumption(cond),1)
    value=a.mp(a.mm('ffvelcdm',{'A':whole,'B':'CC','C':'x','F':'G'}),a.both(gf,member))
    inner_integrable=a.unlift(a.mm('iblss',{'ph':'T.','x':'x','A':inside,'B':whole,'C':gvalue,'V':'CC'},(a.lift(ss),a.lift(a.mm('ioombl')),implies(cond,value),a.lift(gmap_integrable))))
    restricted_map=a.mp(a.mm('resmpt',{'x':'x','A':whole,'B':inside,'C':gvalue}),ss)
    gmap_restricted=a.mp(a.mm('reseq1',{'A':'G','B':f'( x e. {whole} |-> {gvalue} )','C':inside}),gmap)
    gmap_restricted=a.rewrite(restricted_map,gmap_restricted)
    gi=a.rewrite(a.eqsym(gmap_restricted),inner_integrable)
    di=a.rewrite(a.eqsym(hd),gi)
    result=a.unlift(a.mm('ftc2',{'ph':'T.','t':'x','A':'A','B':'B','F':'F'},tuple(a.lift(p) for p in (ar,br,hab,dcn,di,fc))))
    result=a.rewrite(hd,result)
    cond='|- ( T. /\\ x e. '+inside+' )'
    member=part(a.assumption(cond),1)
    val=a.mp(a.mm('fvres',{'A':'x','B':inside,'F':'G'}),member)
    integrand=a.unlift(a.mm('itgeq2dv',{'ph':'T.','x':'x','A':inside,'B':f'( {restriction} ` x )','C':gvalue},(implies(cond,val),)))
    result=a.rewrite(integrand,result)
    closed_condition='|- ( T. /\\ x e. '+whole+' )'
    closed_member=part(a.assumption(closed_condition),1)
    closed_value=a.mp(a.mm('ffvelcdm',{'A':whole,'B':'CC','C':'x','F':'G'}),a.both(gf,closed_member))
    endpoints=a.unlift(a.mm('itgioo',{'ph':'T.','x':'x','A':'A','B':'B','C':gvalue},(a.lift(ar),a.lift(br),implies(closed_condition,closed_value))))
    result=a.rewrite(endpoints,result)
    expected=f'|- S. {whole} {gvalue} _d x = ( ( F ` B ) - ( F ` A ) )'
    hypotheses=frozenset().union(*(a.infer(p)[1] for p in (ar,br,hab,fc,gc,hd)))
    if a.infer(result)!=(expected,hypotheses):
        raise a.ProofError(('fundamental_calculus_scope',a.infer(result)))
    return result


def derivative_pointwise_graph():
    whole='( A [,] B )';inside='( A (,) B )';derivative='( RR _D F )';restriction=f'( G |` {inside} )'
    ar,br=h('A e. RR'),h('B e. RR')
    fc=h(f'F e. ( {whole} -cn-> CC )');gc=h(f'G e. ( {whole} -cn-> CC )')
    pointwise=h(f'A. x e. {inside} x {derivative} ( G ` x )')
    ff=a.mp(a.mm('cncff',{'F':'F','A':whole,'B':'CC'}),fc)
    whole_real=a.mp(a.mm('iccssre'),a.both(ar,br))
    topology='( topGen ` ran (,) )';complex_topology='( TopOpen ` CCfld )'
    derivative_info=a.mp(a.mm('dvfval',{'S':'RR','F':'F','A':whole,'T':topology,'K':complex_topology},(a.mm('tgioo4'),a.eqref(complex_topology))),a.both(a.mm('axresscn'),ff,whole_real))
    derivative_bound=part(derivative_info,1)
    derivative_bound=a.rewrite(a.mp(a.mm('iccntr'),a.both(ar,br)),derivative_bound)
    domain_upper=a.mp(a.mm('dmss',{'A':derivative,'B':f'( {inside} X. CC )'}),derivative_bound)
    cc_nonempty=a.mp(a.mm('ne0i',{'A':'CC','B':'0'}),a.mm('0cn'))
    product_domain=a.mp(a.mm('dmxp',{'A':inside,'B':'CC'}),cc_nonempty)
    domain_upper=a.rewrite(product_domain,domain_upper)
    df=a.mm('dvf',{'F':'F'})
    dfn=a.mp(a.mm('ffn',{'F':derivative,'A':f'dom {derivative}','B':'CC'}),df)
    member=h('x e. '+inside)
    derivative_at=('rall_elim',pointwise,member)
    domain_member=a.mp(a.mm('fnbr',{'F':derivative,'A':f'dom {derivative}','B':'x','C':'( G ` x )'}),a.both(dfn,derivative_at))
    domain_lower=a.mm('ssriv',{'x':'x','A':inside,'B':f'dom {derivative}'},(implies('|- x e. '+inside,domain_member),))
    domain=a.mm('eqssi',{'A':f'dom {derivative}','B':inside},(domain_upper,domain_lower))
    dfn=a.rewrite(domain,dfn)
    d_fun=a.mp(a.mm('ffun',{'F':derivative,'A':f'dom {derivative}','B':'CC'}),df)
    derivative_value=a.mp(a.mp(a.mm('funbrfv',{'F':derivative,'A':'x','B':'( G ` x )'}),d_fun),derivative_at)
    restricted_value=a.mp(a.mm('fvres',{'A':'x','B':inside,'F':'G'}),member)
    equality=a.rewrite(a.eqsym(restricted_value),derivative_value)
    all_values=a.mm('rgen',{'x':'x','A':inside,'ph':f'( {derivative} ` x ) = ( {restriction} ` x )'},(implies('|- x e. '+inside,equality),))
    gcn=a.mp(a.mp(a.mm('rescncf',{'A':whole,'B':'CC','C':inside,'F':'G'}),a.mm('ioossicc')),gc)
    gf=a.mp(a.mm('cncff',{'F':restriction,'A':inside,'B':'CC'}),gcn)
    gfn=a.mp(a.mm('ffn',{'F':restriction,'A':inside,'B':'CC'}),gf)
    equality_functions=a.mp(a.mm('eqfnfv',{'F':derivative,'G':restriction,'A':inside,'x':'x'}),a.both(dfn,gfn))
    result=iff(equality_functions,all_values,1)
    expected=f'|- {derivative} = {restriction}'
    hypotheses=frozenset(a.infer(p)[0] for p in (ar,br,fc,gc,pointwise))
    if a.infer(result)!=(expected,hypotheses):
        raise a.ProofError(('pointwise_derivative_graph_scope',a.infer(result)))
    return result


def fundamental_calculus_pointwise():
    result=fundamental_calculus(derivative_pointwise_graph())
    expected='|- S. ( A [,] B ) ( G ` x ) _d x = ( ( F ` B ) - ( F ` A ) )'
    hypotheses=frozenset({'|- A e. RR','|- B e. RR','|- A <_ B','|- F e. ( ( A [,] B ) -cn-> CC )','|- G e. ( ( A [,] B ) -cn-> CC )','|- A. x e. ( A (,) B ) x ( RR _D F ) ( G ` x )'})
    if a.infer(result)!=(expected,hypotheses):
        raise a.ProofError(('pointwise_fundamental_calculus_scope',a.infer(result)))
    return result


def singleton_integral():
    hr=h('A e. RR');hf=h('F : RR --> RR')
    domain='{ A }';value='( F ` x )'
    subset=a.mp(a.mm('snssi',{'A':'A','B':'RR'}),hr)
    null=a.mp(a.mm('ovolsn'),hr)
    cond='|- ( T. /\\ x e. { A } )'
    member=part(a.assumption(cond),1)
    xr=a.mm('sselii',{'A':domain,'B':'RR','C':'x'},(subset,member))
    vr=a.mp(a.mm('ffvelcdm',{'F':'F','A':'RR','B':'RR','C':'x'}),a.both(hf,xr))
    vc=a.unlift(a.mm('recnd',{'ph':'T.','A':value},(a.lift(vr),)))
    result=a.unlift(a.mm('itgvol0',{'ph':'T.','x':'x','A':domain,'B':value},(a.lift(subset),a.lift(null),implies(cond,vc))))
    expected=f'|- ( ( x e. {domain} |-> {value} ) e. L^1 /\\ S. {domain} {value} _d x = 0 )'
    if a.infer(result)!=(expected,frozenset({'|- A e. RR','|- F : RR --> RR'})):
        raise a.ProofError(('singleton_scope',a.infer(result)))
    return result



def raw_certificates():
    return {'positive_closed_interval':positive_interval(), 'logarithm_mean_value':logarithm_mean_value(), 'fundamental_calculus':fundamental_calculus(), 'derivative_pointwise_graph':derivative_pointwise_graph(), 'fundamental_calculus_pointwise':fundamental_calculus_pointwise(), 'singleton_integral':singleton_integral()}


EXPECTED_INTERFACES = {'positive_closed_interval': ('|- ( A [,] B ) C_ RR+', ('|- A e. RR+', '|- B e. RR')),
 'logarithm_mean_value': ('|- E. x e. ( A (,) B ) ( 1 / x ) = ( ( ( log ` B ) - ( log ` A ) ) / ( B - A ) )',
                          ('|- A < B', '|- A e. RR+', '|- B e. RR')),
 'fundamental_calculus': ('|- S. ( A [,] B ) ( G ` x ) _d x = ( ( F ` B ) - ( F ` A ) )',
                          ('|- ( RR _D F ) = ( G |` ( A (,) B ) )',
                           '|- A <_ B',
                           '|- A e. RR',
                           '|- B e. RR',
                           '|- F e. ( ( A [,] B ) -cn-> CC )',
                           '|- G e. ( ( A [,] B ) -cn-> CC )')),
 'derivative_pointwise_graph': ('|- ( RR _D F ) = ( G |` ( A (,) B ) )',
                                ('|- A e. RR',
                                 '|- A. x e. ( A (,) B ) x ( RR _D F ) ( G ` x )',
                                 '|- B e. RR',
                                 '|- F e. ( ( A [,] B ) -cn-> CC )',
                                 '|- G e. ( ( A [,] B ) -cn-> CC )')),
 'fundamental_calculus_pointwise': ('|- S. ( A [,] B ) ( G ` x ) _d x = ( ( F ` B ) - ( F ` A ) )',
                                    ('|- A <_ B',
                                     '|- A e. RR',
                                     '|- A. x e. ( A (,) B ) x ( RR _D F ) ( G ` x )',
                                     '|- B e. RR',
                                     '|- F e. ( ( A [,] B ) -cn-> CC )',
                                     '|- G e. ( ( A [,] B ) -cn-> CC )')),
 'singleton_integral': ('|- ( ( x e. { A } |-> ( F ` x ) ) e. L^1 /\\ S. { A } ( F ` x ) _d x = 0 )',
                        ('|- A e. RR', '|- F : RR --> RR'))}

def checks():
    results=[]
    proofs=raw_certificates()
    def check(name):
        formula,hypotheses=a.infer(proofs[name])
        expected,required=EXPECTED_INTERFACES[name]
        if formula!=expected or hypotheses!=frozenset(required):
            raise a.ProofError(('certificate_scope',name))
        results.append({'id':name,'passed':True,'formula':formula,'hypotheses':sorted(hypotheses)})
    check('positive_closed_interval')
    check('logarithm_mean_value')
    check('fundamental_calculus')
    check('derivative_pointwise_graph')
    check('fundamental_calculus_pointwise')
    check('singleton_integral')
    return results


if __name__=='__main__':
    results=checks()
    print(json.dumps({'backend':'Python/Metamath','checks':len(results),'passed':True,'results':results}))
