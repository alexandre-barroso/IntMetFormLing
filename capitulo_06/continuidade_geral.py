import json
import sys
from fractions import Fraction
import sympy as sp
from pathlib import Path

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'capitulo_02'))
import analise_geral as a
import riemann_geral as r
from triplice import iff,part,h,as_real,as_complex,positive_parts
from ponte_analise import implies,positive_interval,singleton_integral


def density_continuity():
    X='( A [,] B )';ccnz='( CC \\ { 0 } )'
    hp,hb,hm,hs=h('A e. RR+'),h('B e. RR'),h('M e. RR'),h('S e. RR+')
    ha=as_real('A',hp);sr=as_real('S',hs);sc=as_complex('S',sr)
    xs=a.mp(a.mm('iccssre'),a.both(ha,hb))
    xcc=a.mm('sstri',{'A':X,'B':'RR','C':'CC'},(xs,a.mm('axresscn')))
    ccss=a.mm('ssid',{'A':'CC'})
    nzcc=a.mm('difss',{'A':'CC','B':'{ 0 }'})
    def constant(value,proof,target='CC'):
        subset=ccss if target=='CC' else nzcc
        return a.mp(a.mm('cncfmptc',{'x':'x','A':value,'S':X,'T':target}),a.both(proof,xcc,subset))
    def binary(label,u,v,cu,cv):
        return a.unlift(a.mm(label,{'ph':'T.','x':'x','X':X,'A':u,'B':v},(a.lift(cu),a.lift(cv))))
    def nonzero_constant(value,cp,nz):
        membership=iff(a.mm('eldifsn',{'A':value,'B':'CC','C':'0'}),a.both(cp,nz),1)
        return constant(value,membership,ccnz)
    def pointwise_rewrite(left,right,proof):
        return a.unlift(a.mm('mpteq2dva',{'ph':'T.','x':'x','A':X,'B':left,'C':right},(proof,)))
    logrp='( log |` RR+ )';logrestricted=f'( {logrp} |` {X} )'
    lcn=a.mp(a.mp(a.mm('rescncf',{'A':'RR+','B':'RR','C':X,'F':logrp}),positive_interval()),a.mm('relogcn'))
    cnss=a.mp(a.mm('cncfss',{'A':X,'B':'RR','C':'CC'}),a.both(a.mm('axresscn'),ccss))
    lcn=a.mm('sselii',{'A':f'( {X} -cn-> RR )','B':f'( {X} -cn-> CC )','C':logrestricted},(cnss,lcn))
    lf=a.mp(a.mm('cncff',{'F':logrestricted,'A':X,'B':'CC'}),lcn)
    lmap=a.unlift(a.mm('feqmptd',{'ph':'T.','x':'x','F':logrestricted,'A':X,'B':'CC'},(a.lift(lf),)))
    cond='|- ( T. /\\ x e. '+X+' )';member=part(a.assumption(cond),1)
    xrp=a.mm('sselii',{'A':X,'B':'RR+','C':'x'},(positive_interval(),member))
    outer=a.mp(a.mm('fvres',{'A':'x','B':X,'F':logrp}),member)
    inner=a.mp(a.mm('fvres',{'A':'x','B':'RR+','F':'log'}),xrp)
    value=a.rewrite(inner,outer)
    lexpr='( log ` x )'
    leq=pointwise_rewrite(f'( {logrestricted} ` x )',lexpr,implies(cond,value))
    lcn=a.rewrite(leq,a.rewrite(lmap,lcn))
    diff=f'( {lexpr} - M )'
    diffcn=binary('subcncf',lexpr,'M',lcn,constant('M',as_complex('M',hm)))
    quotient=f'( {diff} / S )'
    sqnz=a.mp(a.mm('rpne0',{'A':'S'}),hs)
    qcn=binary('divcncf',diff,'S',diffcn,nonzero_constant('S',sc,sqnz))
    product=f'( {quotient} x. {quotient} )';square=f'( {quotient} ^ 2 )'
    squarecn=binary('mulcncf',quotient,quotient,qcn,qcn)
    qf=a.mp(a.mm('cncff',{'F':f'( x e. {X} |-> {quotient} )','A':X,'B':'CC'}),qcn)
    qval=a.mp(a.mm('ffvelcdm',{'F':f'( x e. {X} |-> {quotient} )','A':X,'B':'CC','C':'x'}),a.both(qf,member))
    mapvalue=a.mp(a.mm('fvmpt2',{'x':'x','A':X,'B':quotient,'C':'_V','F':f'( x e. {X} |-> {quotient} )'},(a.eqref(f'( x e. {X} |-> {quotient} )'),)),a.both(member,a.mm('ovex',{'A':diff,'B':'S','F':'/'})))
    qtype=a.mm('eqeltrri',{'A':f'( ( x e. {X} |-> {quotient} ) ` x )','B':quotient,'C':'CC'},(mapvalue,qval))
    qsq=a.mp(a.mm('sqval',{'A':quotient}),qtype)
    squareeq=pointwise_rewrite(product,square,implies(cond,a.eqsym(qsq)))
    squarecn=a.rewrite(squareeq,squarecn)
    negsquare=f'( 0 - {square} )'
    negcn=binary('subcncf','0',square,constant('0',a.mm('0cn')),squarecn)
    exponent=f'( {negsquare} / 2 )'
    two_c=as_complex('2',as_real('2',a.mm('2rp')))
    two_nz=a.mp(a.mm('rpne0',{'A':'2'}),a.mm('2rp'))
    expcn=binary('divcncf',negsquare,'2',negcn,nonzero_constant('2',two_c,two_nz))
    numerator=f'( exp ` {exponent} )'
    numcn=a.unlift(a.mm('cncfmpt1f',{'ph':'T.','x':'x','X':X,'F':'exp','A':exponent},(a.lift(a.mm('efcn')),a.lift(expcn))))
    pi_p=iff(a.mm('elrp',{'A':'_pi'}),a.both(a.mm('pire'),a.mm('pipos')),1)
    two_pi='( 2 x. _pi )'
    two_pi_p=a.mp(a.mm('rpmulcl',{'A':'2','B':'_pi'}),a.both(a.mm('2rp'),pi_p))
    root=f'( sqrt ` {two_pi} )'
    root_p=a.mp(a.mm('rpsqrtcl',{'A':two_pi}),two_pi_p)
    scale=f'( S x. {root} )'
    scale_p=a.mp(a.mm('rpmulcl',{'A':'S','B':root}),a.both(hs,root_p))
    scalec=as_complex(scale,as_real(scale,scale_p))
    idcn=a.mp(a.mm('cncfmptid',{'x':'x','S':X,'T':'CC'}),a.both(xcc,ccss))
    denominator=f'( x x. {scale} )'
    dencn=binary('mulcncf','x',scale,idcn,constant(scale,scalec))
    denp=a.mp(a.mm('rpmulcl',{'A':'x','B':scale}),a.both(xrp,scale_p))
    denc=as_complex(denominator,as_real(denominator,denp))
    dennz=a.mp(a.mm('rpne0',{'A':denominator}),denp)
    denmem=iff(a.mm('eldifsn',{'A':denominator,'B':'CC','C':'0'}),a.both(denc,dennz),1)
    denfunc=a.unlift(a.mm('fmpttd',{'ph':'T.','x':'x','A':X,'B':denominator,'C':ccnz},(implies(cond,denmem),)))
    dencodomain=iff(a.mp(a.mm('cncfcdm',{'A':X,'B':'CC','C':ccnz,'F':f'( x e. {X} |-> {denominator} )'}),a.both(nzcc,dencn)),denfunc,1)
    density=f'( {numerator} / {denominator} )'
    result=binary('divcncf',numerator,denominator,numcn,dencodomain)
    expected=f'|- ( x e. {X} |-> {density} ) e. ( {X} -cn-> CC )'
    hypotheses=frozenset(a.infer(p)[0] for p in (hp,hb,hm,hs))
    if a.infer(result)!=(expected,hypotheses):
        raise a.ProofError(('density_continuity_scope',a.infer(result)))
    return {'proof':result,'formula':expected,'hypotheses':hypotheses,'density':density,'function':f'( x e. {X} |-> {density} )','standardized_expression':quotient,'standardized_continuity_complex':qcn}


def density_term():
    return r.fn('lognormal_restriction',r.v('mean'),r.v('scale'),r.A,r.B)


def riemann_specialization(density=None):
    if density is None:
        density=density_continuity()
    expected_density='( ( exp ` ( ( 0 - ( ( ( ( log ` x ) - M ) / S ) ^ 2 ) ) / 2 ) ) / ( x x. ( S x. ( sqrt ` ( 2 x. _pi ) ) ) ) )'
    expected_function=f'( x e. ( A [,] B ) |-> {expected_density} )'
    expected_formula=f'|- {expected_function} e. ( ( A [,] B ) -cn-> CC )'
    expected_hypotheses=frozenset({'|- A e. RR+','|- B e. RR','|- M e. RR','|- S e. RR+'})
    if a.infer(density['proof'])!=(expected_formula,expected_hypotheses) or density['function']!=expected_function or density['density']!=expected_density:
        raise a.ProofError('lognormal_definition_or_continuity_scope')
    real_a=as_real('A',h('A e. RR+'))
    if a.infer(real_a)!=('|- A e. RR',frozenset({'|- A e. RR+'})):
        raise a.ProofError('positive_endpoint_real_bridge')
    source=r.displayed_sum_limit_certificate()
    if source['formula']!=r.expected_riemann_formula() or source['hypotheses']!=r.GLOBALS:
        raise a.ProofError('riemann_general_scope')
    universal=('all','f',('imp',r.continuous(r.F),source['proof']))
    instance=('instantiate',universal,density_term())
    conditional,hypotheses=r.analytic_infer(instance)
    antecedent=r.continuous(density_term())
    expected=r.sub_f(r.expected_riemann_formula(),'f',density_term())
    required=r.GLOBALS-{r.continuous(r.F)}
    if conditional!=r.implies_f(antecedent,expected) or hypotheses!=required:
        raise a.ProofError('riemann_function_instantiation')
    translated=frozenset((r.positive(r.A),r.fn('real',r.B),r.fn('real',r.v('mean')),r.positive(r.v('scale'))))
    available=translated|{r.fn('real',r.A),r.fn('lt',r.A,r.B)}
    if not required<=available:
        raise a.ProofError('undischarged_riemann_hypothesis')
    conclusions={'continuity':antecedent,'limit':conditional[2]}
    if conclusions['continuity']!=conditional[1]:
        raise a.ProofError('riemann_modus_ponens')
    return {'formula':conclusions['limit'],'hypotheses':translated|{r.fn('lt',r.A,r.B)},'function':density_term(),'continuity_proof':density['proof'],'universal_instantiation':instance,'positive_endpoint_proof':real_a}


def figure_specialization():
    general=riemann_specialization()
    values={'a':Fraction(3,100),'b':Fraction(7,50),'mean':Fraction(-67,25),'scale':Fraction(59,100)}
    if not (values['a']>0 and values['a']<values['b'] and values['scale']>0):
        raise a.ProofError('rational_parameter_domain')
    def value(term):
        if term[0]!='var' or term[1] not in values:
            raise a.ProofError('rational_parameter')
        return values[term[1]]
    for premise in general['hypotheses']:
        if premise[0]=='real':
            valid=isinstance(value(premise[1]),Fraction)
        elif premise[0]=='positive':
            valid=value(premise[1])>0
        elif premise[0]=='lt':
            valid=value(premise[1])<value(premise[2])
        else:
            raise a.ProofError('rational_premise')
        if not valid:
            raise a.ProofError('rational_domain_obligation')
    formula=general['formula']
    for name,q in values.items():
        formula=r.sub_f(formula,name,('rational',q.numerator,q.denominator))
    if r.free_f(formula):
        raise a.ProofError('unbound_parameter_after_specialization')
    log_t,m,s,t,root=sp.symbols('log_t m s t root',nonzero=True)
    exponent_a=-( (log_t-m)/s )**2/2
    exponent_b=-(log_t-m)**2/(2*s**2)
    if sp.cancel(exponent_a-exponent_b)!=0 or sp.cancel(1/(t*(s*root))-1/(t*s*root))!=0:
        raise a.ProofError('density_expression_identity')
    if sp.expand((log_t-m).subs(m,sp.Rational(-67,25))-(log_t+sp.Rational(268,100)))!=0:
        raise a.ProofError('mean_parameter_identity')
    return {'formula':formula,'hypotheses':frozenset(),'parameters':values,'exponent_identity':str(exponent_a-exponent_b),'denominator_nonzero':['t>0','s>0','sqrt(2*pi)>0']}


def rejected(operation):
    try:
        operation()
    except (a.ProofError,r.ProofError):
        return True
    return False


def checks():
    results=[]
    def check(name,condition,formula=None,hypotheses=None):
        if not condition:
            raise a.ProofError(('check_failed',name))
        results.append({'id':name,'passed':True,'formula':formula,'hypotheses':sorted(hypotheses,key=repr) if hypotheses is not None else []})
    density=density_continuity()
    check('lognormal_continuous_on_every_positive_compact_interval',True,density['formula'],density['hypotheses'])
    limit=riemann_specialization(density)
    check('lognormal_right_riemann_limit_general',limit['formula']==r.sub_f(r.expected_riemann_formula(),'f',density_term()),limit['formula'],limit['hypotheses'])
    figure=figure_specialization()
    check('lognormal_right_riemann_limit_parameters',not figure['hypotheses'] and figure['formula'][0:2]==('all','epsilon'),figure['formula'],figure['hypotheses'])
    wrong=dict(density);wrong['density']=density['density'].replace(' / 2 ',' / 3 ')
    check('changed_exponent_cannot_reuse_continuity',rejected(lambda:riemann_specialization(wrong)))
    wrong=dict(density);wrong['proof']=h(density['formula'].removeprefix('|- '))
    check('assumed_continuity_cannot_replace_proof',rejected(lambda:riemann_specialization(wrong)))
    point=singleton_integral()
    expected='|- ( ( x e. { A } |-> ( F ` x ) ) e. L^1 /\\ S. { A } ( F ` x ) _d x = 0 )'
    check('singleton_integral_zero_general',a.infer(point)==(expected,frozenset({'|- A e. RR','|- F : RR --> RR'})),expected,a.infer(point)[1])
    return results


if __name__=='__main__':
    result=checks()
    print(json.dumps({'backend':'Python/Metamath-and-natural-deduction','checks':len(result),'passed':True,'results':result}))
