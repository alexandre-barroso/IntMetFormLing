import json
import sys
from pathlib import Path

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'capitulo_02'))
import analise_geral as a
from triplice import h,iff,part,as_real,as_complex
from ponte_analise import implies,positive_interval


def mapped_equality(domain,left,right,pointwise,condition):
    return a.unlift(a.mm('mpteq2dva',{'ph':'T.','x':'x','A':domain,'B':left,'C':right},(implies(condition,pointwise),)))


def constant_derivative_positive(value,value_complex):
    domain='RR+';global_function=f'( x e. RR |-> {value} )';zero_function='( x e. RR |-> 0 )'
    condition='|- ( T. /\\ x e. RR )'
    function=a.unlift(a.mm('fmpttd',{'ph':'T.','x':'x','A':'RR','B':value,'C':'CC'},(implies(condition,value_complex),)))
    derivative=a.unlift(a.mm('dvmptc',{'ph':'T.','S':'RR','x':'x','A':value},(a.lift(a.mm('reelprrecn')),a.lift(value_complex))))
    j='( TopOpen ` CCfld )';t='( topGen ` ran (,) )'
    restricted=a.mp(a.mm('dvres',{'K':j,'T':t,'S':'RR','F':global_function,'A':'RR','B':domain},(a.eqref(j),a.mm('tgioo4'))),a.both(a.both(a.mm('axresscn'),function),a.both(a.mm('ssid',{'A':'RR'}),a.mm('rpssre'))))
    restricted=a.rewrite(derivative,restricted)
    opened=a.rewrite(a.mm('ioorp'),a.mm('iooretop',{'A':'0','B':'+oo'}))
    interior=a.mp(a.mm('isopn3i',{'J':t,'S':domain}),a.both(a.mm('retop'),opened))
    restricted=a.rewrite(interior,restricted)
    for expression in (value,'0'):
        equality=a.mp(a.mm('resmpt',{'x':'x','A':'RR','B':domain,'C':expression}),a.mm('rpssre'))
        restricted=a.rewrite(equality,restricted)
    return restricted


def logarithm_map_derivative():
    domain='RR+';logf='( log |` RR+ )';expr='( log ` x )'
    lf=a.mp(a.mm('cncff',{'F':logf,'A':domain,'B':'RR'}),a.mm('relogcn'))
    lf=a.mp(a.mm('fss',{'F':logf,'A':domain,'B':'RR','C':'CC'}),a.both(lf,a.mm('axresscn')))
    equality=a.unlift(a.mm('feqmptd',{'ph':'T.','x':'x','F':logf,'A':domain,'B':'CC'},(a.lift(lf),)))
    condition='|- ( T. /\\ x e. RR+ )';member=part(a.assumption(condition),1)
    value=a.mp(a.mm('fvres',{'A':'x','B':domain,'F':'log'}),member)
    equality=a.rewrite(mapped_equality(domain,f'( {logf} ` x )',expr,value,condition),equality)
    return a.rewrite(equality,a.mm('dvrelog'))


def standardized_log_derivative():
    domain='RR+';condition='|- ( T. /\\ x e. RR+ )'
    member=part(a.assumption(condition),1)
    mr=h('M e. RR');sp=h('S e. RR+')
    mc=as_complex('M',mr);sr=as_real('S',sp);sc=as_complex('S',sr);snz=a.mp(a.mm('rpne0',{'A':'S'}),sp)
    logarithm='( log ` x )';difference=f'( {logarithm} - M )';reciprocal='( 1 / x )'
    lc=as_complex(logarithm,a.mp(a.mm('relogcl',{'A':'x'}),member))
    reciprocal_c=as_complex(reciprocal,as_real(reciprocal,a.mp(a.mm('rpreccl',{'A':'x'}),member)))
    sub=a.unlift(a.mm('dvmptsub',{'ph':'T.','S':'RR','x':'x','X':domain,'A':logarithm,'B':reciprocal,'C':'M','D':'0','V':'CC','W':'CC'},(a.lift(a.mm('reelprrecn')),implies(condition,lc),implies(condition,reciprocal_c),a.lift(logarithm_map_derivative()),implies(condition,mc),implies(condition,a.mm('0cn')),a.lift(constant_derivative_positive('M',mc)))))
    subzero=a.mp(a.mm('subid1',{'A':reciprocal}),reciprocal_c)
    sub=a.rewrite(mapped_equality(domain,f'( {reciprocal} - 0 )',reciprocal,subzero,condition),sub)
    inv='( 1 / S )';inv_c=as_complex(inv,as_real(inv,a.mp(a.mm('rpreccl',{'A':'S'}),sp)))
    diff_c=a.mp(a.mm('subcl',{'A':logarithm,'B':'M'}),a.both(lc,mc))
    scaled=a.unlift(a.mm('dvmptcmul',{'ph':'T.','S':'RR','x':'x','X':domain,'A':difference,'B':reciprocal,'C':inv,'V':'CC'},(a.lift(a.mm('reelprrecn')),implies(condition,diff_c),implies(condition,reciprocal_c),a.lift(sub),a.lift(inv_c))))
    quotient=f'( {difference} / S )'
    equal=a.mp(a.mm('divrec2',{'A':difference,'B':'S'}),a.both(diff_c,sc,snz))
    scaled=a.rewrite(mapped_equality(domain,f'( {inv} x. {difference} )',quotient,a.eqsym(equal),condition),scaled)
    xc=as_complex('x',as_real('x',member));xnz=a.mp(a.mm('rpne0',{'A':'x'}),member)
    rec_product=a.eqsym(a.mp(a.mm('divrec2',{'A':reciprocal,'B':'S'}),a.both(reciprocal_c,sc,snz)))
    nested=a.mp(a.mm('divdiv1',{'A':'1','B':'x','C':'S'}),a.both(a.mm('ax1cn'),a.both(xc,xnz),a.both(sc,snz)))
    rec_product=a.rewrite(nested,rec_product)
    rec_product=a.rewrite(a.mp(a.mm('mulcom',{'A':'x','B':'S'}),a.both(xc,sc)),rec_product)
    value='( 1 / ( S x. x ) )'
    scaled=a.rewrite(mapped_equality(domain,f'( {inv} x. {reciprocal} )',value,rec_product,condition),scaled)
    expected=f'|- ( RR _D ( x e. {domain} |-> {quotient} ) ) = ( x e. {domain} |-> {value} )'
    if a.infer(scaled)!=(expected,frozenset({'|- M e. RR','|- S e. RR+'})):
        raise a.ProofError(('standardized_log_derivative_scope',a.infer(scaled)))
    return scaled


def positive_root_two_pi():
    pi_p=iff(a.mm('elrp',{'A':'_pi'}),a.both(a.mm('pire'),a.mm('pipos')),1)
    prod=a.mp(a.mm('rpmulcl',{'A':'2','B':'_pi'}),a.both(a.mm('2rp'),pi_p))
    return a.mp(a.mm('rpsqrtcl',{'A':'( 2 x. _pi )'}),prod)


class ContinuousConstruction:
    def __init__(self,domain,subset,var='x'):
        self.domain=domain;self.subset=subset;self.var=var
        self.ccsubset=a.mm('sstri',{'A':domain,'B':'RR','C':'CC'},(subset,a.mm('axresscn')))
    def constant(self,value,proof,codomain='CC'):
        ss=a.mm('ssid',{'A':'CC'}) if codomain=='CC' else a.mm('difss',{'A':'CC','B':'{ 0 }'})
        return a.mp(a.mm('cncfmptc',{'x':self.var,'A':value,'S':self.domain,'T':codomain}),a.both(proof,self.ccsubset,ss))
    def binary(self,label,left,right,left_cn,right_cn):
        return a.unlift(a.mm(label,{'ph':'T.','x':self.var,'X':self.domain,'A':left,'B':right},(a.lift(left_cn),a.lift(right_cn))))
    def nonzero_constant(self,value,proof,nonzero):
        membership=iff(a.mm('eldifsn',{'A':value,'B':'CC','C':'0'}),a.both(proof,nonzero),1)
        return self.constant(value,membership,'( CC \\ { 0 } )')
    def nonzero_codomain(self,expression,cn,point_complex,point_nonzero):
        domain=self.domain;var=self.var;codomain='( CC \\ { 0 } )';function=f'( {var} e. {domain} |-> {expression} )'
        condition=f'|- ( T. /\\ {var} e. {domain} )'
        member=iff(a.mm('eldifsn',{'A':expression,'B':'CC','C':'0'}),a.both(point_complex,point_nonzero),1)
        f=a.unlift(a.mm('fmpttd',{'ph':'T.','x':var,'A':domain,'B':expression,'C':codomain},(implies(condition,member),)))
        return iff(a.mp(a.mm('cncfcdm',{'A':domain,'B':'CC','C':codomain,'F':function}),a.both(a.mm('difss',{'A':'CC','B':'{ 0 }'}),cn)),f,1)


def gaussian_continuity():
    domain='RR';var='u';builder=ContinuousConstruction(domain,a.mm('ssid',{'A':'RR'}),var)
    power='( u ^ 2 )';global_power='( u e. CC |-> ( u ^ 2 ) )'
    two_nn0=a.mm('2nn0')
    power_cn=a.mp(a.mm('expcncf',{'x':var,'N':'2'}),two_nn0)
    power_cn=a.mp(a.mp(a.mm('rescncf',{'A':'CC','B':'CC','C':domain,'F':global_power}),a.mm('axresscn')),power_cn)
    power_map=a.mp(a.mm('resmpt',{'x':var,'A':'CC','B':domain,'C':power}),a.mm('axresscn'))
    power_cn=a.rewrite(power_map,power_cn)
    negative=f'( 0 - {power} )'
    negative_cn=builder.binary('subcncf','0',power,builder.constant('0',a.mm('0cn')),power_cn)
    two_c=as_complex('2',as_real('2',a.mm('2rp')))
    two_nonzero=a.mp(a.mm('rpne0',{'A':'2'}),a.mm('2rp'))
    exponent=f'( {negative} / 2 )'
    exponent_cn=builder.binary('divcncf',negative,'2',negative_cn,builder.nonzero_constant('2',two_c,two_nonzero))
    exp=f'( exp ` {exponent} )'
    exp_cn=a.unlift(a.mm('cncfmpt1f',{'ph':'T.','x':var,'X':domain,'F':'exp','A':exponent},(a.lift(a.mm('efcn')),a.lift(exponent_cn))))
    root='( sqrt ` ( 2 x. _pi ) )';root_p=positive_root_two_pi();root_c=as_complex(root,as_real(root,root_p));root_nz=a.mp(a.mm('rpne0',{'A':root}),root_p)
    expression=f'( {exp} / {root} )'
    cn=builder.binary('divcncf',exp,root,exp_cn,builder.nonzero_constant(root,root_c,root_nz))
    expected=f'|- ( u e. RR |-> {expression} ) e. ( RR -cn-> CC )'
    if a.infer(cn)!=(expected,frozenset()):
        raise a.ProofError(('gaussian_continuity_scope',a.infer(cn)))
    return {'proof':cn,'expression':expression,'exponential_expression':exp,'root':root}


def standardized_log_closed_derivative():
    whole='( A [,] B )';inside='( A (,) B )';domain='RR+'
    quotient='( ( ( log ` x ) - M ) / S )';reciprocal='( 1 / ( S x. x ) )'
    global_function=f'( x e. {domain} |-> {quotient} )'
    condition='|- ( T. /\\ x e. RR+ )';xp=part(a.assumption(condition),1)
    sp=h('S e. RR+');sr=as_real('S',sp);snz=a.mp(a.mm('rpne0',{'A':'S'}),sp)
    lr=a.mp(a.mm('relogcl',{'A':'x'}),xp)
    difference_r=a.mp(a.mm('resubcl',{'A':'( log ` x )','B':'M'}),a.both(lr,h('M e. RR')))
    quotient_r=a.mp(a.mm('redivcl',{'A':'( ( log ` x ) - M )','B':'S'}),a.both(difference_r,sr,snz))
    quotient_c=as_complex(quotient,quotient_r)
    function=a.unlift(a.mm('fmpttd',{'ph':'T.','x':'x','A':domain,'B':quotient,'C':'CC'},(implies(condition,quotient_c),)))
    ar=as_real('A',h('A e. RR+'));br=h('B e. RR');whole_ss=a.mp(a.mm('iccssre'),a.both(ar,br))
    j='( TopOpen ` CCfld )';t='( topGen ` ran (,) )'
    restricted=a.mp(a.mm('dvres',{'K':j,'T':t,'S':'RR','F':global_function,'A':domain,'B':whole},(a.eqref(j),a.mm('tgioo4'))),a.both(a.both(a.mm('axresscn'),function),a.both(a.mm('rpssre'),whole_ss)))
    restricted=a.rewrite(standardized_log_derivative(),restricted)
    restricted=a.rewrite(a.mp(a.mm('iccntr'),a.both(ar,br)),restricted)
    left_map=a.mp(a.mm('resmpt',{'x':'x','A':domain,'B':whole,'C':quotient}),positive_interval())
    restricted=a.rewrite(left_map,restricted)
    inner_ss=a.mm('sstri',{'A':inside,'B':whole,'C':domain},(a.mm('ioossicc'),positive_interval()))
    right_map=a.mp(a.mm('resmpt',{'x':'x','A':domain,'B':inside,'C':reciprocal}),inner_ss)
    restricted=a.rewrite(right_map,restricted)
    expected=f'|- ( RR _D ( x e. {whole} |-> {quotient} ) ) = ( x e. {inside} |-> {reciprocal} )'
    hypotheses=frozenset({'|- A e. RR+','|- B e. RR','|- M e. RR','|- S e. RR+'})
    if a.infer(restricted)!=(expected,hypotheses):
        raise a.ProofError(('standardized_log_closed_derivative_scope',a.infer(restricted)))
    return restricted


def reciprocal_continuity_integrability():
    whole='( A [,] B )';inside='( A (,) B )';condition='|- ( T. /\\ x e. '+whole+' )'
    ar=as_real('A',h('A e. RR+'));br=h('B e. RR');ss=a.mp(a.mm('iccssre'),a.both(ar,br))
    builder=ContinuousConstruction(whole,ss)
    sp=h('S e. RR+');sc=as_complex('S',as_real('S',sp))
    idcn=a.mp(a.mm('cncfmptid',{'x':'x','S':whole,'T':'CC'}),a.both(builder.ccsubset,a.mm('ssid',{'A':'CC'})))
    denominator='( S x. x )'
    cn=builder.binary('mulcncf','S','x',builder.constant('S',sc),idcn)
    member=part(a.assumption(condition),1)
    xp=a.mm('sselii',{'A':whole,'B':'RR+','C':'x'},(positive_interval(),member))
    prod_p=a.mp(a.mm('rpmulcl',{'A':'S','B':'x'}),a.both(sp,xp))
    prod_c=as_complex(denominator,as_real(denominator,prod_p));prod_nz=a.mp(a.mm('rpne0',{'A':denominator}),prod_p)
    cn=builder.nonzero_codomain(denominator,cn,prod_c,prod_nz)
    expr=f'( 1 / {denominator} )'
    cn=builder.binary('divcncf','1',denominator,builder.constant('1',a.mm('ax1cn')),cn)
    function=f'( x e. {whole} |-> {expr} )';inside_function=f'( x e. {inside} |-> {expr} )'
    integrable=a.mp(a.mm('cniccibl',{'A':'A','B':'B','F':function}),a.both(ar,br,cn))
    valset=a.mm('ovex',{'A':'1','B':denominator,'F':'/'})
    restricted_integrable=a.unlift(a.mm('iblss',{'ph':'T.','x':'x','A':inside,'B':whole,'C':expr,'V':'_V'},(a.lift(a.mm('ioossicc')),a.lift(a.mm('ioombl')),implies(condition,valset),a.lift(integrable))))
    restricted_cn=a.mp(a.mp(a.mm('rescncf',{'A':whole,'B':'CC','C':inside,'F':function}),a.mm('ioossicc')),cn)
    equality=a.mp(a.mm('resmpt',{'x':'x','A':whole,'B':inside,'C':expr}),a.mm('ioossicc'))
    restricted_cn=a.rewrite(equality,restricted_cn)
    both=iff(a.mm('elin',{'A':inside_function,'B':f'( {inside} -cn-> CC )','C':'L^1'}),a.both(restricted_cn,restricted_integrable),1)
    expected=f'|- {inside_function} e. ( ( {inside} -cn-> CC ) i^i L^1 )'
    hypotheses=frozenset({'|- A e. RR+','|- B e. RR','|- S e. RR+'})
    if a.infer(both)!=(expected,hypotheses):
        raise a.ProofError(('reciprocal_continuity_integrability_scope',a.infer(both)))
    return both


def binary_congruence(equality,right,operator,left_slot=True):
    left,right_value=a.equality_parts(a.infer(equality)[0]);left=' '.join(left);right_value=' '.join(right_value)
    label='oveq1' if left_slot else 'oveq2'
    return a.mp(a.mm(label,{'A':left,'B':right_value,'C':right,'F':operator}),equality)


def function_congruence(equality,function):
    left,right=a.equality_parts(a.infer(equality)[0])
    return a.mp(a.mm('fveq2',{'A':' '.join(left),'B':' '.join(right),'F':function}),equality)


def standardized_endpoint(value):
    premise=f'|- x = {value}'
    equation=a.assumption(premise)
    equation=function_congruence(equation,'log')
    equation=binary_congruence(equation,'M','-')
    equation=binary_congruence(equation,'S','/')
    return implies(premise,equation)


def gaussian_composition(standardized):
    premise='|- u = '+standardized
    equation=a.assumption(premise)
    equation=binary_congruence(equation,'2','^')
    equation=binary_congruence(equation,'0','-',False)
    equation=binary_congruence(equation,'2','/')
    equation=function_congruence(equation,'exp')
    equation=binary_congruence(equation,'( sqrt ` ( 2 x. _pi ) )','/')
    return implies(premise,equation)


def standardized_real(value,positive):
    lr=a.mp(a.mm('relogcl',{'A':value}),positive)
    difference=f'( ( log ` {value} ) - M )'
    dr=a.mp(a.mm('resubcl',{'A':f'( log ` {value} )','B':'M'}),a.both(lr,h('M e. RR')))
    sr=as_real('S',h('S e. RR+'));snz=a.mp(a.mm('rpne0',{'A':'S'}),h('S e. RR+'))
    return a.mp(a.mm('redivcl',{'A':difference,'B':'S'}),a.both(dr,sr,snz))


def change_of_variables_oriented():
    from continuidade_geral import density_continuity
    whole='( A [,] B )';condition='|- ( T. /\\ x e. '+whole+' )'
    data=density_continuity();q=data['standardized_expression'];qcn=data['standardized_continuity_complex'];qfunction=f'( x e. {whole} |-> {q} )'
    member=part(a.assumption(condition),1)
    xp=a.mm('sselii',{'A':whole,'B':'RR+','C':'x'},(positive_interval(),member))
    qreal=standardized_real('x',xp)
    qfn=a.unlift(a.mm('fmpttd',{'ph':'T.','x':'x','A':whole,'B':q,'C':'RR'},(implies(condition,qreal),)))
    qcn=iff(a.mp(a.mm('cncfcdm',{'A':whole,'B':'CC','C':'RR','F':qfunction}),a.both(a.mm('axresscn'),qcn)),qfn,1)
    qcn=a.rewrite(a.eqsym(a.mm('ioomax')),qcn)
    gaussian=gaussian_continuity();gexpr=gaussian['expression']
    gcn=a.rewrite(a.eqsym(a.mm('ioomax')),gaussian['proof'])
    za='( ( ( log ` A ) - M ) / S )';zb='( ( ( log ` B ) - M ) / S )';derivative='( 1 / ( S x. x ) )'
    substituted=gexpr.replace('u',q)
    ar=as_real('A',h('A e. RR+'));br=h('B e. RR');order=h('A <_ B')
    result=a.unlift(a.mm('itgsubst',{'ph':'T.','x':'x','u':'u','X':'A','Y':'B','Z':'-oo','W':'+oo','A':q,'B':derivative,'C':gexpr,'E':substituted,'K':za,'L':zb},tuple(a.lift(p) for p in (ar,br,order,a.mm('mnfxr'),a.mm('pnfxr'),qcn,reciprocal_continuity_integrability(),gcn,standardized_log_closed_derivative()))+(gaussian_composition(q),standardized_endpoint('A'),standardized_endpoint('B'))))
    expected=f'|- S_ [ {za} -> {zb} ] {gexpr} _d u = S_ [ A -> B ] ( {substituted} x. {derivative} ) _d x'
    hypotheses=frozenset({'|- A e. RR+','|- B e. RR','|- A <_ B','|- M e. RR','|- S e. RR+'})
    if a.infer(result)!=(expected,hypotheses):
        raise a.ProofError(('change_of_variables_oriented_scope',a.infer(result)))
    return {'proof':result,'gaussian':gexpr,'composed':substituted,'derivative':derivative,'z_a':za,'z_b':zb,'density':data['density']}


def standardized_endpoints_order():
    ap=h('A e. RR+');br=h('B e. RR');order=h('A <_ B');mr=h('M e. RR');sp=h('S e. RR+')
    bp=a.mp(a.mm('rpgecl'),a.both(ap,br,order))
    la='( log ` A )';lb='( log ` B )';lr=a.mp(a.mm('relogcl',{'A':'A'}),ap);rr=a.mp(a.mm('relogcl',{'A':'B'}),bp)
    logorder=iff(a.mp(a.mm('logleb'),a.both(ap,bp)),order)
    shifted=iff(a.mp(a.mm('lesub1',{'A':la,'B':lb,'C':'M'}),a.both(lr,rr,mr)),logorder)
    da=f'( {la} - M )';db=f'( {lb} - M )'
    dar=a.mp(a.mm('resubcl',{'A':la,'B':'M'}),a.both(lr,mr));dbr=a.mp(a.mm('resubcl',{'A':lb,'B':'M'}),a.both(rr,mr))
    sr=as_real('S',sp);spos=a.mp(a.mm('rpgt0',{'A':'S'}),sp)
    result=iff(a.mp(a.mm('lediv1',{'A':da,'B':db,'C':'S'}),a.both(dar,dbr,a.both(sr,spos))),shifted)
    return result,standardized_real('A',ap),standardized_real('B',bp)


def substitution_integrand_identity(domain):
    condition=f'|- ( T. /\\ x e. {domain} )';member=part(a.assumption(condition),1)
    whole='( A [,] B )'
    ss=positive_interval() if domain==whole else a.mm('sstri',{'A':domain,'B':whole,'C':'RR+'},(a.mm('ioossicc'),positive_interval()))
    xp=a.mm('sselii',{'A':domain,'B':'RR+','C':'x'},(ss,member))
    sp=h('S e. RR+');sr=as_real('S',sp);sc=as_complex('S',sr);xc=as_complex('x',as_real('x',xp))
    root='( sqrt ` ( 2 x. _pi ) )';root_p=positive_root_two_pi();root_c=as_complex(root,as_real(root,root_p));root_nz=a.mp(a.mm('rpne0',{'A':root}),root_p)
    q='( ( ( log ` x ) - M ) / S )';q_c=as_complex(q,standardized_real('x',xp))
    square=f'( {q} ^ 2 )';sq_c=a.mp(a.mm('sqcl',{'A':q}),q_c)
    neg=f'( 0 - {square} )';neg_c=a.mp(a.mm('subcl',{'A':'0','B':square}),a.both(a.mm('0cn'),sq_c))
    two_c=as_complex('2',as_real('2',a.mm('2rp')));two_nz=a.mp(a.mm('rpne0',{'A':'2'}),a.mm('2rp'))
    exponent=f'( {neg} / 2 )';exp_c=a.mp(a.mm('divcl',{'A':neg,'B':'2'}),a.both(neg_c,two_c,two_nz))
    numerator=f'( exp ` {exponent} )';num_c=a.mp(a.mm('efcl',{'A':exponent}),exp_c)
    gaussian=f'( {numerator} / {root} )';g_c=a.mp(a.mm('divcl',{'A':numerator,'B':root}),a.both(num_c,root_c,root_nz))
    sx='( S x. x )';sx_p=a.mp(a.mm('rpmulcl',{'A':'S','B':'x'}),a.both(sp,xp));sx_c=as_complex(sx,as_real(sx,sx_p));sx_nz=a.mp(a.mm('rpne0',{'A':sx}),sx_p)
    inverse=f'( 1 / {sx} )';iv_c=a.mp(a.mm('divcl',{'A':'1','B':sx}),a.both(a.mm('ax1cn'),sx_c,sx_nz))
    product=f'( {gaussian} x. {inverse} )';product_c=a.mp(a.mm('mulcl',{'A':gaussian,'B':inverse}),a.both(g_c,iv_c))
    identity=a.mp(a.mm('mulcom',{'A':gaussian,'B':inverse}),a.both(g_c,iv_c))
    division=a.mp(a.mm('divrec2',{'A':gaussian,'B':sx}),a.both(g_c,sx_c,sx_nz))
    identity=a.rewrite(a.eqsym(division),identity)
    double=a.mp(a.mm('divdiv1',{'A':numerator,'B':root,'C':sx}),a.both(num_c,a.both(root_c,root_nz),a.both(sx_c,sx_nz)))
    identity=a.rewrite(double,identity)
    first=a.mp(a.mm('mulcom',{'A':root,'B':sx}),a.both(root_c,sx_c));identity=a.rewrite(first,identity)
    second=a.mp(a.mm('mul32',{'A':'S','B':'x','C':root}),a.both(sc,xc,root_c));identity=a.rewrite(second,identity)
    sroot=f'( S x. {root} )';sr_c=a.mp(a.mm('mulcl',{'A':'S','B':root}),a.both(sc,root_c))
    third=a.mp(a.mm('mulcom',{'A':sroot,'B':'x'}),a.both(sr_c,xc));identity=a.rewrite(third,identity)
    density=f'( {numerator} / ( x x. {sroot} ) )'
    expected=f'|- {product} = {density}'
    if a.infer(identity)[0]!=expected:
        raise a.ProofError(('substitution_integrand_identity_expression',a.infer(identity)))
    return {'proof':implies(condition,identity),'density_complex':implies(condition,a.rewrite(identity,product_c)),'density':density,'product':product}


def lognormal_change_of_variables():
    data=change_of_variables_oriented();result=data['proof'];za=data['z_a'];zb=data['z_b'];gaussian=data['gaussian'];derivative=data['derivative'];composed=data['composed']
    order,zar,zbr=standardized_endpoints_order();ar=as_real('A',h('A e. RR+'));br=h('B e. RR');hab=h('A <_ B')
    left=a.unlift(a.mm('ditgpos',{'ph':'T.','x':'u','A':za,'B':zb,'C':gaussian},(a.lift(order),)))
    right=a.unlift(a.mm('ditgpos',{'ph':'T.','x':'x','A':'A','B':'B','C':f'( {composed} x. {derivative} )'},(a.lift(hab),)))
    result=a.rewrite(left,result);result=a.rewrite(right,result)
    gaussian_data=gaussian_continuity();function=f'( u e. RR |-> {gaussian} )';gf=a.mp(a.mm('cncff',{'F':function,'A':'RR','B':'CC'}),gaussian_data['proof'])
    domain=f'( {za} [,] {zb} )';condition=f'|- ( T. /\\ u e. {domain} )';member=part(a.assumption(condition),1)
    uss=a.mp(a.mm('iccssre',{'A':za,'B':zb}),a.both(zar,zbr));ur=a.mm('sselii',{'A':domain,'B':'RR','C':'u'},(uss,member))
    fvalue=a.mp(a.mm('ffvelcdm',{'F':function,'A':'RR','B':'CC','C':'u'}),a.both(gf,ur))
    value=a.mp(a.mm('fvmpt2',{'x':'u','A':'RR','B':gaussian,'C':'_V','F':function},(a.eqref(function),)),a.both(ur,a.mm('ovex',{'A':gaussian_data['exponential_expression'],'B':gaussian_data['root'],'F':'/'})))
    gc=a.mm('eqeltrri',{'A':f'( {function} ` u )','B':gaussian,'C':'CC'},(value,fvalue))
    closed_gaussian=a.unlift(a.mm('itgioo',{'ph':'T.','x':'u','A':za,'B':zb,'C':gaussian},(a.lift(zar),a.lift(zbr),implies(condition,gc))))
    result=a.rewrite(closed_gaussian,result)
    inner=substitution_integrand_identity('( A (,) B )')
    integrand=a.unlift(a.mm('itgeq2dv',{'ph':'T.','x':'x','A':'( A (,) B )','B':inner['product'],'C':inner['density']},(inner['proof'],)))
    result=a.rewrite(integrand,result)
    whole=substitution_integrand_identity('( A [,] B )')
    closed_density=a.unlift(a.mm('itgioo',{'ph':'T.','x':'x','A':'A','B':'B','C':whole['density']},(a.lift(ar),a.lift(br),whole['density_complex'])))
    result=a.eqsym(a.rewrite(closed_density,result))
    expected=f'|- S. ( A [,] B ) {data["density"]} _d x = S. ( {za} [,] {zb} ) {gaussian} _d u'
    hypotheses=frozenset({'|- A e. RR+','|- B e. RR','|- A <_ B','|- M e. RR','|- S e. RR+'})
    if a.infer(result)!=(expected,hypotheses):
        raise a.ProofError(('lognormal_change_of_variables_scope',a.infer(result)))
    return result


def certificates():
    return {'standardized_log_derivative':standardized_log_derivative(),'gaussian_continuity':gaussian_continuity()['proof'],'standardized_log_closed_derivative':standardized_log_closed_derivative(),'reciprocal_continuity_integrability':reciprocal_continuity_integrability(),'change_of_variables_oriented':change_of_variables_oriented()['proof'],'lognormal_change_of_variables':lognormal_change_of_variables()}



EXPECTED_INTERFACES = {'standardized_log_derivative': ('|- ( RR _D ( x e. RR+ |-> ( ( ( log ` x ) - M ) / S ) ) ) = ( x e. RR+ |-> '
                                 '( 1 / ( S x. x ) ) )',
                                 ('|- M e. RR', '|- S e. RR+')),
 'gaussian_continuity': ('|- ( u e. RR |-> ( ( exp ` ( ( 0 - ( u ^ 2 ) ) / 2 ) ) / ( sqrt ` ( 2 x. _pi ) ) ) '
                         ') e. ( RR -cn-> CC )',
                         ()),
 'standardized_log_closed_derivative': ('|- ( RR _D ( x e. ( A [,] B ) |-> ( ( ( log ` x ) - M ) / S ) ) ) = '
                                        '( x e. ( A (,) B ) |-> ( 1 / ( S x. x ) ) )',
                                        ('|- A e. RR+', '|- B e. RR', '|- M e. RR', '|- S e. RR+')),
 'reciprocal_continuity_integrability': ('|- ( x e. ( A (,) B ) |-> ( 1 / ( S x. x ) ) ) e. ( ( ( A (,) B ) '
                                         '-cn-> CC ) i^i L^1 )',
                                         ('|- A e. RR+', '|- B e. RR', '|- S e. RR+')),
 'change_of_variables_oriented': ('|- S_ [ ( ( ( log ` A ) - M ) / S ) -> ( ( ( log ` B ) - M ) / S ) ] ( ( '
                                  'exp ` ( ( 0 - ( u ^ 2 ) ) / 2 ) ) / ( sqrt ` ( 2 x. _pi ) ) ) _d u = S_ [ '
                                  'A -> B ] ( ( ( exp ` ( ( 0 - ( ( ( ( log ` x ) - M ) / S ) ^ 2 ) ) / 2 ) '
                                  ') / ( sqrt ` ( 2 x. _pi ) ) ) x. ( 1 / ( S x. x ) ) ) _d x',
                                  ('|- A <_ B', '|- A e. RR+', '|- B e. RR', '|- M e. RR', '|- S e. RR+')),
 'lognormal_change_of_variables': ('|- S. ( A [,] B ) ( ( exp ` ( ( 0 - ( ( ( ( log ` x ) - M ) / S ) ^ 2 ) '
                                   ') / 2 ) ) / ( x x. ( S x. ( sqrt ` ( 2 x. _pi ) ) ) ) ) _d x = S. ( ( ( '
                                   '( log ` A ) - M ) / S ) [,] ( ( ( log ` B ) - M ) / S ) ) ( ( exp ` ( ( '
                                   '0 - ( u ^ 2 ) ) / 2 ) ) / ( sqrt ` ( 2 x. _pi ) ) ) _d u',
                                   ('|- A <_ B', '|- A e. RR+', '|- B e. RR', '|- M e. RR', '|- S e. RR+'))}

def checks():
    results=[]
    proofs=certificates()
    def check(name):
        formula,hypotheses=a.infer(proofs[name])
        expected,required=EXPECTED_INTERFACES[name]
        if formula!=expected or hypotheses!=frozenset(required):
            raise a.ProofError(('certificate_scope',name))
        results.append({'id':name,'passed':True,'formula':formula,'hypotheses':sorted(hypotheses)})
    check('standardized_log_derivative')
    check('gaussian_continuity')
    check('standardized_log_closed_derivative')
    check('reciprocal_continuity_integrability')
    check('change_of_variables_oriented')
    check('lognormal_change_of_variables')
    return results


if __name__=='__main__':
    results=checks()
    print(json.dumps({'backend':'Python/Metamath','checks':len(results),'passed':True,'results':results}))
