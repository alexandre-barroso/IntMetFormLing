from pathlib import Path
import json
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from capitulo_07 import probabilidade_geral as p
from capitulo_07 import momentos_algebra as algebra

RVLIST=('List',p.FUNCTION)
NIL=p.C('list_nil',RVLIST)
CONS=p.C('list_cons',p.FT(p.FUNCTION,p.FT(RVLIST,RVLIST)))
TOTAL=p.C('random_variable_list_sum',p.FT(RVLIST,p.FUNCTION))
COUNT=p.C('random_variable_list_real_length',p.FT(RVLIST,'R'))
ALL_L2=p.C('random_variable_list_l2',p.FT(RVLIST,'Prop'))
PAIRWISE=p.C('random_variable_list_pairwise_independent',p.FT(RVLIST,'Prop'))
EACH_INDEPENDENT=p.C('random_variable_independent_of_each',p.FT(p.FUNCTION,p.FT(RVLIST,'Prop')))
COMMON=p.C('random_variable_list_common_variance',p.FT(RVLIST,p.FT('R','Prop')))
CENTERED_COMMON=p.C('random_variable_list_common_centered_variance',p.FT(RVLIST,p.FT('R','Prop')))
VARIANCE_TOTAL=p.C('random_variable_list_variance_sum',p.FT(RVLIST,'R'))
RTWO=p.Add(p.RONE,p.RONE)
RMINUSONE=p.Sub(p.RZERO,p.RONE)


def total(xs):
    return p.A(TOTAL,xs)


def count(xs):
    return p.A(COUNT,xs)


def variance_total(xs):
    return p.A(VARIANCE_TOTAL,xs)


def moment_variance(f):
    return p.Sub(p.expectation(p.square_function(f)),p.Mul(p.expectation(f),p.expectation(f)))


def centered(f):
    return p.subtract_function(f,p.constant_function(p.expectation(f)))


def variance(f):
    return p.expectation(p.square_function(centered(f)))


def covariance(f,g):
    return p.expectation(p.product_function(centered(f),centered(g)))


def foundations():
    f,g=p.V('function',p.FUNCTION),p.V('other_function',p.FUNCTION)
    h,t=p.V('list_head',p.FUNCTION),p.V('list_tail',RVLIST)
    v,a=p.V('variance_value','R'),p.V('real_value','R')
    x=p.V('extensional_point',p.OMEGA)
    cons=p.A(CONS,h,t)
    return {
        'moment_function_extensionality':p.alls((f,g),p.Imp(p.All(x,p.Eq(p.A(f,x),p.A(g,x))),p.Eq(f,g))),
        'moment_total_nil':p.Eq(total(NIL),p.constant_function(p.RZERO)),
        'moment_total_cons':p.alls((h,t),p.Eq(total(cons),p.add_function(h,total(t)))),
        'moment_count_nil':p.Eq(count(NIL),p.RZERO),
        'moment_count_cons':p.alls((h,t),p.Eq(count(cons),p.Add(p.RONE,count(t)))),
        'moment_l2_nil':p.A(ALL_L2,NIL),
        'moment_l2_cons':p.alls((h,t),p.Iff(p.A(ALL_L2,cons),p.And(p.square_integrable(h),p.A(ALL_L2,t)))),
        'moment_pairwise_nil':p.A(PAIRWISE,NIL),
        'moment_pairwise_cons':p.alls((h,t),p.Iff(p.A(PAIRWISE,cons),p.And(p.A(EACH_INDEPENDENT,h,t),p.A(PAIRWISE,t)))),
        'moment_each_nil':p.All(f,p.A(EACH_INDEPENDENT,f,NIL)),
        'moment_each_cons':p.alls((f,h,t),p.Iff(p.A(EACH_INDEPENDENT,f,cons),p.And(p.independent_functions(f,h),p.A(EACH_INDEPENDENT,f,t)))),
        'moment_common_nil':p.All(v,p.A(COMMON,NIL,v)),
        'moment_common_cons':p.alls((h,t,v),p.Iff(p.A(COMMON,cons,v),p.And(p.Eq(moment_variance(h),v),p.A(COMMON,t,v)))),
        'moment_centered_common_nil':p.All(v,p.A(CENTERED_COMMON,NIL,v)),
        'moment_centered_common_cons':p.alls((h,t,v),p.Iff(p.A(CENTERED_COMMON,cons,v),p.And(p.Eq(variance(h),v),p.A(CENTERED_COMMON,t,v)))),
        'moment_variance_total_nil':p.Eq(variance_total(NIL),p.RZERO),
        'moment_variance_total_cons':p.alls((h,t),p.Eq(variance_total(cons),p.Add(variance(h),variance_total(t)))),
        'moment_positive_reciprocal':p.All(a,p.Imp(p.Lt(p.RZERO,a),p.Eq(p.Mul(p.Div(p.RONE,a),a),p.RONE))),
        'moment_positive_division_factor':p.alls((v,a),p.Imp(p.Lt(p.RZERO,a),p.Eq(p.Div(v,a),p.Mul(v,p.Div(p.RONE,a))))),
        'moment_positive_reciprocal_square':p.All(a,p.Imp(p.Lt(p.RZERO,a),p.Eq(p.Mul(p.Div(p.RONE,a),p.Div(p.RONE,a)),p.Div(p.RONE,p.Mul(a,a)))))
    }


def use(kernel,name,*terms):
    return p.instantiate(('ref' if name in kernel.verified else 'axiom',name),*terms)


def conclusion(kernel,proof):
    return kernel.infer(proof).conclusion


def literal(kernel,name,*terms):
    return p.instantiate(('axiom',name),*terms)


def signed(kernel,f,value,proof,target):
    point=p.V('integrand_identity_point',p.OMEGA)
    equality=p.close(p.ring(p.A(f,point),p.A(target,point)),(point,))
    equality=p.apply(literal(kernel,'moment_function_extensionality',f,target),equality)
    placeholder=p.V('integrand_placeholder',p.FUNCTION)
    return ('eq_e',equality,placeholder,p.has_signed_integral(placeholder,value),proof)


def linear_integral(kernel,terms,constant=p.RZERO):
    f=p.constant_function(constant)
    value=constant
    proof=use(kernel,'constant_signed_integral',constant)
    for coefficient,term,term_value,term_proof in terms:
        scaled=p.scale_function(coefficient,term)
        scaled_value=p.Mul(coefficient,term_value)
        scaled_proof=p.apply(use(kernel,'signed_integral_scale',term,term_value,coefficient),term_proof)
        proof=p.apply(use(kernel,'signed_integral_add',f,scaled,value,scaled_value),proof,scaled_proof)
        f=p.add_function(f,scaled)
        value=p.Add(value,scaled_value)
    return f,value,proof


def normalize_integral(kernel,f,value,proof,target,target_value):
    proof=signed(kernel,f,value,proof,target)
    placeholder=p.V('integral_value_placeholder','R')
    return ('eq_e',p.ring(value,target_value),placeholder,p.has_signed_integral(target,placeholder),proof)


def expectation_from(kernel,f,value,proof):
    return p.apply(use(kernel,'expectation_of_signed_integral',f,value),proof)


def integral_self_value(kernel,f,value,proof):
    equality=expectation_from(kernel,f,value,proof)
    placeholder=p.V('expected_value_placeholder','R')
    return ('eq_e',p.symmetric(p.expectation(f),value,equality),placeholder,p.has_signed_integral(f,placeholder),proof)


def l2_integral(kernel,f,hypothesis):
    return p.apply(use(kernel,'l2_implies_integrable',f),hypothesis)


def l2_square(kernel,f,hypothesis):
    return p.apply(use(kernel,'l2_square_signed_integral',f),hypothesis)


def independent_product(kernel,f,g,hf,hg,independence):
    return p.apply(use(kernel,'independent_l2_product_integral',f,g),hf,hg,independence)


def unfold_conjunction(kernel,name,terms,hypothesis):
    return p.apply(('and_l',literal(kernel,name,*terms)),hypothesis)


def derive_centered_identities(kernel):
    f,g=p.V('center_f',p.FUNCTION),p.V('center_g',p.FUNCTION)
    sf,sg,sfg=p.V('first_moment','R'),p.V('other_first_moment','R'),p.V('cross_moment','R')
    conditions=(p.has_signed_integral(f,sf),p.has_signed_integral(g,sg),p.has_signed_integral(p.product_function(f,g),sfg))
    hf,hg,hfg=map(p.hyp,conditions)
    ef,eg=expectation_from(kernel,f,sf,hf),expectation_from(kernel,g,sg,hg)
    terms=[(p.RONE,p.product_function(f,g),sfg,hfg),(p.Sub(p.RZERO,sg),f,sf,hf),(p.Sub(p.RZERO,sf),g,sg,hg)]
    fun,value,proof=linear_integral(kernel,terms,p.Mul(sf,sg))
    target=p.product_function(p.subtract_function(f,p.constant_function(sf)),p.subtract_function(g,p.constant_function(sg)))
    wanted=p.Sub(sfg,p.Mul(sf,sg))
    proof=normalize_integral(kernel,fun,value,proof,target,wanted)
    answer=expectation_from(kernel,target,wanted,proof)
    answer=p.rewrite(kernel,answer,ef,True)
    answer=p.rewrite(kernel,answer,eg,True)
    target_formula=p.Eq(covariance(f,g),p.Sub(sfg,p.Mul(p.expectation(f),p.expectation(g))))
    answer=('conversion',target_formula,answer)
    formula=p.alls((f,g,sf,sg,sfg),p.imps(conditions,target_formula))
    kernel.theorem('covariance_from_signed_moments',formula,p.close(answer,(f,g,sf,sg,sfg),conditions))
    f2=p.square_function(f)
    conditions2=(p.has_signed_integral(f,sf),p.has_signed_integral(f2,sfg))
    answer=p.apply(p.ref('covariance_from_signed_moments',f,f,sf,sf,sfg),p.hyp(conditions2[0]),p.hyp(conditions2[0]),p.hyp(conditions2[1]))
    target2=p.Eq(variance(f),p.Sub(sfg,p.Mul(p.expectation(f),p.expectation(f))))
    answer=('conversion',target2,answer)
    kernel.theorem('variance_from_signed_moments',p.alls((f,sf,sfg),p.imps(conditions2,target2)),p.close(answer,(f,sf,sfg),conditions2))
    l2=p.square_integrable(f)
    answer=p.apply(p.ref('variance_from_signed_moments',f,p.expectation(f),p.expectation(f2)),l2_integral(kernel,f,p.hyp(l2)),l2_square(kernel,f,p.hyp(l2)))
    kernel.theorem('l2_variance_definition_bridge',p.All(f,p.Imp(l2,p.Eq(variance(f),moment_variance(f)))),p.close(answer,(f,),(l2,)))


def derive_sum_integral(kernel):
    xs,h,t=p.V('sum_list',RVLIST),p.V('sum_head',p.FUNCTION),p.V('sum_tail',RVLIST)
    body=p.Imp(p.A(ALL_L2,xs),p.integrable(total(xs)))
    base_integral=use(kernel,'constant_signed_integral',p.RZERO)
    base_integral=p.rewrite(kernel,base_integral,literal(kernel,'moment_total_nil'),True)
    base=integral_self_value(kernel,total(NIL),p.RZERO,base_integral)
    base=p.close(base,assumptions=(p.A(ALL_L2,NIL),))
    cons=p.A(CONS,h,t);condition=p.A(ALL_L2,cons)
    decomposed=unfold_conjunction(kernel,'moment_l2_cons',(h,t),p.hyp(condition))
    ih=p.substitute(body,xs,t)
    ht=p.apply(p.hyp(ih),('and_r',decomposed))
    hh=l2_integral(kernel,h,('and_l',decomposed))
    value=p.Add(p.expectation(h),p.expectation(total(t)))
    step=p.apply(use(kernel,'signed_integral_add',h,total(t),p.expectation(h),p.expectation(total(t))),hh,ht)
    step=p.rewrite(kernel,step,literal(kernel,'moment_total_cons',h,t),True)
    step=integral_self_value(kernel,total(cons),value,step)
    step=p.close(step,(h,t),(ih,condition))
    proof=('list_induction',xs,h,t,body,base,step)
    kernel.theorem('l2_list_sum_integrable',p.All(xs,body),proof)


def derive_product_with_sum(kernel):
    xs,h,t=p.V('product_list',RVLIST),p.V('product_head',p.FUNCTION),p.V('product_tail',RVLIST)
    f=p.V('outside_function',p.FUNCTION)
    def predicate(seq):
        conditions=(p.square_integrable(f),p.A(ALL_L2,seq),p.A(EACH_INDEPENDENT,f,seq))
        return p.All(f,p.imps(conditions,p.has_signed_integral(p.product_function(f,total(seq)),p.Mul(p.expectation(f),p.expectation(total(seq))))))
    conditions0=(p.square_integrable(f),p.A(ALL_L2,NIL),p.A(EACH_INDEPENDENT,f,NIL))
    zero=p.constant_function(p.RZERO)
    proof=normalize_integral(kernel,zero,p.RZERO,use(kernel,'constant_signed_integral',p.RZERO),p.product_function(f,zero),p.RZERO)
    proof=p.rewrite(kernel,proof,literal(kernel,'moment_total_nil'),True)
    integral0=p.rewrite(kernel,use(kernel,'constant_signed_integral',p.RZERO),literal(kernel,'moment_total_nil'),True)
    expected0=expectation_from(kernel,total(NIL),p.RZERO,integral0)
    placeholder=p.V('zero_expected_placeholder','R')
    proof=('eq_e',p.ring(p.RZERO,p.Mul(p.expectation(f),p.RZERO)),placeholder,p.has_signed_integral(p.product_function(f,total(NIL)),placeholder),proof)
    proof=p.rewrite(kernel,proof,expected0,True)
    base=p.close(proof,(f,),conditions0)
    cons=p.A(CONS,h,t)
    conditions=(p.square_integrable(f),p.A(ALL_L2,cons),p.A(EACH_INDEPENDENT,f,cons))
    lf,ls,ind=map(p.hyp,conditions)
    ls=unfold_conjunction(kernel,'moment_l2_cons',(h,t),ls)
    ind=unfold_conjunction(kernel,'moment_each_cons',(f,h,t),ind)
    head=independent_product(kernel,f,h,lf,('and_l',ls),('and_l',ind))
    tail=p.apply(p.instantiate(p.hyp(predicate(t)),f),lf,('and_r',ls),('and_r',ind))
    sf,sh,st=p.expectation(f),p.expectation(h),p.expectation(total(t))
    fun,value,proof=linear_integral(kernel,[(p.RONE,p.product_function(f,h),p.Mul(sf,sh),head),(p.RONE,p.product_function(f,total(t)),p.Mul(sf,st),tail)])
    target=p.product_function(f,p.add_function(h,total(t)))
    wanted=p.Mul(sf,p.Add(sh,st))
    proof=normalize_integral(kernel,fun,value,proof,target,wanted)
    proof=p.rewrite(kernel,proof,literal(kernel,'moment_total_cons',h,t),True)
    ht=p.apply(p.ref('l2_list_sum_integrable',t),('and_r',ls))
    hh=l2_integral(kernel,h,('and_l',ls))
    si=p.apply(use(kernel,'signed_integral_add',h,total(t),sh,st),hh,ht)
    si=p.rewrite(kernel,si,literal(kernel,'moment_total_cons',h,t),True)
    es=expectation_from(kernel,total(cons),p.Add(sh,st),si)
    proof=p.rewrite(kernel,proof,es,True)
    step=p.close(proof,(f,),conditions)
    step=p.close(step,(h,t),(predicate(t),))
    body=predicate(xs)
    kernel.theorem('independent_product_with_finite_sum',p.All(xs,body),('list_induction',xs,h,t,body,base,step))


def algebra_under(kernel,left,right,equalities):
    def reduce(original):
        proof=('eq_i',original)
        current=original
        for index,equality in enumerate(equalities):
            old,new=conclusion(kernel,equality)[1:]
            placeholder=p.V('algebra_replacement_'+str(index),p.sort_of(old))
            pattern=p.replace_subterm(current,old,placeholder)
            if pattern==current:
                continue
            proof=('eq_e',equality,placeholder,p.Eq(original,pattern),proof)
            current=p.substitute(pattern,placeholder,new)
        return current,proof
    reduced_left,left_proof=reduce(left)
    reduced_right,right_proof=reduce(right)
    middle=p.ring(reduced_left,reduced_right)
    first=p.eq_trans(left,reduced_left,reduced_right,left_proof,middle)
    return p.eq_trans(left,reduced_right,right,first,p.symmetric(right,reduced_right,right_proof))


def change_value(kernel,f,old,new,proof,equality):
    placeholder=p.V('changed_integral_value','R')
    if not p.same(conclusion(kernel,equality),p.Eq(old,new)):
        raise ValueError('wrong integral value equality')
    return ('eq_e',equality,placeholder,p.has_signed_integral(f,placeholder),proof)


def derive_common_variance_sum(kernel):
    xs,h,t=p.V('variance_list',RVLIST),p.V('variance_head',p.FUNCTION),p.V('variance_tail',RVLIST)
    v=p.V('common_variance','R')
    def wanted(seq):
        return p.Add(p.Mul(p.expectation(total(seq)),p.expectation(total(seq))),p.Mul(count(seq),v))
    def conditions(seq):
        return (p.A(ALL_L2,seq),p.A(PAIRWISE,seq),p.A(COMMON,seq,v))
    def predicate(seq):
        return p.All(v,p.imps(conditions(seq),p.has_signed_integral(p.square_function(total(seq)),wanted(seq))))
    zero=p.constant_function(p.RZERO)
    zero_integral=use(kernel,'constant_signed_integral',p.RZERO)
    base=normalize_integral(kernel,zero,p.RZERO,zero_integral,p.square_function(zero),p.RZERO)
    base=p.rewrite(kernel,base,literal(kernel,'moment_total_nil'),True)
    total0=p.rewrite(kernel,zero_integral,literal(kernel,'moment_total_nil'),True)
    expected0=expectation_from(kernel,total(NIL),p.RZERO,total0)
    base=change_value(kernel,p.square_function(total(NIL)),p.RZERO,wanted(NIL),base,algebra_under(kernel,p.RZERO,wanted(NIL),(expected0,literal(kernel,'moment_count_nil'))))
    base=p.close(base,(v,),conditions(NIL))
    cons=p.A(CONS,h,t)
    ls,ind,common=map(p.hyp,conditions(cons))
    ls=unfold_conjunction(kernel,'moment_l2_cons',(h,t),ls)
    ind=unfold_conjunction(kernel,'moment_pairwise_cons',(h,t),ind)
    common=unfold_conjunction(kernel,'moment_common_cons',(h,t,v),common)
    hh=l2_integral(kernel,h,('and_l',ls))
    ht=p.apply(p.ref('l2_list_sum_integrable',t),('and_r',ls))
    hsquare=l2_square(kernel,h,('and_l',ls))
    tsquare=p.apply(p.instantiate(p.hyp(predicate(t)),v),('and_r',ls),('and_r',ind),('and_r',common))
    cross=p.apply(p.ref('independent_product_with_finite_sum',t,h),('and_l',ls),('and_r',ls),('and_l',ind))
    eh,et=p.expectation(h),p.expectation(total(t))
    eh2=p.expectation(p.square_function(h))
    fun,value,proof=linear_integral(kernel,[(p.RONE,p.square_function(h),eh2,hsquare),(RTWO,p.product_function(h,total(t)),p.Mul(eh,et),cross),(p.RONE,p.square_function(total(t)),wanted(t),tsquare)])
    expanded=p.square_function(p.add_function(h,total(t)))
    proof=signed(kernel,fun,value,proof,expanded)
    proof=p.rewrite(kernel,proof,literal(kernel,'moment_total_cons',h,t),True)
    common_head=('and_l',common)
    head_square_value=p.Add(v,p.Mul(eh,eh))
    common_equation=p.ring(eh2,p.Add(p.Sub(eh2,p.Mul(eh,eh)),p.Mul(eh,eh)))
    common_equation=p.rewrite(kernel,common_equation,common_head)
    sum_integral=p.apply(use(kernel,'signed_integral_add',h,total(t),eh,et),hh,ht)
    sum_integral=p.rewrite(kernel,sum_integral,literal(kernel,'moment_total_cons',h,t),True)
    expected_sum=expectation_from(kernel,total(cons),p.Add(eh,et),sum_integral)
    equality=algebra_under(kernel,value,wanted(cons),(common_equation,expected_sum,literal(kernel,'moment_count_cons',h,t)))
    proof=change_value(kernel,p.square_function(total(cons)),value,wanted(cons),proof,equality)
    step=p.close(p.close(proof,(v,),conditions(cons)),(h,t),(predicate(t),))
    body=predicate(xs)
    kernel.theorem('independent_common_variance_sum_moment',p.All(xs,body),('list_induction',xs,h,t,body,base,step))


def derive_mean_variance(kernel):
    xs=p.V('observations',RVLIST);v=p.V('population_variance','R')
    n=count(xs);s=total(xs);es=p.expectation(s)
    q=p.Div(p.RONE,n);mean=p.scale_function(q,s)
    conditions=(p.A(ALL_L2,xs),p.A(PAIRWISE,xs),p.A(COMMON,xs,v),p.Lt(p.RZERO,n))
    ll,ind,cv,pos=map(p.hyp,conditions)
    first=p.apply(p.ref('l2_list_sum_integrable',xs),ll)
    second_value=p.Add(p.Mul(es,es),p.Mul(n,v))
    second=p.apply(p.ref('independent_common_variance_sum_moment',xs,v),ll,ind,cv)
    mean_first=p.apply(use(kernel,'signed_integral_scale',s,es,q),first)
    mean_first_value=p.Mul(q,es)
    square_scale=p.Mul(q,q)
    scaled_square=p.scale_function(square_scale,p.square_function(s))
    mean_second_value=p.Mul(square_scale,second_value)
    mean_second=p.apply(use(kernel,'signed_integral_scale',p.square_function(s),second_value,square_scale),second)
    mean_second=signed(kernel,scaled_square,mean_second_value,mean_second,p.square_function(mean))
    answer=p.apply(p.ref('variance_from_signed_moments',mean,mean_first_value,mean_second_value),mean_first,mean_second)
    emean=expectation_from(kernel,mean,mean_first_value,mean_first)
    result=p.Div(v,n)
    current=conclusion(kernel,answer)[2]
    expanded=p.Mul(p.Mul(q,n),p.Mul(q,v))
    equality=algebra_under(kernel,current,expanded,(emean,))
    inverse=p.apply(literal(kernel,'moment_positive_reciprocal',n),pos)
    factor=p.apply(literal(kernel,'moment_positive_division_factor',v,n),pos)
    equality=p.rewrite(kernel,equality,inverse)
    tail=algebra_under(kernel,conclusion(kernel,equality)[2],result,(factor,))
    final_equality=p.eq_trans(current,conclusion(kernel,equality)[2],result,equality,tail)
    answer=p.eq_trans(variance(mean),current,result,answer,final_equality)
    formula=p.alls((xs,v),p.imps(conditions,p.Eq(variance(mean),result)))
    kernel.theorem('variance_of_mean_for_arbitrary_nonempty_finite_sample',formula,p.close(answer,(xs,v),conditions))


def derive_centered_independent_product(kernel):
    f,g=p.V('centered_left',p.FUNCTION),p.V('centered_right',p.FUNCTION)
    conditions=(p.square_integrable(f),p.square_integrable(g),p.independent_functions(f,g),p.Eq(p.expectation(f),p.RZERO),p.Eq(p.expectation(g),p.RZERO))
    hf,hg,ind,ef,eg=map(p.hyp,conditions)
    product=p.product_function(f,g)
    value=p.Mul(p.expectation(f),p.expectation(g))
    proof=independent_product(kernel,f,g,hf,hg,ind)
    equality=algebra_under(kernel,value,p.RZERO,(ef,eg))
    proof=change_value(kernel,product,value,p.RZERO,proof,equality)
    answer=expectation_from(kernel,product,p.RZERO,proof)
    kernel.theorem('centered_independent_cross_moment_zero',p.alls((f,g),p.imps(conditions,p.Eq(p.expectation(product),p.RZERO))),p.close(answer,(f,g),conditions))


def derive_centered_common_bridge(kernel):
    xs,h,t=p.V('bridge_list',RVLIST),p.V('bridge_head',p.FUNCTION),p.V('bridge_tail',RVLIST)
    v=p.V('bridge_variance','R')
    def predicate(seq):
        return p.All(v,p.imps((p.A(ALL_L2,seq),p.A(CENTERED_COMMON,seq,v)),p.A(COMMON,seq,v)))
    base=p.close(literal(kernel,'moment_common_nil',v),(v,),(p.A(ALL_L2,NIL),p.A(CENTERED_COMMON,NIL,v)))
    cons=p.A(CONS,h,t)
    conditions=(p.A(ALL_L2,cons),p.A(CENTERED_COMMON,cons,v))
    ls=unfold_conjunction(kernel,'moment_l2_cons',(h,t),p.hyp(conditions[0]))
    values=unfold_conjunction(kernel,'moment_centered_common_cons',(h,t,v),p.hyp(conditions[1]))
    head=p.apply(p.ref('l2_variance_definition_bridge',h),('and_l',ls))
    head=p.rewrite(kernel,('and_l',values),head)
    tail=p.apply(p.instantiate(p.hyp(predicate(t)),v),('and_r',ls),('and_r',values))
    proof=p.apply(('and_r',literal(kernel,'moment_common_cons',h,t,v)),('and_i',head,tail))
    step=p.close(p.close(proof,(v,),conditions),(h,t),(predicate(t),))
    body=predicate(xs)
    kernel.theorem('common_centered_variance_to_moments',p.All(xs,body),('list_induction',xs,h,t,body,base,step))
    conditions=(p.A(ALL_L2,xs),p.A(PAIRWISE,xs),p.A(CENTERED_COMMON,xs,v),p.Lt(p.RZERO,count(xs)))
    ll,ind,cv,pos=map(p.hyp,conditions)
    common=p.apply(p.ref('common_centered_variance_to_moments',xs,v),ll,cv)
    proof=p.apply(p.ref('variance_of_mean_for_arbitrary_nonempty_finite_sample',xs,v),ll,ind,common,pos)
    kernel.theorem('book_mean_variance_from_pairwise_independence',p.alls((xs,v),p.imps(conditions,p.Eq(variance(p.scale_function(p.Div(p.RONE,count(xs)),total(xs))),p.Div(v,count(xs))))),p.close(proof,(xs,v),conditions))


def derive_shared_participant(kernel):
    names=('u','v','e','w','f')
    variables={name:p.V('component_'+name,p.FUNCTION) for name in names}
    pairs=(('u','w'),('u','f'),('v','u'),('v','w'),('v','f'),('e','u'),('e','w'),('e','f'))
    conditions=tuple(p.square_integrable(variables[name]) for name in names)+tuple(p.independent_functions(variables[a],variables[b]) for a,b in pairs)
    l2={name:p.hyp(conditions[i]) for i,name in enumerate(names)}
    independence={pair:p.hyp(conditions[len(names)+i]) for i,pair in enumerate(pairs)}
    first={name:l2_integral(kernel,variables[name],l2[name]) for name in names}
    means={name:p.expectation(variables[name]) for name in names}
    u,v,e,w,f=(variables[name] for name in names)
    left=p.add_function(p.add_function(u,v),e)
    right=p.add_function(p.add_function(u,w),f)
    def sum_integral(selected,target):
        fun,value,proof=linear_integral(kernel,[(p.RONE,variables[name],means[name],first[name]) for name in selected])
        return value,signed(kernel,fun,value,proof,target)
    left_value,left_proof=sum_integral(('u','v','e'),left)
    right_value,right_proof=sum_integral(('u','w','f'),right)
    terms=[]
    for a in ('u','v','e'):
        for b in ('u','w','f'):
            term=p.product_function(variables[a],variables[b])
            if (a,b)==('u','u'):
                value=p.expectation(p.square_function(u))
                proof=l2_square(kernel,u,l2['u'])
            else:
                value=p.Mul(means[a],means[b])
                proof=independent_product(kernel,variables[a],variables[b],l2[a],l2[b],independence[a,b])
            terms.append((p.RONE,term,value,proof))
    fun,cross_value,cross_proof=linear_integral(kernel,terms)
    product=p.product_function(left,right)
    cross_proof=signed(kernel,fun,cross_value,cross_proof,product)
    answer=p.apply(p.ref('covariance_from_signed_moments',left,right,left_value,right_value,cross_value),left_proof,right_proof,cross_proof)
    current=conclusion(kernel,answer)[2]
    el=expectation_from(kernel,left,left_value,left_proof)
    er=expectation_from(kernel,right,right_value,right_proof)
    equality=algebra_under(kernel,current,moment_variance(u),(el,er))
    bridge=p.apply(p.ref('l2_variance_definition_bridge',u),l2['u'])
    equality=p.eq_trans(current,moment_variance(u),variance(u),equality,p.symmetric(variance(u),moment_variance(u),bridge))
    answer=p.eq_trans(covariance(left,right),current,variance(u),answer,equality)
    formula=p.alls(tuple(variables.values()),p.imps(conditions,p.Eq(covariance(left,right),variance(u))))
    kernel.theorem('shared_participant_covariance_from_independence',formula,p.close(answer,tuple(variables.values()),conditions))


def derive_book_mean_chain(kernel):
    f=p.V('scaled_random_variable',p.FUNCTION)
    first_value,second_value,c=(p.V(name,'R') for name in ('scaled_first_moment','scaled_second_moment','real_multiplier'))
    conditions=(p.has_signed_integral(f,first_value),p.has_signed_integral(p.square_function(f),second_value))
    first,second=map(p.hyp,conditions)
    scaled=p.scale_function(c,f);square_c=p.Mul(c,c)
    scaled_first_value=p.Mul(c,first_value)
    scaled_second_value=p.Mul(square_c,second_value)
    scaled_first=p.apply(use(kernel,'signed_integral_scale',f,first_value,c),first)
    scaled_second=p.apply(use(kernel,'signed_integral_scale',p.square_function(f),second_value,square_c),second)
    scaled_second=signed(kernel,p.scale_function(square_c,p.square_function(f)),scaled_second_value,scaled_second,p.square_function(scaled))
    base=p.apply(p.ref('variance_from_signed_moments',f,first_value,second_value),first,second)
    expanded=p.apply(p.ref('variance_from_signed_moments',scaled,scaled_first_value,scaled_second_value),scaled_first,scaled_second)
    wanted=p.Mul(square_c,variance(f))
    equality=algebra_under(kernel,conclusion(kernel,expanded)[2],wanted,(base,expectation_from(kernel,f,first_value,first),expectation_from(kernel,scaled,scaled_first_value,scaled_first)))
    proof=p.eq_trans(variance(scaled),conclusion(kernel,expanded)[2],wanted,expanded,equality)
    formula=p.alls((f,first_value,second_value,c),p.imps(conditions,p.Eq(variance(scaled),wanted)))
    kernel.theorem('variance_of_scalar_from_signed_moments',formula,p.close(proof,(f,first_value,second_value,c),conditions))
    xs=p.V('book_observations',RVLIST);v=p.V('book_population_variance','R')
    n=count(xs);s=total(xs);es=p.expectation(s)
    conditions=(p.A(ALL_L2,xs),p.A(PAIRWISE,xs),p.A(CENTERED_COMMON,xs,v))
    ll,ind,cv=map(p.hyp,conditions)
    common=p.apply(p.ref('common_centered_variance_to_moments',xs,v),ll,cv)
    first=p.apply(p.ref('l2_list_sum_integrable',xs),ll)
    second_value=p.Add(p.Mul(es,es),p.Mul(n,v))
    second=p.apply(p.ref('independent_common_variance_sum_moment',xs,v),ll,ind,common)
    expanded=p.apply(p.ref('variance_from_signed_moments',s,es,second_value),first,second)
    value=p.Mul(n,v)
    proof=p.eq_trans(variance(s),conclusion(kernel,expanded)[2],value,expanded,p.ring(conclusion(kernel,expanded)[2],value))
    formula=p.alls((xs,v),p.imps(conditions,p.Eq(variance(s),value)))
    kernel.theorem('book_sum_variance_from_pairwise_independence',formula,p.close(proof,(xs,v),conditions))
    h,t=p.V('common_variance_head',p.FUNCTION),p.V('common_variance_tail',RVLIST)
    def predicate(seq):
        return p.All(v,p.Imp(p.A(CENTERED_COMMON,seq,v),p.Eq(variance_total(seq),p.Mul(count(seq),v))))
    base=algebra_under(kernel,variance_total(NIL),p.Mul(count(NIL),v),(literal(kernel,'moment_variance_total_nil'),literal(kernel,'moment_count_nil')))
    base=p.close(base,(v,),(p.A(CENTERED_COMMON,NIL,v),))
    cons=p.A(CONS,h,t);condition=p.A(CENTERED_COMMON,cons,v)
    separated=unfold_conjunction(kernel,'moment_centered_common_cons',(h,t,v),p.hyp(condition))
    tail=p.apply(p.instantiate(p.hyp(predicate(t)),v),('and_r',separated))
    step=algebra_under(kernel,variance_total(cons),p.Mul(count(cons),v),(literal(kernel,'moment_variance_total_cons',h,t),literal(kernel,'moment_count_cons',h,t),('and_l',separated),tail))
    step=p.close(p.close(step,(v,),(condition,)),(h,t),(predicate(t),))
    kernel.theorem('book_sum_of_common_variances',p.All(xs,predicate(xs)),('list_induction',xs,h,t,predicate(xs),base,step))
    individual=p.apply(p.ref('book_sum_of_common_variances',xs,v),cv)
    total_proof=p.apply(p.ref('book_sum_variance_from_pairwise_independence',xs,v),ll,ind,cv)
    proof=p.eq_trans(variance(s),value,variance_total(xs),total_proof,p.symmetric(variance_total(xs),value,individual))
    formula=p.alls((xs,v),p.imps(conditions,p.Eq(variance(s),variance_total(xs))))
    kernel.theorem('book_variance_sum_additivity',formula,p.close(proof,(xs,v),conditions))
    positive=p.Lt(p.RZERO,n)
    q=p.Div(p.RONE,n);mean=p.scale_function(q,s)
    proof=p.apply(p.ref('variance_of_scalar_from_signed_moments',s,es,second_value,q),first,second)
    reciprocal=p.apply(literal(kernel,'moment_positive_reciprocal_square',n),p.hyp(positive))
    wanted=p.Mul(p.Div(p.RONE,p.Mul(n,n)),variance(s))
    equality=algebra_under(kernel,conclusion(kernel,proof)[2],wanted,(reciprocal,))
    proof=p.eq_trans(variance(mean),conclusion(kernel,proof)[2],wanted,proof,equality)
    formula=p.alls((xs,v),p.imps(conditions+(positive,),p.Eq(variance(mean),wanted)))
    kernel.theorem('book_mean_variance_scaling',formula,p.close(proof,(xs,v),conditions+(positive,)))
    scale=p.Div(p.RONE,p.Mul(n,n))
    first=proof
    additive=p.apply(p.ref('book_variance_sum_additivity',xs,v),ll,ind,cv)
    common=p.apply(p.ref('book_sum_of_common_variances',xs,v),cv)
    placeholder=p.V('scaled_variance_placeholder','R')
    second=('eq_e',additive,placeholder,p.Eq(p.Mul(scale,variance(s)),p.Mul(scale,placeholder)),('eq_i',p.Mul(scale,variance(s))))
    third=('eq_e',common,placeholder,p.Eq(p.Mul(scale,variance_total(xs)),p.Mul(scale,placeholder)),('eq_i',p.Mul(scale,variance_total(xs))))
    linked=p.eq_trans(variance(mean),p.Mul(scale,variance(s)),p.Mul(scale,variance_total(xs)),first,second)
    linked=p.eq_trans(variance(mean),p.Mul(scale,variance_total(xs)),p.Mul(scale,value),linked,third)
    final=p.apply(p.ref('book_mean_variance_from_pairwise_independence',xs,v),ll,ind,cv,p.hyp(positive))
    fourth=p.eq_trans(p.Mul(scale,value),variance(mean),p.Div(v,n),p.symmetric(variance(mean),p.Mul(scale,value),linked),final)
    chain=('and_i',first,('and_i',second,('and_i',third,fourth)))
    target=p.And(p.Eq(variance(mean),p.Mul(scale,variance(s))),p.And(p.Eq(p.Mul(scale,variance(s)),p.Mul(scale,variance_total(xs))),p.And(p.Eq(p.Mul(scale,variance_total(xs)),p.Mul(scale,value)),p.Eq(p.Mul(scale,value),p.Div(v,n)))))
    kernel.theorem('book_entire_variance_chain',p.alls((xs,v),p.imps(conditions+(positive,),target)),p.close(chain,(xs,v),conditions+(positive,)))


def derive_all(kernel):
    for builder in (derive_centered_identities,derive_sum_integral,derive_product_with_sum,derive_common_variance_sum,derive_mean_variance,derive_centered_independent_product,derive_centered_common_bridge,derive_shared_participant,derive_book_mean_chain):
        builder(kernel)
    return kernel


def check(name,condition):
    if condition is not True:
        raise AssertionError(name)
    return {'id':name,'passed':True}


def remove_premise(formula,index):
    if formula[0]=='all':
        return ('all',formula[1],remove_premise(formula[2],index))
    if formula[0]!='imp':
        raise ValueError('premise does not exist')
    if index==0:
        return formula[2]
    return ('imp',formula[1],remove_premise(formula[2],index-1))


def verify_general_probability():
    kernel=p.probability_certificates()
    expected_interfaces=p.planned_probability_interfaces()
    for name,formula in expected_interfaces.items():
        if name in kernel.axioms or name not in kernel.verified or not p.same(kernel.verified[name].conclusion,formula) or kernel.verified[name].assumptions:
            raise ValueError(('general integration interface not proved',name))
    if not all(item['passed'] for item in algebra.results):
        raise ValueError('moment algebra failed')
    p.add_axioms(kernel,foundations())
    derive_all(kernel)
    targets={name:next(record for record in kernel.records if record[0]==name) for name in ('book_mean_variance_from_pairwise_independence','centered_independent_cross_moment_zero','shared_participant_covariance_from_independence')}
    mean,cross,shared=targets.values()
    results=[
        check('general_mean_variance_from_original_hypotheses',not kernel.infer(('ref',mean[0])).assumptions and p.same(kernel.infer(('ref',mean[0])).conclusion,mean[1])),
        check('general_centered_independent_cross_moment',not kernel.infer(('ref',cross[0])).assumptions and p.same(kernel.infer(('ref',cross[0])).conclusion,cross[1])),
        check('general_shared_participant_covariance',not kernel.infer(('ref',shared[0])).assumptions and p.same(kernel.infer(('ref',shared[0])).conclusion,shared[1])),
        check('book_mean_chain_sum_variance',not kernel.infer(('ref','book_sum_variance_from_pairwise_independence')).assumptions),
        check('book_mean_chain_scalar_variance',not kernel.infer(('ref','book_mean_variance_scaling')).assumptions),
        check('book_mean_chain_variance_additivity',not kernel.infer(('ref','book_variance_sum_additivity')).assumptions),
        check('book_mean_chain_common_variance_sum',not kernel.infer(('ref','book_sum_of_common_variances')).assumptions),
        check('book_entire_displayed_variance_chain',not kernel.infer(('ref','book_entire_variance_chain')).assumptions),
        check('positive_reciprocal_square_domain',algebra.positive_n.is_positive is True and p.sp.cancel((1/algebra.positive_n)**2-1/(algebra.positive_n**2))==0),
        check('no_general_probability_result_postulated',not set(expected_interfaces)&set(kernel.axioms)),
        check('reject_missing_sample_positivity',p.rejects(lambda:kernel.theorem('invalid_nonpositive_sample',remove_premise(mean[1],3),mean[2]))),
        check('reject_missing_common_variance',p.rejects(lambda:kernel.theorem('invalid_heterogeneous_variance',remove_premise(mean[1],2),mean[2]))),
        check('reject_missing_pairwise_independence',p.rejects(lambda:kernel.theorem('invalid_dependent_sample',remove_premise(mean[1],1),mean[2]))),
        check('reject_missing_product_independence',p.rejects(lambda:kernel.theorem('invalid_dependent_product',remove_premise(cross[1],2),cross[2]))),
        check('reject_each_missing_shared_independence',all(p.rejects(lambda index=index:kernel.theorem('invalid_shared_independence_'+str(index),remove_premise(shared[1],index),shared[2])) for index in range(5,13)))
    ]
    return {'kernel':kernel,'results':results,'targets':targets}


if __name__=='__main__':
    verification=verify_general_probability()
    print(json.dumps({'backend':'Python 3','passed':all(item['passed'] for item in verification['results']),'results':verification['results'],'general_probability_complete':True,'derived_theorems':len(verification['kernel'].verified),'scope':'Arbitrary probability spaces and square-integrable real random variables; arbitrary finite nonempty samples with pairwise independence and common variance; shared participant covariance with exactly eight cross independences. No normality, finite support or already-diagonal covariance matrix is assumed.'}))
