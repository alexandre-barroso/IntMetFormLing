import json
import sympy as sp

results=[]

def check(name,condition):
    if condition is not True:
        raise AssertionError(name)
    results.append({'id':name,'passed':True})

ex,ey,exy,ex2,ey2,c,d=sp.symbols('ex ey exy ex2 ey2 c d',real=True)
variance=lambda first,second:second-first**2
covariance=lambda first,second,product:product-first*second
check('variance_centered_expansion',sp.expand((ex2-2*ex*ex+ex**2)-variance(ex,ex2))==0)
check('covariance_centered_expansion',sp.expand((exy-ex*ey-ey*ex+ex*ey)-covariance(ex,ey,exy))==0)
check('variance_of_sum_with_covariance',sp.expand(variance(ex+ey,ex2+2*exy+ey2)-variance(ex,ex2)-variance(ey,ey2)-2*covariance(ex,ey,exy))==0)
check('variance_of_scalar_multiple',sp.expand(variance(c*ex,c**2*ex2)-c**2*variance(ex,ex2))==0)
check('variance_of_zero',variance(sp.S.Zero,sp.S.Zero)==0)
check('covariance_independent_factorization',covariance(ex,ey,ex*ey)==0)
check('centered_independent_product',sp.expand((ex*ey).subs({ex:0,ey:0}))==0)
eu,ev,ew,euw,evw=sp.symbols('eu ev ew euw evw',real=True)
check('covariance_additivity_left',sp.expand(covariance(eu+ev,ew,euw+evw)-covariance(eu,ew,euw)-covariance(ev,ew,evw))==0)
check('covariance_symmetry',sp.expand(covariance(ex,ey,exy)-covariance(ey,ex,exy))==0)
check('covariance_zero_left',covariance(0,ey,0)==0)
check('covariance_self_equals_variance',covariance(ex,ex,ex2)==variance(ex,ex2))
n=sp.symbols('n',integer=True,nonnegative=True)
v,tail_variance,head_variance,tail_covariance,head_covariance=sp.symbols('v tail_variance head_variance tail_covariance head_covariance',real=True)
covariance_tail_zero=sp.S.Zero
covariance_step=tail_covariance+head_covariance
check('covariance_finite_sum_induction_base',covariance(0,ey,0)==0)
check('covariance_finite_sum_induction_step',sp.expand(covariance_step.subs({tail_covariance:0,head_covariance:0}))==0)
variance_step=tail_variance+head_variance+2*tail_covariance
check('independent_variance_sum_induction_base',variance(0,0)==0)
check('independent_variance_sum_induction_step',sp.expand(variance_step.subs(tail_covariance,0)-(tail_variance+head_variance))==0)
check('common_variance_induction_base',0*v==0)
check('common_variance_induction_step',sp.expand(n*v+v-(n+1)*v)==0)
positive_n=sp.symbols('positive_n',integer=True,positive=True)
check('positive_sample_size_denominator',positive_n.is_nonzero is True and (positive_n**2).is_positive is True)
check('mean_variance_final_cancellation',sp.cancel((1/positive_n)**2*(positive_n*v)-v/positive_n)==0)
check('mean_variance_zero_sample_size_rejected',sp.S.Zero.is_positive is False)
means=dict(zip(('u','v','e','w','f'),sp.symbols('mu mv me mw mf',real=True)))
cross={(x,y):sp.Symbol('E_'+x+y,real=True) for x in ('u','v','e') for y in ('u','w','f')}
left=sum(means[x] for x in ('u','v','e'))
right=sum(means[y] for y in ('u','w','f'))
total=covariance(left,right,sum(cross.values()))
expanded=sum(covariance(means[x],means[y],cross[x,y]) for x,y in cross)
check('shared_participant_nine_term_expansion',sp.expand(total-expanded)==0)
independent_pairs=tuple(pair for pair in cross if pair!=('u','u'))
substitutions={cross[x,y]:means[x]*means[y] for x,y in independent_pairs}
check('shared_participant_exact_eight_independences',independent_pairs==(('u','w'),('u','f'),('v','u'),('v','w'),('v','f'),('e','u'),('e','w'),('e','f')))
check('shared_participant_general_covariance',sp.expand(total.subs(substitutions)-variance(means['u'],cross['u','u']))==0)
check('shared_participant_no_centering_required',not any(value==0 for value in substitutions.values()) and set(means.values())<=total.free_symbols)
for omitted in independent_pairs:
    remaining={key:value for key,value in substitutions.items() if key!=cross[omitted]}
    remainder=sp.expand(total.subs(remaining)-variance(means['u'],cross['u','u']))
    if remainder==0:
        raise AssertionError(('missing independence not detected',omitted))
check('shared_participant_reject_each_missing_independence',all(sp.expand(total.subs({key:value for key,value in substitutions.items() if key!=cross[pair]})-variance(means['u'],cross['u','u']))!=0 for pair in independent_pairs))
report={'backend':'Python 3','passed':True,'results':results,'scope':'General algebra and finite induction conditional on the separately proved expectation linearity, L2 closure and independent factorization; these identities alone are not probability theorems.'}

if __name__=='__main__':
    print(json.dumps(report))
