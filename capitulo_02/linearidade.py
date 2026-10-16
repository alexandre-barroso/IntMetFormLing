import json
import sympy as sp

c,u,v,w,f,width,I=sp.symbols('c u v w f width I',real=True)
m=sp.Symbol('m',nonnegative=True)
epsilon,slack=sp.symbols('epsilon slack',positive=True)
xs,tail,nil=sp.symbols('xs tail nil')
head=sp.Symbol('head',real=True)
cons=sp.Function('cons')
total=sp.Function('total')
scaled=sp.Function('scaled')

def recursive_definition(expression):
    return expression.subs({total(nil):0,scaled(nil):0,total(cons(head,tail)):head+total(tail),scaled(cons(head,tail)):c*head+scaled(tail)},simultaneous=True)

def finite_sum_induction(left,right):
    if {head,tail}&(left.free_symbols|right.free_symbols):return False
    base=sp.expand(recursive_definition(left.subs(xs,nil))-recursive_definition(right.subs(xs,nil)))
    hypothesis_left=left.subs(xs,tail)
    hypothesis_right=right.subs(xs,tail)
    step_left=recursive_definition(left.subs(xs,cons(head,tail)))
    step_right=recursive_definition(right.subs(xs,cons(head,tail)))
    step_left=step_left.subs(hypothesis_left,hypothesis_right)
    return base==0 and sp.expand(step_left-step_right)==0

def epsilon_transfer(tolerance,margin):
    if tolerance.is_positive is not True or margin.is_positive is not True:return False
    return sp.cancel(epsilon-m*(tolerance-slack)-margin)==0

def absolute_error_identity():
    return sp.simplify(sp.Abs(c*u-c*I)-sp.Abs(c)*sp.Abs(u-I))==0

def scale_riemann_limit(premise,target,tolerance,margin):
    if len(premise)!=4 or premise[0]!='riemann_tagged_sum_limit':return False
    _,integrand,interval,value=premise
    if target!=('riemann_tagged_sum_limit',('scale',c,integrand),interval,c*value):return False
    return finite_sum_induction(scaled(xs),c*total(xs)) and absolute_error_identity() and epsilon_transfer(tolerance,margin)

source=('riemann_tagged_sum_limit',('product','w','f_n'),('0','T'),I)
target=('riemann_tagged_sum_limit',('scale',c,('product','w','f_n')),('0','T'),c*I)
tolerance=epsilon/(m+1)
margin=epsilon/(m+1)+m*slack
results=[]
def check(name,value):
    if not value:raise AssertionError(name)
    results.append({'id':name,'passed':True})

check('total_nil',recursive_definition(total(nil))==0)
check('total_cons',recursive_definition(total(cons(head,tail)))==head+total(tail))
check('scaled_nil',recursive_definition(scaled(nil))==0)
check('scaled_cons',recursive_definition(scaled(cons(head,tail)))==c*head+scaled(tail))
check('finite_sum_linearity_induction',finite_sum_induction(scaled(xs),c*total(xs)))
check('pointwise_scaled_product',sp.expand((c*w)*f-c*(w*f))==0)
check('tagged_contribution_scaling',sp.expand(((c*w)*f)*width-c*((w*f)*width))==0)
check('absolute_error_factorization',absolute_error_identity())
check('absolute_multiplier_nonnegative',sp.Abs(c).is_nonnegative is True)
check('source_tolerance_positive',tolerance.is_positive is True)
check('source_error_slack',sp.expand(tolerance-(tolerance-slack)-slack)==0 and slack.is_positive is True)
check('epsilon_transfer',epsilon_transfer(tolerance,margin))
check('zero_scalar_included',sp.simplify(margin.subs(m,0)-epsilon)==0)
check('riemann_integral_scaling',scale_riemann_limit(source,target,tolerance,margin))
check('wrong_sum_rejected',not finite_sum_induction(scaled(xs),total(xs)))
check('wrong_base_rejected',not finite_sum_induction(scaled(xs),c*total(xs)+1))
check('unscaled_tolerance_rejected',not epsilon_transfer(epsilon,epsilon-m*(epsilon-slack)))
check('zero_tolerance_rejected',not epsilon_transfer(sp.Integer(0),epsilon+m*slack))
check('wrong_limit_rejected',not scale_riemann_limit(source,('riemann_tagged_sum_limit',target[1],target[2],I),tolerance,margin))
check('changed_interval_rejected',not scale_riemann_limit(source,('riemann_tagged_sum_limit',target[1],('0','2T'),c*I),tolerance,margin))
print(json.dumps({'backend':'Python 3','scope':'Assume g=w*f_n Riemann integrable on [0,T], T>=0: for every positive eta an appropriate mesh threshold makes |S(g)-I|<eta. Recursive finite-sum induction gives S(c*g)=c*S(g). With m=|c| and eta=epsilon/(m+1), slack=eta-|S(g)-I|>0; epsilon-|S(c*g)-c*I|=epsilon/(m+1)+m*slack>0. The same source mesh threshold therefore proves the scaled integral by the tagged-sum limit definition, including c=0. No primitive or target linearity assumption is used.','checks':len(results),'passed':True,'results':results}))
