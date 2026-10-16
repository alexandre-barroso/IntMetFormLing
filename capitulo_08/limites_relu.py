import json
import sympy as sp

h=sp.Symbol('h',positive=True)
x=sp.Symbol('x',real=True)
rho=sp.Max(0,x)
zero=rho.subs(x,0)
left=rho.subs(x,-h)
right=rho.subs(x,h)
left_quotient=sp.cancel((left-zero)/(-h))
right_quotient=sp.cancel((right-zero)/h)
results=[]
def check(name,value):
    if not value:raise AssertionError(name)
    results.append({'id':name,'passed':True})

check('actual_max_left_branch',left==0)
check('actual_max_right_branch',right==h)
check('actual_value_at_zero',zero==0)
check('one_sided_limits_equal_actual_value',sp.limit(left,h,0,dir='+')==zero and sp.limit(right,h,0,dir='+')==zero)
check('actual_left_difference_quotient',left_quotient==0)
check('actual_right_difference_quotient',right_quotient==1)
check('one_sided_derivatives_disagree',sp.limit(left_quotient,h,0,dir='+')==0 and sp.limit(right_quotient,h,0,dir='+')==1)
check('equal_slopes_rejected',left_quotient!=right_quotient)
check('altered_intercept_breaks_continuity',sp.limit(left+1,h,0,dir='+')!=zero)
print(json.dumps({'backend':'Python 3','scope':'actual real Max(0,x), symbolic h>0, both one-sided limits and actual difference quotients at zero','checks':len(results),'passed':True,'results':results}))
