import json
import sympy as sp

N=sp.Symbol('N',positive=True,integer=True)
xs,tail=sp.symbols('xs tail')
head=sp.Symbol('head',real=True)
nil=sp.Symbol('nil')
cons=sp.Function('cons')
total=sp.Function('total')
weighted=sp.Function('weighted')

def reduce_definition(expression):
    definitions={total(nil):sp.Integer(0),weighted(nil):sp.Integer(0),total(cons(head,tail)):head+total(tail),weighted(cons(head,tail)):head/N+weighted(tail)}
    return expression.subs(definitions,simultaneous=True)

def structural_induction(left,right):
    if not N.is_positive or not N.is_integer or {head,tail}&(left.free_symbols|right.free_symbols):
        raise ValueError('invalid induction parameters')
    base_left=reduce_definition(left.subs(xs,nil))
    base_right=reduce_definition(right.subs(xs,nil))
    if sp.simplify(base_left-base_right)!=0:return False
    hypothesis_left=left.subs(xs,tail)
    hypothesis_right=right.subs(xs,tail)
    step_left=reduce_definition(left.subs(xs,cons(head,tail)))
    step_right=reduce_definition(right.subs(xs,cons(head,tail)))
    step_right=step_right.subs(hypothesis_right,hypothesis_left)
    return sp.cancel(step_left-step_right)==0

results=[]
def check(name,value):
    if not value:raise AssertionError(name)
    results.append({'id':name,'passed':True})

check('recursive_total_nil',reduce_definition(total(nil))==0)
check('recursive_total_cons',reduce_definition(total(cons(head,tail)))==head+total(tail))
check('recursive_weighted_nil',reduce_definition(weighted(nil))==0)
check('recursive_weighted_cons',reduce_definition(weighted(cons(head,tail)))==head/N+weighted(tail))
check('mean_distributivity_induction',structural_induction(total(xs)/N,weighted(xs)))
check('false_base_rejected',not structural_induction(total(xs)/N,weighted(xs)+1))
check('false_step_rejected',not structural_induction(total(xs),weighted(xs)))
print(json.dumps({'backend':'Python 3','scope':'structural induction on finite real lists from the explicit total and weighted-sum recursions; N is fixed and positive','checks':len(results),'passed':True,'results':results}))
