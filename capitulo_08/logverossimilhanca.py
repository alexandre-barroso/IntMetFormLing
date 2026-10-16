import json
import sympy as sp

xs,head,tail,nil=sp.symbols('xs fresh_head fresh_tail nil')
cons=sp.Function('cons')
N=sp.Symbol('N',positive=True)
observed=sp.Function('observed',nonnegative=True)
expected=sp.Function('expected',positive=True)
positive_count=sp.Symbol('positive_count',positive=True)
folds=[sp.Function('original_sum'),sp.Function('ratio_sum'),sp.Function('cancelled_sum')]
def contribution(index,o,e):
    formulas=[o*(sp.log(o/N)-sp.log(e/N)),o*sp.log((o/N)/(e/N)),o*sp.log(o/e)]
    return sp.Piecewise((0,sp.Eq(o,0)),(formulas[index],True))
def unfold(expression):
    rules={}
    for index,f in enumerate(folds):
        rules[f(nil)]=sp.Integer(0)
        rules[f(cons(head,tail))]=contribution(index,observed(head),expected(head))+f(tail)
    return expression.subs(rules,simultaneous=True)
def structural_equality(left,right):
    if {head,tail}&(left.free_symbols|right.free_symbols):return False
    if sp.simplify(unfold(left.subs(xs,nil))-unfold(right.subs(xs,nil)))!=0:return False
    hypothesis_left=left.subs(xs,tail)
    hypothesis_right=right.subs(xs,tail)
    step_left=unfold(left.subs(xs,cons(head,tail))).subs(hypothesis_left,hypothesis_right)
    step_right=unfold(right.subs(xs,cons(head,tail))).subs(hypothesis_left,hypothesis_right)
    return all(sp.simplify(sp.expand_log((step_left-step_right).subs(observed(head),value)))==0 for value in [sp.Integer(0),positive_count])
results=[]
def check(name,value):
    if not value:raise AssertionError(name)
    results.append({'id':name,'passed':True})

real_count=sp.Symbol('real_count',real=True)
check('nonnegative_count_cases_exhaustive',sp.simplify(sp.reduce_inequalities([real_count>=0,sp.Ne(real_count,0),real_count<=0],real_count))==sp.false)
check('finite_log_ratio_induction',structural_equality(folds[0](xs),folds[1](xs)))
check('finite_total_cancellation_induction',structural_equality(folds[1](xs),folds[2](xs)))
check('zero_contributions',all(contribution(i,sp.Integer(0),expected(head))==0 for i in range(3)))
x,e=sp.symbols('x e',positive=True)
check('zero_contribution_right_limit',sp.limit(x*sp.log(x/e),x,0,dir='+')==0)
check('wrong_sum_base_rejected',not structural_equality(folds[0](xs),folds[1](xs)+1))
check('wrong_sum_sign_rejected',not structural_equality(folds[0](xs),-folds[1](xs)))
check('nonfresh_induction_rejected',not structural_equality(folds[0](xs),folds[1](xs)+head))
print(json.dumps({'backend':'Python 3','scope':'finite sums over observed>=0 expected>0 N>0; zero terms defined continuously; structural induction in explicit list recursions with exhaustive zero/positive head cases','checks':len(results),'passed':True,'results':results}))
