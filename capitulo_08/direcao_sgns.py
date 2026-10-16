import json
import sympy as sp

xs,head,tail,nil=sp.symbols('xs head tail nil')
cons=sp.Function('cons')
u,v=sp.Function('u',real=True),sp.Function('v',real=True)
dot,norm,updated=map(sp.Function,('dot','norm','updated'))
class Nonzero(sp.logic.boolalg.BooleanFunction):
    nargs=1
nonzero=Nonzero
rate,p,y=sp.symbols('rate p y',real=True)
rules={dot(nil):0,norm(nil):0,updated(nil):0,dot(cons(head,tail)):u(head)*v(head)+dot(tail),norm(cons(head,tail)):v(head)**2+norm(tail),updated(cons(head,tail)):(u(head)-rate*(p-y)*v(head))*v(head)+updated(tail)}
def unfold(x):return sp.sympify(x).xreplace(rules)
def update_induction(sign=-1):
    left=updated(xs)
    right=dot(xs)+sign*rate*(p-y)*norm(xs)
    base=sp.expand(unfold(left.subs(xs,nil))-unfold(right.subs(xs,nil)))
    step=unfold(left.subs(xs,cons(head,tail))).subs(left.subs(xs,tail),right.subs(xs,tail))-unfold(right.subs(xs,cons(head,tail)))
    return base==0 and sp.expand(step)==0

def nonzero_unfold(sequence):
    if sequence==nil:return sp.false
    if sequence.func==cons:return sp.Or(sp.Ne(v(sequence.args[0]),0),nonzero(sequence.args[1]))
    return nonzero(sequence)

def positive_norm_induction():
    tail_nonnegative=sp.Symbol('tail_nonnegative',nonnegative=True)
    tail_positive=sp.Symbol('tail_positive',positive=True)
    nonzero_head=sp.Symbol('nonzero_head',real=True,nonzero=True)
    base=unfold(norm(nil))==0 and nonzero_unfold(nil)==sp.false
    split=nonzero_unfold(cons(head,tail))==sp.Or(sp.Ne(v(head),0),nonzero(tail))
    nonnegative_step=unfold(norm(cons(head,tail))).subs(norm(tail),tail_nonnegative).is_nonnegative is True
    head_branch=unfold(norm(cons(head,tail))).subs({v(head):nonzero_head,norm(tail):tail_nonnegative}).is_positive is True
    tail_branch=unfold(norm(cons(head,tail))).subs({v(head):0,norm(tail):tail_positive}).is_positive is True
    return base and split and nonnegative_step and head_branch and tail_branch

z=sp.Symbol('z',real=True)
alpha,s=sp.symbols('alpha s',positive=True)
probability=sp.exp(z)/(1+sp.exp(z))
observed=-alpha*(probability-1)*s
negative=-alpha*probability*s
results=[]
def check(name,value):
    if value is not True:raise AssertionError(name)
    results.append({'id':name,'passed':True})

check('actual_finite_dot_update_induction',update_induction())
check('nonzero_vector_strict_square_sum_induction',positive_norm_induction())
check('actual_sigmoid_positive',probability.is_positive is True)
check('actual_sigmoid_below_one',sp.cancel(1-probability)==1/(1+sp.exp(z)) and (1/(1+sp.exp(z))).is_positive is True)
check('observed_pair_strict_increase',sp.cancel(observed)==alpha*s/(1+sp.exp(z)) and (alpha*s/(1+sp.exp(z))).is_positive is True)
check('negative_pair_strict_decrease',(-negative).is_positive is True)
check('zero_context_not_strict',observed.subs(s,0)==0 and negative.subs(s,0)==0)
check('zero_step_not_strict',observed.subs(alpha,0)==0 and negative.subs(alpha,0)==0)
check('wrong_update_sign_rejected',not update_induction(1))
print(json.dumps({'backend':'Python 3','scope':'arbitrary finite real vectors, context fixed and nonzero, positive step, sigmoid of finite real score, label zero or one; actual update fold and nonzero-square-sum induction','checks':len(results),'passed':True,'results':results}))
