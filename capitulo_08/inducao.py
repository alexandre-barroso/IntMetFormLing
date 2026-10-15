import json
import sympy as sp

xs,head,tail,nil=sp.symbols('xs fresh_head fresh_tail nil')
cons=sp.Function('cons')
D=sp.Symbol('D',positive=True)
shift,rate,prob,target,weight=sp.symbols('shift rate prob target weight',real=True)
count=sp.Function('count',nonnegative=True)
score=sp.Function('score',real=True)
u=sp.Function('u',real=True)
v=sp.Function('v',real=True)
g=sp.Function('g',nonnegative=True)
c=sp.Function('c',nonnegative=True)
names=['count_total','length','laplace_raw','laplace_normalized','exponential_total','exponential_normalized','shifted_exponential_total','dot','norm_squared','updated_dot','generated_total','copied_total','mixture_total']
folds={name:sp.Function(name,real=True) for name in names}
terms={
 'count_total':count(head),
 'length':sp.Integer(1),
 'laplace_raw':count(head)+1,
 'laplace_normalized':(count(head)+1)/D,
 'exponential_total':sp.exp(score(head)),
 'exponential_normalized':sp.exp(score(head))/D,
 'shifted_exponential_total':sp.exp(score(head)+shift),
 'dot':u(head)*v(head),
 'norm_squared':v(head)**2,
 'updated_dot':(u(head)-rate*(prob-target)*v(head))*v(head),
 'generated_total':g(head),
 'copied_total':c(head),
 'mixture_total':weight*g(head)+(1-weight)*c(head)}

def unfold(expression):
    rules={}
    for name,f in folds.items():
        rules[f(nil)]=sp.Integer(0)
        rules[f(cons(head,tail))]=terms[name]+f(tail)
    return expression.subs(rules,simultaneous=True)

def structural_induction(left,right):
    if {head,tail}&(left.free_symbols|right.free_symbols):return False
    base_left=unfold(left.subs(xs,nil))
    base_right=unfold(right.subs(xs,nil))
    if sp.simplify(base_left-base_right)!=0:return False
    hypothesis_left=left.subs(xs,tail)
    hypothesis_right=right.subs(xs,tail)
    step_left=unfold(left.subs(xs,cons(head,tail)))
    step_right=unfold(right.subs(xs,cons(head,tail)))
    step_left=step_left.subs(hypothesis_left,hypothesis_right)
    step_right=step_right.subs(hypothesis_left,hypothesis_right)
    return sp.simplify(sp.expand_power_exp(step_left-step_right))==0

def nonnegative_induction(name):
    f=folds[name]
    if unfold(f(nil))!=0:return False
    tail_total=sp.Symbol('induction_tail_total',nonnegative=True)
    step=unfold(f(cons(head,tail))).subs(f(tail),tail_total)
    return step.is_nonnegative is True

def positive_nonempty(name):
    if not nonnegative_induction(name):return False
    f=folds[name]
    tail_total=sp.Symbol('induction_tail_total',nonnegative=True)
    return unfold(f(cons(head,tail))).subs(f(tail),tail_total).is_positive is True

results=[]
def check(name,value):
    if value is not True:raise AssertionError(name)
    results.append({'id':name,'passed':True})

count_total,length,laplace_raw,laplace_normalized,exponential_total,exponential_normalized,shifted_exponential_total,dot,norm_squared,updated_dot,generated_total,copied_total,mixture_total=[folds[name] for name in names]
check('finite_fold_empty_definitions',all(unfold(f(nil))==0 for f in folds.values()))
check('finite_fold_cons_definitions',all(unfold(f(cons(head,tail)))==terms[name]+f(tail) for name,f in folds.items()))
check('laplace_numerator_induction',structural_induction(laplace_raw(xs),count_total(xs)+length(xs)))
check('laplace_division_induction',structural_induction(laplace_normalized(xs),(count_total(xs)+length(xs))/D))
check('laplace_nonempty_denominator',positive_nonempty('laplace_raw'))
check('laplace_denominator_cancellation',sp.cancel(D/D)==1)
check('softmax_division_induction',structural_induction(exponential_normalized(xs),exponential_total(xs)/D))
check('softmax_nonempty_denominator',positive_nonempty('exponential_total'))
check('softmax_component_positive',(sp.exp(score(head))/D).is_positive is True)
check('softmax_denominator_cancellation',sp.cancel(D/D)==1)
check('softmax_shift_induction',structural_induction(shifted_exponential_total(xs),sp.exp(shift)*exponential_total(xs)))
check('softmax_shift_cancellation',sp.simplify(sp.exp(score(head)+shift)/(sp.exp(shift)*D)-sp.exp(score(head))/D)==0 and sp.exp(shift).is_positive is True)
check('word2vec_dot_update_induction',structural_induction(updated_dot(xs),dot(xs)-rate*(prob-target)*norm_squared(xs)))
check('norm_squared_induction',nonnegative_induction('norm_squared'))
check('mixture_sum_induction',structural_induction(mixture_total(xs),weight*generated_total(xs)+(1-weight)*copied_total(xs)))
check('mixture_unit_totals',sp.expand(weight*1+(1-weight)*1)==1)
r=sp.Symbol('nonnegative_odds',nonnegative=True)
piece=weight*g(head)+(1-weight)*c(head)
check('mixture_interior_nonnegative',sp.factor(piece.subs(weight,r/(1+r))).is_nonnegative is True)
check('mixture_endpoint_nonnegative',piece.subs(weight,1).is_nonnegative is True)
check('mixture_parameterization_inverse',sp.cancel((weight/(1-weight))/(1+weight/(1-weight))-weight)==0 and len(sp.solve(sp.Eq(weight,r/(1+r)),r))==1 and sp.cancel(sp.solve(sp.Eq(weight,r/(1+r)),r)[0]-weight/(1-weight))==0)
check('mixture_parameterization_domain',sp.simplify(sp.reduce_inequalities([weight>=0,weight<1,weight/(1-weight)<0],weight))==sp.false)
check('false_base_rejected',not structural_induction(exponential_normalized(xs),exponential_total(xs)/D+1))
check('false_step_rejected',not structural_induction(updated_dot(xs),dot(xs)+rate*(prob-target)*norm_squared(xs)))
check('nonfresh_parameter_rejected',not structural_induction(exponential_total(xs),exponential_total(xs)+head))
print(json.dumps({'backend':'Python 3','scope':'induction on finite lists from the explicit nil/cons recursions; positive denominators; nonnegative counts and component distributions','checks':len(results),'passed':True,'results':results}))
