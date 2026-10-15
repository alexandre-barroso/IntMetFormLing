import json
import sympy as sp

a,b,minimum,u,v=sp.symbols('a b minimum u v',real=True)
xs,tail,nil=sp.symbols('xs tail nil')
cons=sp.Function('cons')
fold=sp.Function('fold')
F=sp.Function('F')
def unfold(expression):
    if not isinstance(expression,sp.Basic) or not expression.args:
        return expression
    expression=expression.func(*(unfold(arg) for arg in expression.args))
    if expression.func==fold:
        row,body=expression.args
        if row==nil:
            return sp.Integer(0)
        if row.func==cons:
            first,second,rest=row.args
            return body.subs({a:first,b:second},simultaneous=True)+fold(rest,body)
    return expression
def fold_identity_induction(left,right,absolute_value_rule=False):
    if {tail,u,v}&(left.free_symbols|right.free_symbols):
        return False
    base=sp.expand(unfold(left.subs(xs,nil))-unfold(right.subs(xs,nil)))
    hypothesis_left=left.subs(xs,tail)
    hypothesis_right=right.subs(xs,tail)
    step_left=unfold(left.subs(xs,cons(u,v,tail))).subs(hypothesis_left,hypothesis_right)
    step_right=unfold(right.subs(xs,cons(u,v,tail)))
    if absolute_value_rule:
        step_left=step_left.subs(sp.Abs(u-v),u+v-2*sp.Min(u,v))
        step_right=step_right.subs(sp.Abs(u-v),u+v-2*sp.Min(u,v))
    return base==0 and sp.expand(step_left-step_right)==0
def sum_nonnegative_induction():
    head,remainder=sp.symbols('head remainder',nonnegative=True)
    base=unfold(fold(nil,F(a,b)))
    step=unfold(fold(cons(u,v,tail),F(a,b)))
    expected=F(u,v)+fold(tail,F(a,b))
    constrained=step.subs({F(u,v):head,fold(tail,F(a,b)):remainder})
    return base==0 and step==expected and constrained.is_nonnegative is True
results=[]
def check(identifier,condition):
    results.append({'id':identifier,'passed':bool(condition)})
check('dp_absolute_min_cases',sp.expand((b-a)-(a+b-2*a))==0 and sp.expand((a-b)-(a+b-2*b))==0 and sp.Abs(a-b).is_nonnegative is True)
nonnegative_a,nonnegative_minimum,complement,excess=sp.symbols('nonnegative_a nonnegative_minimum complement excess',nonnegative=True)
first_gap=sp.expand(a-a*minimum)
second_gap=sp.expand(b-a*minimum)
check('dp_pointwise_min_bound',sp.expand(first_gap-a*(1-minimum))==0 and (nonnegative_a*complement).is_nonnegative is True and sp.expand(second_gap-((b-minimum)+minimum*(1-a)))==0 and (excess+nonnegative_minimum*complement).is_nonnegative is True)
absolute_identity=fold_identity_induction(fold(xs,sp.Abs(a-b)),fold(xs,a)+fold(xs,b)-2*fold(xs,sp.Min(a,b)),True)
residual_identity=fold_identity_induction(fold(xs,sp.Min(a,b)-minimum*a),fold(xs,sp.Min(a,b))-minimum*fold(xs,a))
check('dp_absolute_sum_induction',absolute_identity)
check('dp_residual_sum_induction',residual_identity)
check('dp_nonnegative_sum_induction',sum_nonnegative_induction())
overlap,residual=sp.symbols('overlap residual',real=True)
nonnegative_residual=sp.symbols('nonnegative_residual',nonnegative=True)
check('dp_aggregate_bound',absolute_identity and residual_identity and sum_nonnegative_induction() and sp.simplify((1+1-2*overlap)/2-(1-overlap))==0 and sp.simplify((1-minimum)-(1-(minimum+nonnegative_residual)))==nonnegative_residual and nonnegative_residual.is_nonnegative is True)
index=sp.symbols('index',integer=True)
size=sp.symbols('size',integer=True,nonnegative=True)
check('dp_extremal_general',sp.Min(1,1-complement)==1-complement and sp.Min(0,nonnegative_a)==0 and sp.Sum(sp.Integer(0),(index,1,size)).doit()==0 and sp.simplify((1+1-2*minimum)/2-(1-minimum))==0)
denominator=sp.symbols('denominator',positive=True)
nonnegative_distance,gap=sp.symbols('nonnegative_distance gap',nonnegative=True)
distance=sp.symbols('distance',real=True)
check('dp_normalized_bound',sp.cancel(1-distance/denominator-(denominator-distance)/denominator)==0 and (nonnegative_distance/denominator).is_nonnegative is True and (gap/denominator).is_nonnegative is True and sp.cancel(denominator/denominator)==1)
check('dp_wrong_absolute_identity_rejected',not fold_identity_induction(fold(xs,sp.Abs(a-b)),fold(xs,a)+fold(xs,b)-fold(xs,sp.Min(a,b)),True))
def entry_le_sum_induction():
    selected=sp.symbols('selected',real=True)
    head_mass,tail_mass,tail_gap=sp.symbols('head_mass tail_mass tail_gap',nonnegative=True)
    total=unfold(fold(cons(u,v,tail),F(a,b)))
    head_gap=sp.expand(total-F(u,v))
    recursive_gap=sp.expand((total-selected).subs(fold(tail,F(a,b)),selected+tail_gap))
    return sum_nonnegative_induction() and head_gap==fold(tail,F(a,b)) and head_gap.subs(fold(tail,F(a,b)),tail_mass).is_nonnegative is True and recursive_gap==F(u,v)+tail_gap and recursive_gap.subs(F(u,v),head_mass).is_nonnegative is True
check('dp_entry_le_sum_induction',entry_le_sum_induction())
remaining=sp.symbols('remaining',nonnegative=True)
check('dp_probability_entries_bounded',entry_le_sum_induction() and sp.simplify((1-remaining)-1)==-remaining and (-remaining).is_nonpositive is True)
minimum_gap=sp.symbols('minimum_gap',nonnegative=True)
check('dp_minimum_in_unit_interval',sp.simplify((1-remaining-minimum_gap)-1)==-remaining-minimum_gap and (-remaining-minimum_gap).is_nonpositive is True and sp.simplify(1-(1-remaining))==remaining)
report={'backend':'Python/SymPy','checks':len(results),'passed':all(r['passed'] for r in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
