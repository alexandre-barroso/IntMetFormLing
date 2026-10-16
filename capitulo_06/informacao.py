import json
import sympy as sp

xs,ys,tail,nil=sp.symbols('xs ys tail nil')
i,j,k,h=sp.symbols('i j k h')
c=sp.symbols('c',real=True)
cons=sp.Function('cons')
S=sp.Function('finiteSum')
F,G,P,C,R,L,J,K=[sp.Function(name) for name in ['F','G','P','C','R','safeLog2','jointTerm','conditionalTerm']]
def unfold(expression):
    if not isinstance(expression,sp.Basic) or not expression.args:
        return expression
    expression=expression.func(*(unfold(arg) for arg in expression.args))
    if expression.func==S:
        sequence,slot,body=expression.args
        if sequence==nil:
            return sp.Integer(0)
        if sequence.func==cons:
            head,rest=sequence.args
            return body.subs(slot,head)+S(rest,slot,body)
    return expression
def induction_identity(left,right):
    if {tail,h}&(left.free_symbols|right.free_symbols):
        return False
    base=sp.expand(unfold(left.subs(xs,nil))-unfold(right.subs(xs,nil)))
    ih_left,ih_right=left.subs(xs,tail),right.subs(xs,tail)
    step_left=unfold(left.subs(xs,cons(h,tail))).subs(ih_left,ih_right)
    step_right=unfold(right.subs(xs,cons(h,tail)))
    return base==0 and sp.expand(step_left-step_right)==0
sum_zero=induction_identity(S(xs,i,0),sp.Integer(0))
sum_add=induction_identity(S(xs,i,F(i)+G(i)),S(xs,i,F(i))+S(xs,i,G(i)))
sum_scale=induction_identity(S(xs,i,c*F(i)),c*S(xs,i,F(i)))
sum_subtract=induction_identity(S(xs,i,F(i)-G(i)),S(xs,i,F(i))-S(xs,i,G(i)))
def linearize(expression):
    if not isinstance(expression,sp.Basic) or not expression.args:
        return expression
    expression=expression.func(*(linearize(arg) for arg in expression.args))
    if expression.func!=S:
        return expression
    sequence,slot,body=expression.args
    if body==0:
        if not sum_zero:
            raise ArithmeticError('zero')
        return sp.Integer(0)
    if body.is_Add:
        if not sum_add:
            raise ArithmeticError('addition')
        return sp.Add(*(linearize(S(sequence,slot,term)) for term in body.args))
    factor,dependent=body.as_independent(slot,as_Add=False)
    if factor!=1:
        if not sum_scale:
            raise ArithmeticError('scaling')
        return factor*S(sequence,slot,dependent)
    return expression
def fubini_induction():
    left=S(xs,i,S(ys,j,F(i,j)))
    right=S(ys,j,S(xs,i,F(i,j)))
    base=sp.expand(linearize(unfold(left.subs(xs,nil)))-linearize(unfold(right.subs(xs,nil))))
    ih_left,ih_right=left.subs(xs,tail),right.subs(xs,tail)
    step_left=linearize(unfold(left.subs(xs,cons(h,tail)))).subs(ih_left,ih_right)
    step_right=linearize(unfold(right.subs(xs,cons(h,tail))))
    return base==0 and sp.expand(step_left-step_right)==0
sum_exchange=fubini_induction()
def sum_nonnegative_induction():
    head_mass,tail_mass=sp.symbols('head_mass tail_mass',nonnegative=True)
    base=unfold(S(nil,i,F(i)))
    step=unfold(S(cons(h,tail),i,F(i)))
    expected=F(h)+S(tail,i,F(i))
    constrained=step.subs({F(h):head_mass,S(tail,i,F(i)):tail_mass})
    return base==0 and step==expected and constrained.is_nonnegative is True
def entry_le_sum_induction():
    selected=sp.symbols('selected',real=True)
    head_mass,tail_mass,tail_gap=sp.symbols('head_mass tail_mass tail_gap',nonnegative=True)
    total=unfold(S(cons(h,tail),i,F(i)))
    head_gap=sp.expand(total-F(h))
    recursive_gap=sp.expand((total-selected).subs(S(tail,i,F(i)),selected+tail_gap))
    return sum_nonnegative_induction() and head_gap==S(tail,i,F(i)) and head_gap.subs(S(tail,i,F(i)),tail_mass).is_nonnegative is True and recursive_gap==F(h)+tail_gap and recursive_gap.subs(F(h),head_mass).is_nonnegative is True
positive_cell=sp.symbols('positive_cell',positive=True)
nonnegative_rest=sp.symbols('nonnegative_rest',nonnegative=True)
nonnegative_cell=sp.symbols('nonnegative_cell',nonnegative=True)
real_cell,real_rest=sp.symbols('real_cell real_rest',real=True)
p,r,y=sp.symbols('p r y',positive=True)
def safe_log2(value):
    return sp.Piecewise((0,sp.Eq(value,0)),(sp.log(value)/sp.log(2),True))
def joint_term(mass,row,column):
    if mass==0:
        return sp.Integer(0)
    return mass*sp.log(mass/(row*column))/sp.log(2)
def conditional_term(mass,row):
    if mass==0:
        return sp.Integer(0)
    return mass*sp.log(mass/row)/sp.log(2)
def conditional_probability_term(mass,row):
    if mass==0:
        return sp.Integer(0)
    return (mass/row)*sp.log(mass/row)/sp.log(2)
positive_identity=sp.simplify(sp.expand_log(joint_term(p,r,y)-(conditional_term(p,r)-p*safe_log2(y))))==0
zero_identity=joint_term(0,real_cell,real_rest)==conditional_term(0,real_cell)-0*safe_log2(real_rest)==0
zero_total_implies_zero=sp.reduce_inequalities([real_cell>=0,-real_cell>=0],real_cell)==sp.Eq(real_cell,0)
Q=sp.Function('conditionalProbabilityTerm')
def map_expression(expression,rule,protected=()):
    if not isinstance(expression,sp.Basic) or not expression.args or expression.func in protected:
        return rule(expression)
    rebuilt=expression.func(*(map_expression(arg,rule,protected) for arg in expression.args))
    return rule(rebuilt)
def push_scalar(expression):
    if not expression.is_Mul:
        return expression
    sums=[arg for arg in expression.args if arg.func==S]
    if len(sums)!=1:
        return expression
    summation=sums[0]
    sequence,slot,body=summation.args
    factors=list(expression.args)
    factors.remove(summation)
    factor=sp.Mul(*factors)
    if factor.has(slot) or not sum_scale:
        return expression
    return S(sequence,slot,factor*body)
def push_all(expression):
    while True:
        transformed=map_expression(expression,push_scalar)
        if transformed==expression:
            return expression
        expression=transformed
def exchange_nested(expression):
    if expression.func!=S or expression.args[2].func!=S or not sum_exchange:
        raise ArithmeticError('exchange')
    outer_sequence,outer_slot,inner=expression.args
    inner_sequence,inner_slot,body=inner.args
    if outer_slot==inner_slot or inner_sequence.has(outer_slot) or outer_sequence.has(inner_slot):
        raise ArithmeticError('capture')
    return S(inner_sequence,inner_slot,S(outer_sequence,outer_slot,body))
def marginal_entropy_chain():
    original=-S(ys,j,C(j)*L(C(j)))
    substituted=map_expression(original,lambda value:S(xs,i,P(i,j)) if value==C(j) else value,(L,))
    distributed=push_all(substituted)
    expected_distributed=S(ys,j,S(xs,i,-P(i,j)*L(C(j))))
    if distributed!=expected_distributed:
        raise ArithmeticError('marginal scaling')
    exchanged=exchange_nested(distributed)
    expected=-S(xs,i,S(ys,j,P(i,j)*L(C(j))))
    if sp.expand(linearize(exchanged)-linearize(expected))!=0:
        raise ArithmeticError('marginal exchange')
    return original,substituted,exchanged
conditional_positive=sp.simplify(r*conditional_probability_term(p,r)-conditional_term(p,r))==0
conditional_zero=conditional_probability_term(0,real_cell)==conditional_term(0,real_cell)==0
def conditional_entropy_chain():
    original=-S(xs,i,R(i)*S(ys,j,Q(i,j)))
    distributed=push_all(original)
    def cancel_row(value):
        if value==-R(i)*Q(i,j):
            if not (conditional_positive and conditional_zero):
                raise ArithmeticError('conditional term')
            return -K(i,j)
        return value
    cancelled=map_expression(distributed,cancel_row)
    expected=-S(xs,i,S(ys,j,K(i,j)))
    if sp.expand(linearize(cancelled)-linearize(expected))!=0:
        raise ArithmeticError('conditional scaling')
    return original,distributed,cancelled
def marginal_entropy_expansion():
    marginal_entropy_chain()
    return sum_exchange and sum_scale

def conditional_entropy_expansion():
    conditional_entropy_chain()
    return sum_scale and conditional_positive and conditional_zero

def information_entropy_composition():
    source=S(xs,i,S(ys,j,J(i,j)))
    def pointwise(value):
        if value==J(i,j):
            if not (positive_identity and zero_identity and entry_le_sum_induction()):
                raise ArithmeticError('pointwise identity')
            return K(i,j)-P(i,j)*L(C(j))
        return value
    derived=map_expression(source,pointwise)
    h_y=marginal_entropy_chain()[-1]
    h_y_given_x=conditional_entropy_chain()[-1]
    return sum_subtract and sp.expand(linearize(derived)-linearize(h_y-h_y_given_x))==0
results=[]
def check(identifier,condition):
    results.append({'id':identifier,'passed':bool(condition)})
check('finite_sum_zero_induction',sum_zero)
check('finite_sum_addition_induction',sum_add)
check('finite_sum_scaling_induction',sum_scale)
check('finite_sum_subtraction_induction',sum_subtract)
check('finite_sum_exchange_induction',sum_exchange)
check('finite_sum_nonnegative_induction',sum_nonnegative_induction())
check('entry_le_finite_sum_induction',entry_le_sum_induction())
check('positive_cell_positive_marginals',(positive_cell+nonnegative_rest).is_positive is True)
check('zero_marginal_zero_cells',zero_total_implies_zero and sp.expand((real_cell+real_rest).subs(real_rest,-real_cell))==0)
check('information_positive_term_identity',positive_identity)
check('information_zero_term_identity',zero_identity and safe_log2(0)==0)
check('marginal_entropy_expansion_induction',marginal_entropy_expansion())
check('conditional_entropy_expansion_induction',conditional_entropy_expansion())
check('information_entropy_composition_induction',information_entropy_composition())
check('wrong_sum_scaling_rejected',not induction_identity(S(xs,i,c*F(i)),2*c*S(xs,i,F(i))))
check('wrong_information_sign_rejected',sp.simplify(sp.expand_log(joint_term(p,r,y)-(conditional_term(p,r)+p*safe_log2(y))))!=-0)
report={'backend':'Python/SymPy','checks':len(results),'passed':all(r['passed'] for r in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
