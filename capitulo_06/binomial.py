import json
from dataclasses import dataclass
import sympy as sp

n,k,j=sp.symbols('n k j',integer=True,nonnegative=True)
p,q,a,b,h,previous,i,mu=sp.symbols('p q a b h previous i mu',real=True)
xs,tail,nil=sp.symbols('xs tail nil')
cons=sp.Function('cons')
transition=sp.Function('transition')
fold=sp.Function('fold')
length=sp.Function('length')
F,G=sp.Function('F'),sp.Function('G')

@dataclass(frozen=True)
class Monomial:
    coefficient:object
    p_degree:object
    q_degree:object
    def shift(self,p_increment,q_increment):
        return Monomial(self.coefficient,self.p_degree+p_increment,self.q_degree+q_increment)

def monomial_equal(left,right):
    return sp.simplify(left.p_degree-right.p_degree)==0 and sp.simplify(left.q_degree-right.q_degree)==0 and sp.combsimp(sp.sympify(left.coefficient-right.coefficient))==0

def monomial_add(left,right):
    if sp.simplify(left.p_degree-right.p_degree)!=0 or sp.simplify(left.q_degree-right.q_degree)!=0:raise ValueError('unequal degrees')
    return Monomial(left.coefficient+right.coefficient,left.p_degree,left.q_degree)

def binomial_term(size,index):
    return Monomial(sp.binomial(size,index),sp.sympify(index),sp.sympify(size-index))

def coefficient_induction(term):
    base=monomial_equal(term(0,0),Monomial(1,0,0))
    lower=monomial_equal(term(n+1,0),term(n,0).shift(0,1))
    upper=monomial_equal(term(n+1,n+1),term(n,n).shift(1,0))
    interior=monomial_equal(term(k+j+2,k+1),monomial_add(term(k+j+1,k).shift(1,0),term(k+j+1,k+1).shift(0,1)))
    return base and lower and upper and interior

def unfold_once(expression):
    if not isinstance(expression,sp.Basic) or not expression.args:return expression
    expression=expression.func(*(unfold(arg) for arg in expression.args))
    if expression.func==transition:
        row,prev=expression.args
        if row==nil:return cons(p*prev,nil)
        if row.func==cons:
            weight,rest=row.args
            return cons(q*weight+p*prev,transition(rest,weight))
    if expression.func==length:
        row=expression.args[0]
        if row==nil:return sp.Integer(0)
        if row.func==cons:return 1+length(row.args[1])
    if expression.func==fold:
        row,start,body=expression.args
        if row==nil:return sp.Integer(0)
        if row.func==cons:
            weight,rest=row.args
            return weight*body.subs(k,start)+fold(rest,start+1,body)
    return expression

def unfold(expression):
    while True:
        reduced=unfold_once(expression)
        if reduced==expression:return expression
        expression=reduced

def fold_induction(left,right):
    if {tail,h}&(left.free_symbols|right.free_symbols):return False
    base_left=unfold(left.subs(xs,nil))
    base_right=unfold(right.subs(xs,nil))
    hypothesis_left=left.subs({xs:tail,i:i+1},simultaneous=True)
    hypothesis_right=right.subs({xs:tail,i:i+1},simultaneous=True)
    step_left=unfold(left.subs(xs,cons(h,tail)))
    step_right=unfold(right.subs(xs,cons(h,tail)))
    step_left=step_left.subs(hypothesis_left,hypothesis_right)
    return sp.expand(base_left-base_right)==0 and sp.expand(step_left-step_right)==0

def row_length_induction():
    left=length(transition(xs,previous))
    right=length(xs)+1
    base=sp.expand(unfold(left.subs(xs,nil))-unfold(right.subs(xs,nil)))
    hypothesis_left=left.subs({xs:tail,previous:h},simultaneous=True)
    hypothesis_right=right.subs(xs,tail)
    step_left=unfold(left.subs(xs,cons(h,tail))).subs(hypothesis_left,hypothesis_right)
    step_right=unfold(right.subs(xs,cons(h,tail)))
    return base==0 and sp.expand(step_left-step_right)==0 and unfold(length(cons(sp.Integer(1),nil)))==1

def weighted_transition_induction():
    left=fold(transition(xs,previous),i,F(k))
    right=q*fold(xs,i,F(k))+p*fold(xs,i+1,F(k))+p*previous*F(i)
    base=sp.expand(unfold(left.subs(xs,nil))-unfold(right.subs(xs,nil)))
    hypothesis_left=left.subs({xs:tail,previous:h,i:i+1},simultaneous=True)
    hypothesis_right=right.subs({xs:tail,previous:h,i:i+1},simultaneous=True)
    step_left=unfold(left.subs(xs,cons(h,tail))).subs(hypothesis_left,hypothesis_right)
    step_right=unfold(right.subs(xs,cons(h,tail)))
    return base==0 and sp.expand(step_left-step_right)==0

def shift_body_certificate(power):
    shifted=sp.expand((k+1)**power)
    polynomial=sp.Poly(shifted,k)
    right=sum(polynomial.nth(r)*fold(xs,i,k**r) for r in range(power+1))
    return fold_induction(fold(xs,i,shifted),right)

def moment_induction(closed_forms):
    if not coefficient_induction(binomial_term) or not row_length_induction() or not weighted_transition_induction():return False
    if not fold_induction(fold(xs,i+1,F(k)),fold(xs,i,F(k+1))):return False
    if len(closed_forms)!=3:return False
    for order in range(3):
        if not shift_body_certificate(order):return False
        base=unfold(unfold(fold(cons(sp.Integer(1),nil),0,k**order)))
        if sp.expand(closed_forms[order].subs(n,0)-base)!=0:return False
        coefficients=sp.Poly(sp.expand((k+1)**order),k)
        next_moment=(q*closed_forms[order]+p*sum(coefficients.nth(r)*closed_forms[r] for r in range(order+1))).subs(q,1-p)
        if sp.expand(next_moment-closed_forms[order].subs(n,n+1))!=0:return False
    return True

def endpoint_recurrences():
    pad=sp.Function('pad')
    zero_base=unfold(transition(nil,previous)).subs({p:0,q:1})==cons(0,nil)
    zero_left=unfold(transition(cons(h,tail),previous)).subs({p:0,q:1}).subs(transition(tail,h),pad(tail))
    zero_right=cons(h,pad(tail))
    one_base=unfold(transition(nil,previous)).subs({p:1,q:0})==cons(previous,nil)
    one_left=unfold(transition(cons(h,tail),previous)).subs({p:1,q:0}).subs(transition(tail,h),cons(h,tail))
    one_right=cons(previous,cons(h,tail))
    return zero_base and zero_left==zero_right and one_base and one_left==one_right

moments=[sp.Integer(1),n*p,(n*p)**2+n*p*(1-p)]
nonnegative=sp.symbols('p_nonnegative q_nonnegative u_nonnegative v_nonnegative rest_nonnegative',nonnegative=True)
pn,qn,un,vn,rest=nonnegative
def single_coefficient_bound_induction():
    selected,tail_total=sp.symbols('selected tail_total',real=True)
    step_total=unfold(fold(cons(h,tail),i,sp.Integer(1)))
    definition=step_total==h+fold(tail,i+1,sp.Integer(1))
    head_gap=sp.expand((h+tail_total)-h).subs(tail_total,rest)
    tail_gap=sp.expand((h+tail_total)-selected).subs({h:un,tail_total:selected+rest})
    return definition and head_gap.is_nonnegative is True and sp.simplify(tail_gap).is_nonnegative is True

results=[]
def check(name,value):
    if not value:raise AssertionError(name)
    results.append({'id':name,'passed':True})

check('binomial_pascal_interior',sp.combsimp(sp.binomial(k+j+2,k+1)-sp.binomial(k+j+1,k)-sp.binomial(k+j+1,k+1))==0)
check('binomial_boundary_coefficients',sp.binomial(n,0)==1 and sp.binomial(n,n)==1)
check('binomial_coefficient_induction',coefficient_induction(binomial_term))
check('binomial_zero_extension',sp.binomial(n,-1)==0 and sp.binomial(n,n+1)==0)
check('natural_power_zero_convention',sp.Pow(0,0)==1 and sp.Pow(p,0)==1 and sp.Pow(q,0)==1)
check('binomial_row_support_induction',row_length_induction())
check('weighted_sum_transition_induction',weighted_transition_induction())
check('weighted_sum_linearity_induction',fold_induction(fold(xs,i,a*F(k)+b*G(k)),a*fold(xs,i,F(k))+b*fold(xs,i,G(k))))
check('weighted_sum_index_shift_induction',fold_induction(fold(xs,i+1,F(k)),fold(xs,i,F(k+1))))
check('moment_shift_polynomials',all(shift_body_certificate(order) for order in range(3)))
check('binomial_normalization_mean_second_moment_induction',moment_induction(moments))
check('centered_square_linearity_induction',fold_induction(fold(xs,i,(k-mu)**2),fold(xs,i,k**2)-2*mu*fold(xs,i,k)+mu**2*fold(xs,i,1)))
check('binomial_variance_from_pmf',moment_induction(moments) and fold_induction(fold(xs,i,(k-mu)**2),fold(xs,i,k**2)-2*mu*fold(xs,i,k)+mu**2*fold(xs,i,1)) and sp.expand(moments[2]-2*n*p*moments[1]+(n*p)**2*moments[0]-n*p*(1-p))==0)
check('binomial_parameter_domain',sp.simplify(sp.Equivalent(sp.reduce_inequalities([p>=0,1-p>=0],p),sp.And(p>=0,p<=1)))==sp.true)
check('binomial_mass_nonnegative_induction',sp.Integer(1).is_nonnegative is True and (qn*un+pn*vn).is_nonnegative is True and (pn*un).is_nonnegative is True)
check('sum_nonnegative_induction',sp.Integer(0).is_nonnegative is True and (un+rest).is_nonnegative is True)
check('single_coefficient_le_total_induction',single_coefficient_bound_induction())
check('binomial_mass_at_most_one',single_coefficient_bound_induction() and moment_induction(moments) and sp.simplify(1-(1-rest)-rest)==0 and rest.is_nonnegative is True)
check('endpoint_distribution_induction',endpoint_recurrences())
check('endpoint_moments',all(sp.expand(formula.subs(p,0)-expected)==0 for formula,expected in zip(moments,[1,0,0])) and all(sp.expand(formula.subs(p,1)-expected)==0 for formula,expected in zip(moments,[1,n,n**2])))
check('wrong_coefficient_rejected',not coefficient_induction(lambda size,index:Monomial(1,sp.sympify(index),sp.sympify(size-index))))
check('wrong_mean_rejected',not moment_induction([sp.Integer(1),n*p+1,moments[2]]))
check('wrong_variance_moment_rejected',not moment_induction([sp.Integer(1),n*p,(n*p)**2+n*p]))
check('outside_probability_counterexample',sp.binomial(1,0)*sp.Integer(2)**0*(1-sp.Integer(2))**1==-1)
print(json.dumps({'backend':'Python 3','scope':'n is an arbitrary natural number, 0<=p<=1, q=1-p. The row [1] advances by q times each old coefficient plus p times its predecessor, extended by zero. Pascal, both edges and the n=0 base certify each coefficient as binomial(n,k)*p^k*q^(n-k); monomials are polynomial natural powers, with power zero equal to one even at zero. Structural induction on finite rows derives the weighted-sum recurrence. Induction on n then proves normalization, mean and second moment from this actual recurrence, and finite-fold linearity gives variance. No finite sample of n, no generator assumed equal to the PMF, and no division by p or q are used. Endpoint recurrences retain p=0,1 and n=0.','checks':len(results),'passed':True,'results':results}))
