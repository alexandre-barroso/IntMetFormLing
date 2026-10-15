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

import contextlib
import io
with contextlib.redirect_stdout(io.StringIO()) as binary_output:
    import escolhas as binary
binary_run=json.loads(binary_output.getvalue())
if binary_run.get('passed') is not True or binary_run.get('checks')!=18 or not all(r.get('passed') is True for r in binary_run['results']):raise AssertionError('binary enumeration dependency')

word_nil,family_nil,family,other_family,word_head,family_tail=sp.symbols('word_nil family_nil family other_family word_head family_tail')
word_cons,family_cons,family_append,prefix_map,binary_tree,word_weight,word_ones,tree_sum,binomial_row=map(sp.Function,['word_cons','family_cons','family_append','prefix_map','binary_tree','word_weight','word_ones','tree_sum','binomial_row'])
tree_proved=set()

def tree_reduce_once(expression):
    if not isinstance(expression,sp.Basic) or not expression.args:return expression
    expression=expression.func(*(tree_reduce(arg) for arg in expression.args))
    if expression.func==word_weight:
        word=expression.args[0]
        if word==word_nil:return sp.Integer(1)
        if word.func==word_cons:
            bit,rest=word.args
            if bit==0:return q*word_weight(rest)
            if bit==1:return p*word_weight(rest)
    if expression.func==word_ones:
        word=expression.args[0]
        if word==word_nil:return sp.Integer(0)
        if word.func==word_cons:
            bit,rest=word.args
            if bit==0:return word_ones(rest)
            if bit==1:return word_ones(rest)+1
    if expression.func==family_append:
        left,right=expression.args
        if left==family_nil:return right
        if left.func==family_cons:return family_cons(left.args[0],family_append(left.args[1],right))
    if expression.func==prefix_map:
        bit,words=expression.args
        if words==family_nil:return family_nil
        if words.func==family_cons:return family_cons(word_cons(bit,words.args[0]),prefix_map(bit,words.args[1]))
    if expression.func==binary_tree:
        size=expression.args[0]
        if size==0:return family_cons(word_nil,family_nil)
        if size==n+1:return family_append(prefix_map(0,binary_tree(n)),prefix_map(1,binary_tree(n)))
    if expression.func==binomial_row:
        size=expression.args[0]
        if size==0:return cons(1,nil)
        if size==n+1:return transition(binomial_row(n),0)
    if expression.func==tree_sum:
        words,body=expression.args
        if words==family_nil:return sp.Integer(0)
        if words.func==family_cons:return word_weight(words.args[0])*body.subs(k,word_ones(words.args[0]))+tree_sum(words.args[1],body)
        if words.func==family_append and 'sum_append' in tree_proved:return tree_sum(words.args[0],body)+tree_sum(words.args[1],body)
        if words.func==prefix_map:
            bit,rest=words.args
            if bit==0 and 'sum_prefix_zero' in tree_proved:return q*tree_sum(rest,body)
            if bit==1 and 'sum_prefix_one' in tree_proved:return p*tree_sum(rest,body.subs(k,k+1))
    return unfold(expression)

def tree_reduce(expression):
    expression=sp.sympify(expression)
    while True:
        reduced=tree_reduce_once(expression)
        if reduced==expression:return expression
        expression=reduced

def tree_family_induction(left,right):
    if {word_head,family_tail}&(left.free_symbols|right.free_symbols):return False
    base=sp.expand(tree_reduce(left.subs(family,family_nil))-tree_reduce(right.subs(family,family_nil)))
    ih_left=tree_reduce(left.subs(family,family_tail))
    ih_right=tree_reduce(right.subs(family,family_tail))
    step_left=tree_reduce(left.subs(family,family_cons(word_head,family_tail)))
    step_right=tree_reduce(right.subs(family,family_cons(word_head,family_tail)))
    return base==0 and sp.expand(tree_reduce(step_left.subs(ih_left,ih_right))-step_right)==0

tree_rules={
    'sum_append':(tree_sum(family_append(family,other_family),F(k)),tree_sum(family,F(k))+tree_sum(other_family,F(k))),
    'sum_prefix_zero':(tree_sum(prefix_map(0,family),F(k)),q*tree_sum(family,F(k))),
    'sum_prefix_one':(tree_sum(prefix_map(1,family),F(k)),p*tree_sum(family,F(k+1)))
}

def tree_certify(name,left,right):
    if name not in tree_rules or tree_rules[name]!=(left,right):return False
    if name in tree_proved:return True
    valid=tree_family_induction(left,right)
    if valid:tree_proved.add(name)
    return valid

def binary_enumeration_certificate():
    b=binary
    expected_base=b.term('fcons',b.SNIL,b.FNIL)
    expected_step=b.term('append',b.term('map',b.BIT0,b.term('enum',b.n)),b.term('map',b.BIT1,b.term('enum',b.n)))
    exact_definitions=b.normalize(b.term('enum',b.ZERO))==expected_base and b.normalize(b.term('enum',b.term('succ',b.n)))==expected_step
    own_definitions=tree_reduce(binary_tree(0))==family_cons(word_nil,family_nil) and tree_reduce(binary_tree(n+1))==family_append(prefix_map(0,binary_tree(n)),prefix_map(1,binary_tree(n)))
    return exact_definitions and own_definitions and b.coverage_induction() and b.natural_induction(b.term('unique',b.term('enum',b.n)),b.TRUE,b.n)

def sequence_count_law(zero_factor=q,one_factor=p):
    if not binary_enumeration_certificate():return False
    if not all(tree_certify(name,*target) for name,target in tree_rules.items()):return False
    if not coefficient_induction(binomial_term) or not weighted_transition_induction():return False
    if not fold_induction(fold(xs,i+1,F(k)),fold(xs,i,F(k+1))):return False
    sequence_base=tree_reduce(tree_sum(binary_tree(0),F(k)))
    count_base=tree_reduce(fold(binomial_row(0),0,F(k)))
    if sequence_base!=count_base:return False
    sequence_next=tree_reduce(tree_sum(binary_tree(n+1),F(k)))
    expected_sequence_next=zero_factor*tree_sum(binary_tree(n),F(k))+one_factor*tree_sum(binary_tree(n),F(k+1))
    if sp.expand(sequence_next-expected_sequence_next)!=0:return False
    count_next=tree_reduce(fold(binomial_row(n+1),0,F(k)))
    transition_left=fold(transition(xs,previous),i,F(k))
    transition_right=q*fold(xs,i,F(k))+p*fold(xs,i+1,F(k))+p*previous*F(i)
    replacements={xs:binomial_row(n),previous:0,i:0}
    count_next=count_next.subs(transition_left.subs(replacements,simultaneous=True),transition_right.subs(replacements,simultaneous=True))
    count_next=count_next.subs(fold(binomial_row(n),1,F(k)),fold(binomial_row(n),0,F(k+1)))
    sequence_next=sequence_next.subs(tree_sum(binary_tree(n),F(k)),fold(binomial_row(n),0,F(k)))
    sequence_next=sequence_next.subs(tree_sum(binary_tree(n),F(k+1)),fold(binomial_row(n),0,F(k+1)))
    return sp.expand(sequence_next-count_next)==0

beta=sp.symbols('beta',integer=True,positive=True)
beta1,beta2=sp.symbols('beta1 beta2',integer=True,positive=True)
delta=sp.symbols('delta',integer=True,nonnegative=True)
delta_strict=sp.symbols('delta_strict',integer=True,positive=True)
pp,qq=sp.symbols('p_positive q_positive',positive=True)

def bootstrap_average_certificate(proposed_mean,proposed_variance,repetitions=beta):
    if repetitions.is_integer is not True or repetitions.is_positive is not True:return False
    if not sequence_count_law() or not moment_induction(moments):return False
    mean_left=fold(xs,i,k/repetitions)
    mean_right=fold(xs,i,k)/repetitions
    variance_left=fold(xs,i,(k/repetitions-p)**2)
    variance_right=fold(xs,i,k**2)/repetitions**2-2*p*fold(xs,i,k)/repetitions+p**2*fold(xs,i,sp.Integer(1))
    if not fold_induction(mean_left,mean_right) or not fold_induction(variance_left,variance_right):return False
    m0,m1,m2=[formula.subs(n,repetitions) for formula in moments]
    expected_mean=m1/repetitions
    expected_variance=m2/repetitions**2-2*p*m1/repetitions+p**2*m0
    return sp.cancel(expected_mean-proposed_mean)==0 and sp.cancel(expected_variance-proposed_variance)==0

def monotonicity_certificate(proposed_gap):
    if not bootstrap_average_certificate(p,p*(1-p)/beta):return False
    variance=lambda count:p*(1-p)/count
    exact_gap=variance(beta1)-variance(beta2)
    if sp.cancel(exact_gap-proposed_gap)!=0:return False
    expanded_gap=sp.cancel(proposed_gap.subs(beta2,beta1+delta)-p*(1-p)*delta/(beta1*(beta1+delta)))
    domain=sp.simplify(sp.Equivalent(sp.reduce_inequalities([p>=0,1-p>=0],p),sp.And(p>=0,p<=1)))==sp.true
    weak=(pn*qn*delta/(beta1*(beta1+delta))).is_nonnegative is True
    strict=(pp*qq*delta_strict/(beta1*(beta1+delta_strict))).is_positive is True
    return expanded_gap==0 and domain and weak and strict

results=[]
def check(name,value):
    if not value:raise AssertionError(name)
    results.append({'id':name,'passed':True})

check('binary_sequences_complete_and_unique',binary_enumeration_certificate())
check('sequence_product_weight_base_and_branches',tree_reduce(word_weight(word_nil))==1 and tree_reduce(word_weight(word_cons(0,word_head)))==q*word_weight(word_head) and tree_reduce(word_weight(word_cons(1,word_head)))==p*word_weight(word_head))
check('success_count_base_and_branches',tree_reduce(word_ones(word_nil))==0 and tree_reduce(word_ones(word_cons(0,word_head)))==word_ones(word_head) and tree_reduce(word_ones(word_cons(1,word_head)))==word_ones(word_head)+1)
check('sequence_sum_append_induction',tree_certify('sum_append',*tree_rules['sum_append']))
check('sequence_sum_zero_prefix_induction',tree_certify('sum_prefix_zero',*tree_rules['sum_prefix_zero']))
check('sequence_sum_one_prefix_induction',tree_certify('sum_prefix_one',*tree_rules['sum_prefix_one']))
check('independent_sequence_count_binomial_law',sequence_count_law())
check('incorrect_zero_branch_weight_rejected',not sequence_count_law(p,p))
check('omitted_success_increment_rejected',not tree_certify('sum_prefix_one',tree_sum(prefix_map(1,family),F(k)),p*tree_sum(family,F(k))))
check('binomial_coefficients_from_independent_trial_convolution',coefficient_induction(binomial_term) and row_length_induction() and weighted_transition_induction())
check('binomial_normalization_mean_second_moment_induction',moment_induction(moments))
check('probability_parameter_domain',sp.simplify(sp.Equivalent(sp.reduce_inequalities([p>=0,1-p>=0],p),sp.And(p>=0,p<=1)))==sp.true)
check('probability_mass_nonnegative_induction',sp.Integer(1).is_nonnegative is True and (qn*un+pn*vn).is_nonnegative is True and (pn*un).is_nonnegative is True)
check('average_expectation_scaling_induction',fold_induction(fold(xs,i,k/beta),fold(xs,i,k)/beta))
check('average_centered_square_expansion_induction',fold_induction(fold(xs,i,(k/beta-p)**2),fold(xs,i,k**2)/beta**2-2*p*fold(xs,i,k)/beta+p**2*fold(xs,i,sp.Integer(1))))
check('bootstrap_average_mean_and_variance',bootstrap_average_certificate(p,p*(1-p)/beta))
check('variance_decrease_exact_difference',sp.cancel(p*(1-p)/beta1-p*(1-p)/beta2-p*(1-p)*(beta2-beta1)/(beta1*beta2))==0)
check('variance_nonstrict_and_strict_monotonicity',monotonicity_certificate(p*(1-p)*(beta2-beta1)/(beta1*beta2)))
check('endpoint_variance_zero',endpoint_recurrences() and all(sp.cancel((p*(1-p)/beta).subs(p,endpoint))==0 for endpoint in [0,1]))
check('equal_repetitions_equal_variance',sp.cancel((p*(1-p)*(beta2-beta1)/(beta1*beta2)).subs(beta2,beta1))==0)
check('dependence_counterexample',sp.Rational(1,2)*(0-sp.Rational(1,2))**2+sp.Rational(1,2)*(1-sp.Rational(1,2))**2==sp.Rational(1,4) and sp.Rational(1,2)*(1-sp.Rational(1,2))/2==sp.Rational(1,8) and sp.Rational(1,4)!=sp.Rational(1,8))
check('wrong_variance_power_rejected',not bootstrap_average_certificate(p,p*(1-p)/beta**2))
check('wrong_mean_rejected',not bootstrap_average_certificate(p+1,p*(1-p)/beta))
check('zero_repetitions_rejected',not bootstrap_average_certificate(p,p*(1-p),sp.Integer(0)))
check('noninteger_repetitions_rejected',not bootstrap_average_certificate(p,p*(1-p),sp.Rational(1,2)))
check('wrong_monotonicity_sign_rejected',not monotonicity_certificate(-p*(1-p)*(beta2-beta1)/(beta1*beta2)))
check('outside_probability_counterexample',sp.binomial(1,0)*sp.Integer(2)**0*(1-sp.Integer(2))**1==-1)
print(json.dumps({'backend':'Python 3','scope':'Conditional on a fixed observed corpus and fixed p in [0,1], the b>0 indicators are independent Bernoulli(p). The complete, duplicate-free binary-word enumeration has product weights q=1-p for zero and p for one and a recursive count of ones. Structural induction on finite weighted families derives prefix splitting, and induction on b proves its weighted expectations equal the actual binomial convolution row for arbitrary functions of the count. Its coefficients and moments are then certified by structural induction, including p=0 and p=1. Finite-fold linearity proves E[S/b]=p and Var(S/b)=p(1-p)/b. Increasing the positive integer b decreases this variance, strictly only for 0<p<1 and a strict increase of b. The corpus is fixed as a model hypothesis; this does not assert reduction of sampling uncertainty or acquisition of new observations. A perfectly dependent two-replicate counterexample rejects the iid formula without independence.','checks':len(results),'passed':True,'results':results}))
