import json
import sympy as sp

results=[]
def check(identifier,condition):
    results.append({"id":identifier,"passed":bool(condition)})
    if not condition:
        raise AssertionError(identifier)

def softmax(scores):
    if not scores or any(sp.sympify(x).is_real is not True for x in scores):
        raise ValueError('nonempty finite real score vector required')
    weights=[sp.exp(x) for x in scores]
    partition=sum(weights)
    return [u/partition for u in weights]

def attention(q,k,v):
    q,k,v=map(sp.Matrix,(q,k,v))
    if q.rows<=0 or q.cols<=0 or k.shape!=q.shape or v.rows!=q.rows or v.cols<=0:
        raise ValueError('n>0, d_k>0 and compatible Q,K,V required')
    scores=q*k.T/sp.sqrt(q.cols)
    weights=sp.Matrix([softmax(list(scores.row(i))) for i in range(q.rows)])
    return scores,weights,weights*v

def layer(x,w1,w2,b1,b2):
    x,w1,w2,b1,b2=map(sp.Matrix,(x,w1,w2,b1,b2))
    if x.rows!=1 or w1.rows!=x.cols or w2.rows!=w1.cols or w2.cols!=x.cols or b1.shape!=(1,w1.cols) or b2.shape!=x.shape:
        raise ValueError('incompatible row-vector feed-forward dimensions')
    hidden=(x*w1+b1).applyfunc(lambda t:sp.Max(0,t))
    return hidden*w2+b2

def rejects(call):
    try:
        call()
    except ValueError:
        return True
    return False

z=sp.symbols('z',real=True)
Z,u=sp.symbols('Z u',positive=True)
check('softmax_exponential_positive',sp.exp(z).is_positive)
check('softmax_normalization_base',sp.simplify(sum(softmax([z]))-1)==0)
check('softmax_normalization_induction',sp.simplify(Z/(Z+u)+u/(Z+u)-1)==0 and (Z+u).is_positive)
check('softmax_reject_empty',rejects(lambda:softmax([])))
logits=list(map(sp.Rational,['.6','1.1','-1.5','1.2','3.2','-1.1']))
weights=softmax(logits)
check('softmax_source_distribution',sp.simplify(sum(weights)-1)==0 and all(p.is_positive for p in weights))
check('softmax_source_range',all(sp.simplify(1-p).is_positive for p in weights))
q11,q12,q21,q22,k11,k12,k21,k22,v11,v21=sp.symbols('q11 q12 q21 q22 k11 k12 k21 k22 v11 v21',real=True)
queries=sp.Matrix([[q11,q12],[q21,q22]])
keys=sp.Matrix([[k11,k12],[k21,k22]])
values=sp.Matrix([v11,v21])
scores,alpha,output=attention(queries,keys,values)
check('attention_composed_scores',all(sp.simplify(scores[i,j]-sum(queries[i,r]*keys[j,r] for r in range(2))/sp.sqrt(2))==0 for i in range(2) for j in range(2)))
check('attention_composed_weights',all(sp.simplify(alpha[i,j]-sp.exp(scores[i,j])/sum(sp.exp(scores[i,m]) for m in range(2)))==0 for i in range(2) for j in range(2)))
check('attention_composed_output',all(sp.simplify(output[i,0]-sum(sp.exp(scores[i,j])*values[j,0]/sum(sp.exp(scores[i,m]) for m in range(2)) for j in range(2)))==0 for i in range(2)))
check('attention_composed_normalization',all(sp.simplify(sum(alpha.row(i))-1)==0 for i in range(2)))
check('attention_reject_zero_key_dimension',rejects(lambda:attention(sp.zeros(2,0),sp.zeros(2,0),values)))
check('attention_reject_mismatched_keys',rejects(lambda:attention(queries,sp.zeros(3,2),values)))
check('attention_reject_mismatched_values',rejects(lambda:attention(queries,keys,sp.zeros(3,1))))
check('source_dimension_scale',sp.sqrt(sp.Rational(512,8))==8)
x1,x2,a11,a12,a21,a22,b11,b12,b21,b22,c1,c2,d1,d2=sp.symbols('x1 x2 a11 a12 a21 a22 b11 b12 b21 b22 c1 c2 d1 d2',real=True)
x=sp.Matrix([[x1,x2]])
w1=sp.Matrix([[a11,a12],[a21,a22]])
w2=sp.Matrix([[b11,b12],[b21,b22]])
b1=sp.Matrix([[c1,c2]]);b2=sp.Matrix([[d1,d2]])
ff=layer(x,w1,w2,b1,b2)
check('ffn_composed_relu',all(sp.simplify(ff[0,k]-sum(sp.Max(0,sum(x[0,r]*w1[r,j] for r in range(2))+b1[0,j])*w2[j,k] for j in range(2))-b2[0,k])==0 for k in range(2)))
check('ffn_reject_mismatched_hidden',rejects(lambda:layer(x,w1,sp.zeros(3,2),b1,b2)))
counts=sp.symbols('c0:3',integer=True,nonnegative=True)
def laplace(c):
    if not c or any(sp.sympify(a).is_integer is not True or sp.sympify(a).is_nonnegative is not True for a in c):
        raise ValueError('nonempty nonnegative integer count vector required')
    return [(a+1)/(sum(c)+len(c)) for a in c]
lp=laplace(list(counts))
check('laplace_distribution',sp.simplify(sum(lp)-1)==0 and all(p.is_positive for p in lp) and all(sp.simplify(1-p).is_nonnegative for p in lp))
check('laplace_denominator_identity',sum(c+1 for c in counts)==sum(counts)+3)
check('laplace_reject_empty',rejects(lambda:laplace([])))
check('laplace_reject_negative',rejects(lambda:laplace([-1])))
check('laplace_source_denominator',927+1446==2373 and sp.Rational(608+1,2373)>0 and sp.Rational(0+1,2373)>0)
p=sp.symbols('p',real=True)
q=sp.Rational(608,927)
ll=608*sp.log(p)+319*sp.log(1-p)
derivative=sp.diff(ll,p)
check('mle_actual_derivative',sp.cancel(derivative-(608-927*p)/(p*(1-p)))==0)
check('mle_domain_nonzero_denominator',sp.reduce_inequalities([p>0,p<1,sp.Eq(p*(1-p),0)],p)==sp.false)
check('mle_increasing_before',sp.simplify(sp.reduce_inequalities([p>0,p<q,derivative<=0],p))==sp.false)
check('mle_decreasing_after',sp.simplify(sp.reduce_inequalities([p>q,p<1,derivative>=0],p))==sp.false)
check('mle_only_critical',sp.solve(sp.together(derivative).as_numer_denom()[0],p)==[q])
L=p**608*(1-p)**319
check('mle_boundary_values',L.subs(p,0)==0 and L.subs(p,1)==0 and L.subs(p,q)>0)
check('mle_log_tangent_certificate',sp.expand(608*(p/q-1)+319*((1-p)/(1-q)-1))==0)
def brier(predictions,truth):
    p=sp.Matrix(predictions)
    if p.rows<=0 or p.cols<=0 or len(truth)!=p.rows or any(type(t) is not int or not 0<=t<p.cols for t in truth):
        raise ValueError('nonempty samples and one reference class per sample required')
    if any(sp.simplify(sum(p.row(i))-1)!=0 for i in range(p.rows)) or any(v.is_nonnegative is not True for v in p):
        raise ValueError('rows must be nonnegative probability distributions')
    return sum((p[i,j]-int(j==truth[i]))**2 for i in range(p.rows) for j in range(p.cols))/p.rows

bp,by=sp.symbols('bp by',real=True)
check('brier_binary_exact_convention',sp.expand((bp-by)**2+((1-bp)-(1-by))**2-2*(bp-by)**2)==0)
check('brier_nonnegative_sum_step',(sp.Symbol('brier_sum',nonnegative=True)+(bp-by)**2).is_nonnegative)
check('brier_nonempty_average',(sp.Symbol('brier_sum',nonnegative=True)/sp.Symbol('sample_count',positive=True)).is_nonnegative)
check('brier_reject_empty',rejects(lambda:brier([],[])))
check('brier_reject_non_normalized',rejects(lambda:brier([[1,1]],[0])))
check('brier_reject_negative_probabilities',rejects(lambda:brier([[-1,2]],[0])))
check('brier_reject_absent_class',rejects(lambda:brier([[1,0]],[2])))

count=sp.Symbol('count',integer=True,positive=True)
index=sp.Symbol('index',integer=True)
symbolic_scores=sp.IndexedBase('symbolic_scores')
actual_partition=sp.Sum(sp.exp(symbolic_scores[index]),(index,1,count))
check('softmax_general_sum',sp.factor_terms(sp.Sum(sp.exp(symbolic_scores[index])/actual_partition,(index,1,count)))==1)
symbolic_counts=sp.IndexedBase('symbolic_counts')
actual_total=sp.Sum(symbolic_counts[index],(index,1,count))
actual_laplace=sp.Sum((symbolic_counts[index]+1)/(actual_total+count),(index,1,count))
check('laplace_general_sum',sp.factor_terms(sp.factor_terms(actual_laplace).expand().doit())==1)
true_positive=sp.Symbol('true_positive',positive=True)
false_positive,false_negative=sp.symbols('false_positive false_negative',nonnegative=True)
P=true_positive/(true_positive+false_positive)
R=true_positive/(true_positive+false_negative)
check('f1_counts_identity',sp.cancel(2*P*R/(P+R)-2*true_positive/(2*true_positive+false_positive+false_negative))==0)
check('f1_counts_denominators',(true_positive+false_positive).is_positive and (true_positive+false_negative).is_positive and (2*true_positive+false_positive+false_negative).is_positive)
positive_a,positive_b=sp.symbols('positive_a positive_b',positive=True)
probability=positive_a/(positive_a+positive_b)
complement=sp.cancel(1-probability)
check('mle_log_probability_parameterization',sp.simplify(sp.expand_log(sp.log(probability**608*complement**319))-608*sp.log(probability)-319*sp.log(complement))==0)

z,y,a,w,x=sp.symbols('loss_z loss_y other_score weight feature',real=True)
sigmoid=sp.exp(z)/(1+sp.exp(z))
check('cross_entropy_full_rewrite',sp.simplify(sp.expand_log(-(y*sp.log(sigmoid)+(1-y)*sp.log(1-sigmoid)))-(sp.log(1+sp.exp(z))-y*z))==0)
check('loss_derivative_full',sp.simplify(sp.diff(sp.log(1+sp.exp(z))-y*z,z)-(sigmoid-y))==0)
check('loss_gradient_coordinate',sp.simplify(sp.diff(sp.log(1+sp.exp(a+w*x))-y*(a+w*x),w)-(sp.exp(a+w*x)/(1+sp.exp(a+w*x))-y)*x)==0)
check('sigmoid_derivative_identity',sp.simplify(sp.diff(sigmoid,z)-sigmoid*(1-sigmoid))==0)
check('sigmoid_derivative_positive',(sp.exp(z)/(1+sp.exp(z))**2).is_positive)
coeff,prob,target=sp.symbols('rate probability target',real=True)
uvec=sp.IndexedBase('uvec');vvec=sp.IndexedBase('vvec')
updated_dot=sp.Sum((uvec[index]-coeff*(prob-target)*vvec[index])*vvec[index],(index,1,count))
expected_dot=sp.Sum(uvec[index]*vvec[index],(index,1,count))-coeff*(prob-target)*sp.Sum(vvec[index]**2,(index,1,count))
check('word2vec_general_dot_update',sp.factor_terms(sp.expand(updated_dot-expected_dot).doit())==0)
gvec=sp.IndexedBase('generator');cvec=sp.IndexedBase('copy');mix=sp.Symbol('mixture_weight',real=True)
mixture_sum=sp.factor_terms(sp.Sum(mix*gvec[index]+(1-mix)*cvec[index],(index,1,count)).expand().doit())
check('mixture_general_sum',sp.expand(mixture_sum.subs({sp.Sum(gvec[index],(index,1,count)):1,sp.Sum(cvec[index],(index,1,count)):1})-1)==0)
v0,va,vb,vab=sp.symbols('value_empty value_A value_B value_AB',real=True)
import itertools
values_by_set={frozenset():v0,frozenset({'A'}):va,frozenset({'B'}):vb,frozenset({'A','B'}):vab}
contributions={'A':[],'B':[]}
for order in itertools.permutations(['A','B']):
    previous=frozenset()
    for head in order:
        current=previous|{head}
        contributions[head].append(values_by_set[current]-values_by_set[previous])
        previous=current
phi_a=sum(contributions['A'])/2;phi_b=sum(contributions['B'])/2
check('shapley_two_orders',sp.expand(phi_a-((va-v0)+(vab-vb))/2)==0 and sp.expand(phi_b-((vb-v0)+(vab-va))/2)==0)
check('shapley_two_efficiency',sp.expand(phi_a+phi_b-(vab-v0))==0)

report={"backend":"Python/SymPy","checks":len(results),"passed":all(r['passed'] for r in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
