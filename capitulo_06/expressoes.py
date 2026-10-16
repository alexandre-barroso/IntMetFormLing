import json
import sympy as sp

results=[]
def check(identifier,condition):
    results.append({"id":identifier,"passed":bool(condition)})
Q=sp.Rational
acc=[0,1,1,2,3,3,4,3];gen=[0,1,2,2,0,0,3,4]
joint=sp.Matrix(5,5,lambda i,j:Q(sum(a==i and b==j for a,b in zip(acc,gen)),8))
check("joint_from_classes",joint==sp.Matrix([[1,0,0,0,0],[0,1,1,0,0],[0,0,1,0,0],[2,0,0,0,1],[0,0,0,1,0]])/8)
px=[sum(joint.row(i)) for i in range(5)];py=[sum(joint.col(j)) for j in range(5)]
check("marginal_from_classes",px==list(map(lambda v:Q(v,8),[1,2,1,3,1])) and py==list(map(lambda v:Q(v,8),[3,1,2,1,1])))
check("marginal_count_plot",[(j+1,8*py[j]) for j in range(5)]==[(1,3),(2,1),(3,2),(4,1),(5,1)])
check("observed_es_count_plot",[(j+1,8*joint[1,j]) for j in range(5)]==[(1,0),(2,1),(3,1),(4,0),(5,0)])
check("conditional_from_classes", [joint[1,1]/px[1],joint[1,1]/py[1],joint[3,0]/px[3],joint[3,4]/px[3]]==[Q(1,2),1,Q(2,3),Q(1,3)])
check("joint_not_independent",joint[1,1]!=px[1]*py[1])
p,x,y=sp.symbols('p x y',positive=True)
check("log_zero_weight",sp.limit(p*sp.log(p/(x*y),2),p,0,dir='+')==0)
check("mutual_term",sp.simplify(sp.expand_log(p*sp.log(p/x,2)-p*sp.log(y,2)-p*sp.log(p/(x*y),2)))==0)
a,b,c=sp.symbols('a b c',real=True)
check("marginal_entropy_expansion_base", 0*c==0)
check("marginal_entropy_expansion_step",sp.expand((a+b)*c-a*c-b*c)==0)
check("information_entropy_identity_step",sp.expand((-a)-(-b)-(b-a))==0)
H=lambda ps:-sum(t*sp.log(t,2) for t in ps if t!=0)
hy=H(py)
hcond=sum(px[i]*H([joint[i,j]/px[i] for j in range(5)]) for i in range(5))
mi=sum(joint[i,j]*sp.log(joint[i,j]/(px[i]*py[j]),2) for i in range(5) for j in range(5) if joint[i,j])
check("information_entropy_identity",sp.simplify(sp.expand_log(hy-hcond-mi))==0)
n=sp.symbols('n',integer=True,nonnegative=True)
z=sp.symbols('z',positive=True)
k=sp.symbols('k',integer=True,positive=True)
check("binomial_pascal",sp.combsimp(sp.binomial(n+1,k)-sp.binomial(n,k)-sp.binomial(n,k-1))==0)
check("binomial_boundary",sp.binomial(n,0)==1 and sp.binomial(n,n)==1)
g=(1-p+p*z)**n
check("binomial_generating_base",g.subs(n,0)==1)
check("binomial_generating_step",sp.simplify(g.subs(n,n+1)-(1-p+p*z)*g)==0)
check("binomial_total",sp.simplify(g.subs(z,1))==1)
check("binomial_mean",sp.simplify(sp.diff(g,z).subs(z,1)-n*p)==0)
check("binomial_second_moment",sp.simplify((sp.diff(g,z,2)+sp.diff(g,z)).subs(z,1)-((n*p)**2+n*p*(1-p)))==0)
check("binomial_variance",sp.simplify((sp.diff(g,z,2)+sp.diff(g,z)).subs(z,1)-sp.diff(g,z).subs(z,1)**2-n*p*(1-p))==0)
def binomial_distribution(n_trials,probability):
    if not isinstance(n_trials,int) or n_trials<0 or probability<0 or probability>1:
        return None
    return [sp.binomial(n_trials,k)*probability**k*(1-probability)**(n_trials-k) for k in range(n_trials+1)]
check("binomial_invalid_parameter_rejected",binomial_distribution(1,Q(2)) is None and binomial_distribution(-1,Q(1,2)) is None)
check("negative_binomial_counterexample",sp.binomial(1,0)*Q(2)**0*(1-Q(2))**1==-1)
check("binomial_boundary_distributions",binomial_distribution(0,Q(0))==[1] and binomial_distribution(0,Q(1))==[1] and binomial_distribution(1,Q(0))==[1,0] and binomial_distribution(1,Q(1))==[0,1])
pmf=binomial_distribution(100,Q(1,1000))
check("binomial_source_probability_domain",sum(pmf)==1 and all(0<=v<=1 for v in pmf))
check("binomial_source_mean_variance",sum(k*v for k,v in enumerate(pmf))==Q(1,10) and sum((k-Q(1,10))**2*v for k,v in enumerate(pmf))==Q(999,10000))
check("greek_joint_valid",sum(joint)==1 and all(v>=0 for v in joint))
check("greek_conditionals_valid",all(px[i]>0 and sum(joint[i,j]/px[i] for j in range(5))==1 and all(joint[i,j]/px[i]>=0 for j in range(5)) for i in range(5)))
check("greek_entropy_from_classes",sp.simplify(sp.expand_log(hy-(Q(11,4)-Q(3,8)*sp.log(3,2))))==0)
check("greek_conditional_entropy_from_classes",sp.simplify(sp.expand_log(hcond-Q(3,8)*sp.log(3,2)))==0)
check("greek_mutual_information_from_classes",sp.simplify(sp.expand_log(mi-(Q(11,4)-Q(3,4)*sp.log(3,2))))==0)
def conditional_row(matrix,i):
    mass=sum(matrix.row(i))
    return None if mass==0 else [v/mass for v in matrix.row(i)]
def valid_information(matrix):
    if sum(matrix)!=1 or any(v<0 for v in matrix):
        return None
    r=[sum(matrix.row(i)) for i in range(matrix.rows)]
    c=[sum(matrix.col(j)) for j in range(matrix.cols)]
    value=sum(matrix[i,j]*sp.log(matrix[i,j]/(r[i]*c[j]),2) for i in range(matrix.rows) for j in range(matrix.cols) if matrix[i,j]>0)
    conditional=sum(r[i]*H(conditional_row(matrix,i)) for i in range(matrix.rows) if r[i]>0)
    return sp.simplify(value),sp.simplify(H(c)-conditional)
zero_margin=sp.Matrix([[1,0],[0,0]])
check("zero_margin_information_boundary",valid_information(zero_margin)==(0,0) and conditional_row(zero_margin,1) is None)
check("probability_rejects_negative_mass",valid_information(sp.Matrix([[2,-1]])) is None)
duration,scale=sp.symbols('duration scale',positive=True)
location=sp.symbols('location',real=True)
normal_coordinate=(sp.log(duration)-location)/scale
density=sp.exp(-(sp.log(duration)-location)**2/(2*scale**2))/(duration*scale*sp.sqrt(2*sp.pi))
normal_density=lambda z:sp.exp(-z**2/2)/sp.sqrt(2*sp.pi)
check("lognormal_density_positive",density.is_positive is True)
check("lognormal_change_variable_jacobian",sp.simplify(normal_density(normal_coordinate)*sp.diff(normal_coordinate,duration)-density)==0)
normal_cdf=(1+sp.erf(normal_coordinate/sp.sqrt(2)))/2
check("lognormal_interval_antiderivative",sp.simplify(sp.diff(normal_cdf,duration)-density)==0)
normal_variable=sp.symbols('normal_variable',real=True)
check("lognormal_standard_normal_total",sp.integrate(normal_density(normal_variable),(normal_variable,-sp.oo,sp.oo))==1)
check("lognormal_cdf_limits",sp.limit(normal_cdf,duration,0,dir='+')==0 and sp.limit(normal_cdf,duration,sp.oo)==1)
interval_start,interval_width=sp.symbols('interval_start interval_width',positive=True)
interval_end=interval_start+interval_width
normal_primitive=sp.integrate(normal_density(normal_variable),normal_variable)
normal_lower=normal_coordinate.subs(duration,interval_start)
normal_upper=normal_coordinate.subs(duration,interval_end)
normal_interval=normal_primitive.subs(normal_variable,normal_upper)-normal_primitive.subs(normal_variable,normal_lower)
original_interval=normal_cdf.subs(duration,interval_end)-normal_cdf.subs(duration,interval_start)
check("lognormal_interval_endpoints",sp.simplify(normal_lower-(sp.log(interval_start)-location)/scale)==0 and sp.simplify(normal_upper-(sp.log(interval_end)-location)/scale)==0)
check("lognormal_interval_cdf_difference",sp.simplify(normal_interval-original_interval)==0)
check("lognormal_interval_degenerate",sp.simplify(original_interval.subs(interval_width,0))==0 and sp.simplify(normal_interval.subs(interval_width,0))==0)
check("lognormal_transformation_order",sp.simplify(sp.diff(normal_coordinate,duration)).is_positive is True)
def guarded_pmi(joint_mass,row_mass,column_mass):
    if joint_mass<=0 or row_mass<=0 or column_mass<=0:
        return None
    return sp.log(joint_mass/(row_mass*column_mass),2)
check("pmi_zero_rejected",guarded_pmi(0,Q(1,2),Q(1,2)) is None and guarded_pmi(Q(1,2),0,Q(1,2)) is None and guarded_pmi(Q(1,2),Q(1,2),0) is None)
positive_joint,positive_row,positive_column=sp.symbols('positive_joint positive_row positive_column',positive=True)
check("pmi_positive_domain",(positive_joint/(positive_row*positive_column)).is_positive is True and guarded_pmi(positive_joint,positive_row,positive_column)==sp.log(positive_joint/(positive_row*positive_column),2))
constant_cell=[0]*8
constant_joint=sp.Matrix(1,5,lambda i,j:Q(sum(z==i and y==j for z,y in zip(constant_cell,gen)),8))
check("constant_cell_joint_from_classes",list(constant_joint)==py and sum(constant_joint)==1)
constant_entropy=sum(constant_joint)*H([v/sum(constant_joint) for v in constant_joint])
check("constant_cell_no_information",sp.simplify(constant_entropy-H(py))==0)
count_success,count_failure=sp.symbols('count_success count_failure',integer=True,nonnegative=True)
prob_success,prob_failure=sp.symbols('prob_success prob_failure',nonnegative=True)
nonnegative_binomial_term=sp.binomial(count_success+count_failure,count_success)*prob_success**count_success*prob_failure**count_failure
check("binomial_nonnegative_general",nonnegative_binomial_term.is_nonnegative is True)
constant_conditional_reverse=sum(py[j]*H([constant_joint[i,j]/py[j] for i in range(constant_joint.rows)]) for j in range(constant_joint.cols))
constant_information=sum(constant_joint[i,j]*sp.log(constant_joint[i,j]/(sum(constant_joint.row(i))*py[j]),2) for i in range(constant_joint.rows) for j in range(constant_joint.cols) if constant_joint[i,j]>0)
check("constant_cell_conditional_entropy_zero",sp.simplify(constant_conditional_reverse)==0)
check("constant_cell_mutual_information_zero",sp.simplify(constant_information)==0 and valid_information(constant_joint)==(0,0) and valid_information(constant_joint.T)==(0,0))
report={"backend":"Python/SymPy","checks":len(results),"passed":all(r['passed'] for r in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
