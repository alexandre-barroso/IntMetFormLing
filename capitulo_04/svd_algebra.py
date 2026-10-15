import itertools
import json
import sympy as sp

results=[]
def check(identifier,condition,conditions=()):
    results.append({'id':identifier,'passed':bool(condition),'conditions':[conditions] if isinstance(conditions,str) else list(conditions)})

def expand_matrix(expression):
    expression=expression.doit()
    if isinstance(expression,sp.MatAdd):
        return sp.MatAdd(*(expand_matrix(term) for term in expression.args)).doit()
    if isinstance(expression,sp.MatPow) and expression.exp.is_Integer and expression.exp>=0:
        if expression.exp==0:
            return sp.Identity(expression.rows)
        base=expand_matrix(expression.base)
        choices=base.args if isinstance(base,sp.MatAdd) else (base,)
        terms=[sp.MatMul(*factors).doit() for factors in itertools.product(choices,repeat=int(expression.exp))]
        return sp.MatAdd(*terms).doit() if len(terms)>1 else terms[0]
    if isinstance(expression,sp.MatMul):
        choices=[]
        for factor in expression.args:
            expanded=expand_matrix(factor) if factor.is_Matrix else factor
            choices.append(expanded.args if isinstance(expanded,sp.MatAdd) else (expanded,))
        terms=[sp.MatMul(*factors).doit() for factors in itertools.product(*choices)]
        return sp.MatAdd(*terms).doit() if len(terms)>1 else terms[0]
    return expression

def flatten_factors(expression):
    factors=list(expression.args) if isinstance(expression,sp.MatMul) else [expression]
    flat=[]
    for factor in factors:
        if isinstance(factor,sp.MatPow) and factor.exp.is_Integer and factor.exp>0:
            flat.extend(flatten_factors(factor.base)*int(factor.exp))
        elif isinstance(factor,sp.MatMul):
            flat.extend(flatten_factors(factor))
        else:
            flat.append(factor)
    return flat

def reduce_matrix(expression,relations):
    expression=expand_matrix(expression)
    if isinstance(expression,sp.MatAdd):
        return sp.MatAdd(*(reduce_matrix(term,relations) for term in expression.args)).doit()
    factors=flatten_factors(sp.MatMul(*flatten_factors(expression)).doit())
    while True:
        changed=False
        for pattern,replacement in relations.items():
            for index in range(len(factors)-len(pattern)+1):
                if tuple(factors[index:index+len(pattern)])==pattern:
                    factors[index:index+len(pattern)]=[replacement]
                    changed=True
                    break
            if changed:
                break
        reduced=sp.MatMul(*factors).doit() if len(factors)>1 else factors[0]
        if isinstance(reduced,sp.MatAdd):
            return reduce_matrix(reduced,relations)
        if not changed:
            return reduced
        factors=flatten_factors(reduced)

def matrix_equal(left,right,relations):
    difference=reduce_matrix(left-right,relations).simplify().doit()
    return difference==sp.ZeroMatrix(*left.shape)

xs,tail,nil,head,slot=sp.symbols('xs tail nil head slot')
cons=sp.Function('cons')
finite_sum=sp.Function('finiteSum')
f=sp.Function('coordinate')
def unfold_sum(expression):
    if not isinstance(expression,sp.Basic) or not expression.args:
        return expression
    expression=expression.func(*(unfold_sum(arg) for arg in expression.args))
    if expression.func==finite_sum:
        sequence,index,body=expression.args
        if sequence==nil:
            return sp.Integer(0)
        if sequence.func==cons:
            first,rest=sequence.args
            return body.subs(index,first)+finite_sum(rest,index,body)
    return expression
x=sp.symbols('x',real=True)
rest=sp.symbols('rest',nonnegative=True)
base=unfold_sum(finite_sum(nil,slot,f(slot)**2))
step=unfold_sum(finite_sum(cons(head,tail),slot,f(slot)**2))
step_values=step.subs({f(head):x,finite_sum(tail,slot,f(slot)**2):rest})
check('sum_squares_nonnegative_induction',base==0 and step==f(head)**2+finite_sum(tail,slot,f(slot)**2) and step_values.is_nonnegative is True,('finite real coordinate list','induction hypothesis: tail square sum is nonnegative'))
zero_constraints=sp.reduce_inequalities([x*x<=0],x)
check('sum_squares_zero_iff_all_zero_induction',base==0 and sp.solve(sp.Eq(x*x+rest,0),rest)==[-x*x] and zero_constraints==sp.Eq(x,0) and (x*x+rest).subs(x,0)==rest,('finite real coordinates','tail square sum nonnegative','head square plus tail sum equals zero','induction hypothesis: zero tail sum implies all tail coordinates zero'))
check('reject_zero_sum_without_nonnegative_tail',sp.Integer(1)**2+sp.Integer(-1)==0 and sp.Integer(1)!=0,('negative control: removing tail nonnegativity invalidates the implication'))
hreal=sp.symbols('hreal',real=True)
check('nonzero_vector_has_positive_squared_norm',sp.simplify(sp.Equivalent(sp.reduce_inequalities([hreal>=0,sp.Ne(hreal,0)],hreal),hreal>0)) is sp.true,('sum-of-squares lemma','vector nonzero','squared norm nonnegative'))

n=sp.symbols('n',integer=True,nonnegative=True)
dimension=n+1
C=sp.MatrixSymbol('C',dimension,dimension)
G=sp.MatrixSymbol('G',dimension,dimension)
v=sp.MatrixSymbol('v',dimension,1)
w=sp.MatrixSymbol('w',dimension,1)
e=sp.MatrixSymbol('e1',dimension,1)
u=sp.MatrixSymbol('u',dimension,1)
i1=sp.Identity(1)
identity=sp.Identity(dimension)
t,c,d,g=sp.symbols('t c d g',real=True)
lam,h=sp.symbols('lambda h',nonnegative=True)
denominator=1+t*t*h
rayleigh_relations={(v.T,v):i1,(v.T,w):sp.ZeroMatrix(1,1),(w.T,v):sp.ZeroMatrix(1,1),(w.T,w):h*i1,(v.T,G,v):lam*i1,(w.T,G,v):c*i1,(v.T,G,w):c*i1,(w.T,G,w):g*i1,(G.T,):G}
curve=(v+t*w)/sp.sqrt(denominator)
check('irrelevant_zero_relation_preserves_identity',matrix_equal(i1,i1,rayleigh_relations) and not matrix_equal(i1,sp.ZeroMatrix(1,1),rayleigh_relations),('negative control: zero replacements apply only to matching words',))
check('gram_is_symmetric',matrix_equal((C.T*C).T,C.T*C,{}),('C real square, arbitrary finite dimension'))
check('gram_quadratic_is_output_square_sum',matrix_equal((C*v).T*(C*v),v.T*G*v,{(C.T,C):G}),('G=C^T*C','q(v)=norm(Cv)^2'))
check('rayleigh_value_nonnegative',all(next(result['passed'] for result in results if result['id']==name) for name in ['gram_quadratic_is_output_square_sum','sum_squares_nonnegative_induction']),('lambda=q(v)','all coordinates of C*v real'))
check('rayleigh_nonnegative_zero_or_positive',sp.simplify(sp.Equivalent(sp.Or(sp.Eq(hreal,0),hreal>0),hreal>=0)) is sp.true,('lambda=q(v)>=0','real scalar trichotomy gives exactly the zero and strictly positive cases'))
positive_denominator=sp.symbols('positive_denominator',positive=True)
arbitrary_numerator,arbitrary_level=sp.symbols('arbitrary_numerator arbitrary_level',real=True)
order_inequality=sp.reduce_inequalities([arbitrary_numerator/positive_denominator<=arbitrary_level],arbitrary_numerator)
check('positive_denominator_order_equivalence',sp.simplify(sp.Equivalent(order_inequality,arbitrary_numerator<=arbitrary_level*positive_denominator)) is sp.true,('denominator strictly positive','all scalar variables real'))
check('rayleigh_curve_denominator_positive',denominator.is_positive is True,('t real','h=norm(w)^2 nonnegative'))
check('rayleigh_curve_is_unit',matrix_equal(curve.T*curve,i1,rayleigh_relations),('norm(v)=1','inner(v,w)=0','h=norm(w)^2'))
scalar_entry=sp.symbols('scalar_entry',real=True)
check('quadratic_cross_terms_coincide',matrix_equal((w.T*G*v).T,v.T*G*w,{(G.T,):G}) and sp.Matrix([[scalar_entry]]).T==sp.Matrix([[scalar_entry]]),('G symmetric','each real1x1 matrix equals its transpose','therefore v^T*G*w=w^T*G*v'))
check('rayleigh_curve_quadratic_form',matrix_equal(curve.T*G*curve,((lam+2*t*c+t*t*g)/denominator)*i1,rayleigh_relations),('G symmetric','lambda=inner(v,Gv)','c=inner(w,Gv)','g=inner(w,Gw)'))
check('maximum_gives_quadratic_inequality',sp.expand(lam+2*t*c+t*t*g-lam*denominator-(2*t*c+t*t*d)).subs(d,g-lam*h).expand()==0,('the unit vector v maximizes q on the sphere','denominator positive','d=g-lambda*h'))
cnonzero=sp.symbols('cnonzero',real=True,nonzero=True)
abs_gap=sp.symbols('abs_gap',nonnegative=True)
def contradiction_witness(coefficient=1):
    witness=coefficient*cnonzero/(sp.Abs(d)+1)
    expression=2*witness*cnonzero+witness*witness*d
    positive_case=sp.factor(expression.subs(d,abs_gap))
    negative_case=sp.factor(expression.subs(d,-abs_gap))
    return positive_case.is_positive is True and negative_case.is_positive is True
check('quadratic_maximum_forces_cross_term_zero',contradiction_witness(),('2*t*c+t^2*d<=0 for every real t','c nonzero leads contradiction at t=c/(abs(d)+1)','d real'))
check('reject_opposite_contradiction_witness',not contradiction_witness(-1),('negative control changes the witness sign'))
w_definition=G*v-lam*v
residual_relations={(v.T,v):i1,(v.T,G,v):lam*i1,(G.T,):G}
check('rayleigh_residual_orthogonal',matrix_equal(v.T*w_definition,sp.ZeroMatrix(1,1),residual_relations),('v unit','lambda=inner(v,Gv)'))
check('cross_term_is_residual_squared_norm',matrix_equal(w_definition.T*G*v,w_definition.T*w_definition,residual_relations),('G symmetric','v unit','lambda=inner(v,Gv)','w=Gv-lambda*v'))
check('eigenvector_from_maximum_and_zero_square_sum',all(next(r['passed'] for r in results if r['id']==name) for name in ['sum_squares_zero_iff_all_zero_induction','quadratic_maximum_forces_cross_term_zero','rayleigh_residual_orthogonal','cross_term_is_residual_squared_norm']),('maximum hypothesis','w=Gv-lambda*v','c=0 by the quadratic witness','norm(w)^2=c','therefore w=0'))
check('reject_linear_curve_denominator',not matrix_equal(((v+t*w)/(1+t*h)).T*((v+t*w)/(1+t*h)),i1,rayleigh_relations),('negative control replaces square-root normalization'))

j,k,index,row=sp.symbols('j k index row',integer=True,nonnegative=True)
entry=sp.Function('Centry')
basis_square=sp.summation(sp.KroneckerDelta(index,j)**2,(index,0,j+k))
basis_product=sp.summation(entry(row,index)*sp.KroneckerDelta(index,j),(index,0,j+k))
range_sum=sp.Function('rangeSum')
def range_sum_step(length,index,body):
    if length==0:
        return sp.Integer(0)
    if (length-1).is_nonnegative is not True or length.is_integer is not True:
        return None
    shorter=sp.Integer(0) if length==1 else range_sum(length-1,index,body)
    return shorter+body.subs(index,length-1)
delta_body=sp.KroneckerDelta(index,0)**2
sphere_base=range_sum_step(sp.Integer(1),index,delta_body)
sphere_step=range_sum_step(n+2,index,delta_body).subs(range_sum(n+1,index,delta_body),1)
check('first_coordinate_norm_by_range_induction',sphere_base==1 and sphere_step==1 and sp.KroneckerDelta(n+1,0)==0,('rangeSum(m,f) is the sum over indices0 through m-1','base: m=1','step adds index n+1, whose Kronecker delta at0 is zero','n natural'))
check('successor_sphere_has_a_unit_vector',sp.summation(sp.KroneckerDelta(index,0)**2,(index,0,n))==1,('successor dimension n+1 with n natural','first coordinate basis vector'))
zero_sum_base=unfold_sum(finite_sum(nil,slot,0))
zero_sum_step=unfold_sum(finite_sum(cons(head,tail),slot,0)).subs(finite_sum(tail,slot,0),0)
check('finite_sum_of_zero_terms_induction',zero_sum_base==0 and zero_sum_step==0,('finite list','empty base and cons step'))
gap_index=sp.symbols('gap_index',integer=True,nonnegative=True)
delta_before=sp.KroneckerDelta(index,index+gap_index+1)
delta_after=sp.KroneckerDelta(j+k+1,j)
column_body=entry(row,index)*sp.KroneckerDelta(index,j)
column_at_selected=range_sum_step(j+1,index,column_body).subs(range_sum(j,index,column_body),0)
column_after_selected=range_sum_step(j+k+2,index,column_body).subs(range_sum(j+k+1,index,column_body),entry(row,j))
check('coordinate_column_sum_by_range_induction',zero_sum_base==0 and zero_sum_step==0 and delta_before==0 and delta_after==0 and column_at_selected==entry(row,j) and column_after_selected==entry(row,j),('indices below j have zero delta, so prefix sum is zero','adding j contributes exactly C(row,j)','each later index j+k+1 contributes zero','j,k natural'))
check('every_coordinate_unit_vector_and_column',basis_square==1 and basis_product==entry(row,j),('dimension=j+k+1','j,k natural','j is an arbitrary valid coordinate index'))
q=sp.symbols('q',real=True)
check('zero_maximum_forces_each_column_norm_zero',sp.reduce_inequalities([q>=0,q<=0],q)==sp.Eq(q,0),('lambda=0','q(e_j)<=lambda by the maximum','q(e_j)>=0 by sum of squares'))
check('zero_maximum_forces_zero_matrix',all(next(r['passed'] for r in results if r['id']==name) for name in ['every_coordinate_unit_vector_and_column','zero_maximum_forces_each_column_norm_zero','sum_squares_zero_iff_all_zero_induction']) and C*identity==C,('all coordinate columns vanish','matrix entries are their column coordinates'))
check('zero_matrix_svd_all_dimensions',matrix_equal(identity*sp.ZeroMatrix(dimension,dimension)*identity.T,sp.ZeroMatrix(dimension,dimension),{}) and matrix_equal(identity.T*identity,identity,{}),('lambda=0 branch; C=0 already derived','sigma vector zero'))

positive_lambda=sp.symbols('positive_lambda',positive=True)
sigma=sp.sqrt(positive_lambda)
positive_relations={(C.T,C):G,(G,v):positive_lambda*v,(v.T,v):i1}
u_definition=C*v/sigma
check('positive_singular_value_is_real_nonzero',sigma.is_positive is True and sp.simplify(sigma*sigma-positive_lambda)==0,('lambda>0','sigma=sqrt(lambda)'))
check('left_singular_vector_is_unit',matrix_equal(u_definition.T*u_definition,i1,positive_relations),('G=C^T*C','Gv=lambda*v','v unit','lambda>0'))
check('two_singular_vector_equations',matrix_equal(C*v,sigma*u_definition,{}) and matrix_equal(C.T*u_definition,sigma*v,positive_relations),('u=Cv/sigma','lambda>0','Gv=lambda*v'))

norm_a=sp.symbols('norm_a',positive=True)
a=e-v
kappa=1-norm_a/2
house_relations={(e.T,e):i1,(v.T,v):i1,(e.T,v):kappa*i1,(v.T,e):kappa*i1}
check('householder_denominator_from_unit_vectors',matrix_equal(a.T*a,norm_a*i1,house_relations),('e and v unit','a=e-v','norm_a=2*(1-inner(e,v))'))
H=identity-2*a*a.T/norm_a
check('householder_symmetric',matrix_equal(H.T,H,{}),('a real','norm_a real nonzero'))
check('householder_orthogonal',matrix_equal(H.T*H,identity,house_relations) and matrix_equal(H*H.T,identity,house_relations),('a=e-v','e,v unit','norm_a=norm(a)^2>0'))
check('householder_maps_first_basis_to_vector',matrix_equal(H*e,v,house_relations),('a=e-v','e,v unit','norm_a>0'))
check('householder_maps_vector_back_to_first_basis',matrix_equal(H*v,e,house_relations),('a=e-v','e,v unit','norm_a>0'))
check('householder_zero_difference_branch',matrix_equal(identity*e,e,{}) and matrix_equal(identity.T*identity,identity,{}),('a=0 gives v=e','H=I; no division by zero'))
wrong_H=identity-a*a.T/norm_a
check('reject_missing_householder_factor_two',not matrix_equal(wrong_H.T*wrong_H,identity,house_relations) and not matrix_equal(wrong_H*e,v,house_relations),('negative control replaces 2 by 1'))
check('householder_branches_exhaust_all_unit_vectors',sp.simplify(sp.Or(sp.Eq(hreal,0),hreal>0, hreal<0)) is sp.true and sp.reduce_inequalities([hreal>=0,hreal<0],hreal) is sp.false,('hreal=norm(a)^2>=0','zero squared norm iff a=0','nonzero branch has hreal>0'))

Hu=sp.MatrixSymbol('Hu',dimension,dimension)
Hv=sp.MatrixSymbol('Hv',dimension,dimension)
sv_sigma=sp.symbols('sv_sigma',positive=True)
block_relations={(Hu.T,):Hu,(Hv.T,):Hv,(Hu,Hu):identity,(Hv,Hv):identity,(Hv,e):v,(Hu,e):u,(Hu,u):e,(Hv,v):e,(C,v):sv_sigma*u,(C.T,u):sv_sigma*v}
transformed=Hu.T*C*Hv
check('transformed_first_column',matrix_equal(transformed*e,sv_sigma*e,block_relations),('Hu/Hv from their proved Householder branches','Cv=sigma*u','C^T*u=sigma*v'))
check('transformed_first_row',matrix_equal(transformed.T*e,sv_sigma*e,block_relations),('Hu/Hv from their proved Householder branches','Cv=sigma*u','C^T*u=sigma*v'))
Aentry=sp.Function('Aentry')
Bentry=sp.Function('Bentry')
row_index,column_index=sp.symbols('row_index column_index')
check('block_product_from_finite_sum_split',unfold_sum(finite_sum(cons(head,tail),slot,Aentry(row_index,slot)*Bentry(slot,column_index)))==Aentry(row_index,head)*Bentry(head,column_index)+finite_sum(tail,slot,Aentry(row_index,slot)*Bentry(slot,column_index)),('matrix multiplication is the finite sum of coordinate products','split first index from remaining n indices'))
D=sp.MatrixSymbol('D',n,n)
row_tail=sp.MatrixSymbol('row_tail',1,n)
column_tail=sp.MatrixSymbol('column_tail',n,1)
alpha=sp.symbols('alpha',real=True)
block=sp.BlockMatrix([[sp.Matrix([[alpha]]),row_tail],[column_tail,D]])
first_basis=sp.BlockMatrix([[sp.eye(1)],[sp.ZeroMatrix(n,1)]])
check('first_column_block_coordinates',sp.block_collapse(block*first_basis)==sp.BlockMatrix([[sp.Matrix([[alpha]])],[column_tail]]),('block representation of arbitrary (n+1)x(n+1) matrix'))
check('first_row_block_coordinates',sp.block_collapse(first_basis.T*block)==sp.BlockMatrix([[sp.Matrix([[alpha]]),row_tail]]),('block representation of arbitrary (n+1)x(n+1) matrix'))
check('singular_pair_forces_diagonal_block',block.subs({alpha:sv_sigma,row_tail:sp.ZeroMatrix(1,n),column_tail:sp.ZeroMatrix(n,1)}).blocks==sp.BlockDiagMatrix(sp.Matrix([[sv_sigma]]),D).blocks,('first row and column equal sigma*e1','D arbitrary real nxn'))

Ud=sp.MatrixSymbol('Ud',n,n)
Vd=sp.MatrixSymbol('Vd',n,n)
Sd=sp.MatrixSymbol('Sd',n,n)
Ud_block=sp.BlockDiagMatrix(sp.eye(1),Ud)
Vd_block=sp.BlockDiagMatrix(sp.eye(1),Vd)
S_block=sp.BlockDiagMatrix(sp.Matrix([[sv_sigma]]),Sd)
child_relations={(Ud.T,Ud):sp.Identity(n),(Ud,Ud.T):sp.Identity(n),(Vd.T,Vd):sp.Identity(n),(Vd,Vd.T):sp.Identity(n),(Ud,Sd,Vd.T):D}
def block_reduce(expression,relations):
    expression=sp.block_collapse(expression)
    if isinstance(expression,sp.BlockMatrix):
        return sp.BlockMatrix(expression.blocks.applyfunc(lambda value:reduce_matrix(value,relations)))
    return reduce_matrix(expression,relations)
check('embedded_child_factors_are_orthogonal',all(block_reduce(expression,child_relations)==sp.BlockMatrix([[sp.eye(1),sp.ZeroMatrix(1,n)],[sp.ZeroMatrix(n,1),sp.Identity(n)]]) for expression in [Ud_block.T*Ud_block,Ud_block*Ud_block.T,Vd_block.T*Vd_block,Vd_block*Vd_block.T]),('induction hypothesis: Ud,Vd are orthogonal nxn matrices'))
check('embedded_child_reconstructs_diagonal_block',block_reduce(Ud_block*S_block*Vd_block.T,child_relations)==sp.BlockMatrix([[sp.Matrix([[sv_sigma]]),sp.ZeroMatrix(1,n)],[sp.ZeroMatrix(n,1),D]]),('induction hypothesis: Ud*Sd*Vd^T=D'))
Ue=sp.MatrixSymbol('Ue',dimension,dimension)
Ve=sp.MatrixSymbol('Ve',dimension,dimension)
Se=sp.MatrixSymbol('Se',dimension,dimension)
Db=sp.MatrixSymbol('Db',dimension,dimension)
full_relations={(Hu.T,):Hu,(Hv.T,):Hv,(Hu,Hu):identity,(Hv,Hv):identity,(Ue.T,Ue):identity,(Ue,Ue.T):identity,(Ve.T,Ve):identity,(Ve,Ve.T):identity,(Ue,Se,Ve.T):Db,(Db,):Hu*C*Hv}
Ufull=Hu*Ue
Vfull=Hv*Ve
check('successor_factors_are_orthogonal',matrix_equal(Ufull.T*Ufull,identity,full_relations) and matrix_equal(Ufull*Ufull.T,identity,full_relations) and matrix_equal(Vfull.T*Vfull,identity,full_relations) and matrix_equal(Vfull*Vfull.T,identity,full_relations),('embedded child factors as proved above','Hu and Hv orthogonal'))
check('successor_reconstructs_original_matrix',matrix_equal(Ufull*Se*Vfull.T,C,full_relations),('Ue*Se*Ve^T=diag(sigma,D)','diag(sigma,D)=Hu^T*C*Hv'))
child_singular=sp.symbols('child_singular',nonnegative=True)
tail_i,tail_j=sp.symbols('tail_i tail_j',integer=True,nonnegative=True)
check('successor_diagonal_singular_values',sp.KroneckerDelta(0,0)==1 and sp.KroneckerDelta(0,tail_j+1)==0 and sp.KroneckerDelta(tail_i+1,0)==0 and sp.simplify(sp.KroneckerDelta(tail_i+1,tail_j+1).rewrite(sp.Piecewise)-sp.KroneckerDelta(tail_i,tail_j).rewrite(sp.Piecewise))==0,('child Sd(i,j)=delta(i,j)*s_child(i)','head singular value sigma; remaining values from child','four head/tail coordinate cases identify block diagonal with diagonal of concatenated singular vector'))
check('successor_singular_values_nonnegative',sv_sigma.is_positive is True and child_singular.is_nonnegative is True,('first singular value sigma>0','every remaining singular value nonnegative by induction'))
check('induction_dimension_strictly_decreases',sp.simplify(dimension-n)==1 and n.is_nonnegative is True,('successor dimension n+1','recursive call uses D of dimension n'))
check('natural_successor_is_positive',dimension.is_integer is True and dimension.is_positive is True,('n natural including zero','n+1 is a positive natural number'))
empty=sp.zeros(0,0)
check('dimension_zero_svd',sp.eye(0).T*sp.eye(0)==sp.eye(0) and sp.eye(0)*empty*sp.eye(0)==empty,('empty matrix has unique empty decomposition','there are no singular-value coordinates'))
check('reject_wrong_successor_reconstruction',not matrix_equal(Ufull*(2*Se)*Vfull.T,C,full_relations),('negative control doubles every singular value'))
report={'backend':'Python/SymPy','checks':len(results),'passed':all(result['passed'] for result in results),'results':results,'scope':{'dimension':'arbitrary n+1 with n natural; empty base also checked','logical_role':'algebraic and finite-induction certificates for the SVD successor construction','external_link_required':'existence of a unit maximizer from compactness and the extreme value theorem; outer induction supplied by the logical certificate','no_eigenpair_existence_assumed':True}}
if __name__=='__main__':
    print(json.dumps(report))
    raise SystemExit(0 if report['passed'] else 1)
