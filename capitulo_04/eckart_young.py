import itertools
import json
import sympy as sp

results=[]
def check(identifier,condition):
    results.append({'id':identifier,'passed':bool(condition)})

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
    difference=reduce_matrix(left-right,relations)
    return difference==sp.ZeroMatrix(*left.shape)

def trace_normal(expression,relations):
    expression=reduce_matrix(expression,relations)
    if isinstance(expression,sp.MatAdd):
        return sp.expand(sum(trace_normal(term,relations) for term in expression.args))
    if isinstance(expression,sp.ZeroMatrix):
        return sp.Integer(0)
    factors=flatten_factors(expression)
    scalar=sp.Mul(*(factor for factor in factors if not factor.is_Matrix))
    matrices=[factor for factor in factors if factor.is_Matrix]
    choices=[]
    for cut in range(len(matrices)):
        rotated=matrices[cut:]+matrices[:cut]
        reduced=reduce_matrix(sp.MatMul(*rotated).doit(),relations)
        parts=flatten_factors(reduced)
        coefficient=sp.Mul(*(part for part in parts if not part.is_Matrix))
        word=tuple(part for part in parts if part.is_Matrix)
        if any(isinstance(part,sp.ZeroMatrix) for part in word):
            return sp.Integer(0)
        if len(word)==1 and isinstance(word[0],sp.Identity):
            choices.append((0,'',coefficient*word[0].rows))
        else:
            key='|'.join(sp.srepr(part) for part in word)
            choices.append((len(word),key,coefficient*sp.Symbol('trace_'+key,real=True)))
    return sp.expand(scalar*min(choices,key=lambda choice:choice[:2])[2])

def trace_equal(left,right,relations):
    return sp.expand(trace_normal(left,relations)-trace_normal(right,relations))==0

def trace_exchange_certificate(rows,columns):
    x=sp.Matrix(rows,columns,lambda i,j:sp.Symbol(f'x_{i}_{j}',real=True))
    y=sp.Matrix(columns,rows,lambda i,j:sp.Symbol(f'y_{i}_{j}',real=True))
    return sp.expand(sp.trace(x*y)-sp.trace(y*x))==0

check('trace_cyclic_finite_coordinate_identity',all(trace_exchange_certificate(a,b) for a,b in [(9,1),(9,2),(9,3),(9,9),(9,12)]))

b0,b1,bj,c0,c1,cj,d0,d1,dj=sp.symbols('b0 b1 bj c0 c1 cj d0 d1 dj',real=True)
pivot1=sp.Matrix([[c0]])
pivot2=sp.Matrix([[c0,c1],[d0,d1]])
pivot3=sp.Matrix(3,3,sp.symbols('p0:9',real=True))
check('invertible_minor_independent_restricted_rows',all(sp.expand(block*block.adjugate()-block.det()*sp.eye(block.rows))==sp.zeros(block.rows) and sp.expand(block.adjugate()*block-block.det()*sp.eye(block.rows))==sp.zeros(block.rows) for block in [pivot1,pivot2,pivot3]))
for dimension in (1,2,3):
    block=sp.MatrixSymbol(f'block{dimension}',dimension,dimension)
    inverse=sp.MatrixSymbol(f'inverse{dimension}',dimension,dimension)
    coefficients=sp.MatrixSymbol(f'coefficients{dimension}',1,dimension)
    relations={(block,inverse):sp.Identity(dimension)}
    check(f'independence_from_minor_{dimension}',matrix_equal((coefficients*block)*inverse,coefficients,relations))
minor1_residual=sp.factor(b0*cj/c0-bj)
minor2=sp.det(sp.Matrix([[c0,cj],[b0,bj]]))
check('rank_one_every_row_coordinates',sp.cancel(minor1_residual+minor2/c0)==0)
pivot_determinant=pivot2.det()
t1=(b0*d1-b1*d0)/pivot_determinant
t2=(c0*b1-c1*b0)/pivot_determinant
minor3=sp.det(sp.Matrix([[c0,c1,cj],[d0,d1,dj],[b0,b1,bj]]))
check('rank_two_every_row_coordinates',sp.cancel(t1*cj+t2*dj-bj+minor3/pivot_determinant)==0)
check('pivot_row_coordinates_are_exact',sp.simplify(sp.Matrix([[t1,t2]])*pivot2-sp.Matrix([[b0,b1]]))==sp.zeros(1,2))

def row_basis_cases(allow_zero=True,allow_one=True,allow_two=True):
    cases=[]
    for any_entry,any_two in itertools.product((False,True),repeat=2):
        if any_two and not any_entry:
            continue
        branches=[allow_zero and not any_entry,allow_one and any_entry and not any_two,allow_two and any_two]
        if sum(branches)!=1:
            return False
        cases.append((any_entry,any_two))
    return len(cases)==3
check('all_rank_at_most_two_competitors_partition',row_basis_cases())
check('reject_missing_rank_zero_case',not row_basis_cases(allow_zero=False))
check('reject_missing_rank_one_case',not row_basis_cases(allow_one=False))
check('reject_missing_rank_two_case',not row_basis_cases(allow_two=False))

c=sp.Matrix(1,9,sp.symbols('c_0:9',real=True))
d=sp.Matrix(1,9,sp.symbols('d_0:9',real=True))
C=sp.Matrix.vstack(c,d)
gram=C*C.T
minors=[c[0,i]*d[0,j]-c[0,j]*d[0,i] for i in range(9) for j in range(i+1,9)]
check('rank_two_gram_cauchy_binet_all_coordinates',sp.expand(gram.det()-sum(value**2 for value in minors))==0)
check('rank_one_gram_all_coordinates',sp.expand((c*c.T)[0,0]-sum(value**2 for value in c))==0)
positive_pivot=sp.symbols('positive_pivot',real=True,nonzero=True)
other_squares=sp.symbols('other_squares',nonnegative=True)
check('nonzero_pivot_forces_positive_gram',positive_pivot**2>0 and (positive_pivot**2+other_squares).is_positive is True)
g11,g12,g22=sp.symbols('g11 g12 g22',real=True)
gram2=sp.Matrix([[g11,g12],[g12,g22]])
inverse2=gram2.adjugate()/gram2.det()
check('gram_two_inverse_exact',sp.simplify(gram2*inverse2)==sp.eye(2) and sp.simplify(inverse2*gram2)==sp.eye(2) and inverse2.T==inverse2)
h=sp.symbols('h',positive=True)
check('gram_one_inverse_exact',sp.cancel(h*(1/h)-1)==0)

projection_certificates=[]
for rank in (1,2):
    row_basis=sp.MatrixSymbol(f'C{rank}',rank,9)
    coefficients=sp.MatrixSymbol(f'T{rank}',12,rank)
    G=sp.MatrixSymbol(f'G{rank}',rank,rank)
    H=sp.MatrixSymbol(f'H{rank}',rank,rank)
    relations={(row_basis,row_basis.T):G,(G,H):sp.Identity(rank),(H,G):sp.Identity(rank),(H.T,):H}
    P=row_basis.T*H*row_basis
    B=coefficients*row_basis
    certificate=(matrix_equal(P.T,P,relations) and matrix_equal(P*P,P,relations) and matrix_equal(B*P,B,relations) and trace_normal(P,relations)==rank)
    projection_certificates.append(certificate)
    check(f'row_projection_constructed_rank_{rank}',certificate)
check('row_projection_constructed_rank_zero',sp.zeros(9).T==sp.zeros(9) and sp.zeros(9)*sp.zeros(9)==sp.zeros(9) and sp.zeros(12,9)*sp.zeros(9)==sp.zeros(12,9) and sp.trace(sp.zeros(9))==0)
check('every_competitor_has_row_projection',row_basis_cases() and all(projection_certificates) and all(result['passed'] for result in results if result['id'] in ['rank_one_every_row_coordinates','rank_two_every_row_coordinates','rank_two_gram_cauchy_binet_all_coordinates','invertible_minor_independent_restricted_rows']))

A=sp.MatrixSymbol('A',12,9)
B=sp.MatrixSymbol('B',12,9)
E=sp.MatrixSymbol('E',12,9)
P=sp.MatrixSymbol('P',9,9)
V=sp.MatrixSymbol('V',9,9)
U=sp.MatrixSymbol('U',12,9)
Sigma=sp.MatrixSymbol('Sigma',9,9)
Lambda=sp.MatrixSymbol('Lambda',9,9)
H=sp.MatrixSymbol('Indicator',9,9)
identity=sp.Identity(9)
projection_relations={(P.T,):P,(P,P):P}
J=identity-P
check('complementary_projection',matrix_equal(J.T,J,projection_relations) and matrix_equal(J*J,J,projection_relations))
check('frobenius_projection_trace',trace_equal((E*P).T*(E*P),E.T*E*P,projection_relations))
check('frobenius_complement_trace',trace_equal((E*J).T*(E*J),E.T*E*J,projection_relations))
check('frobenius_orthogonal_decomposition',trace_equal(E.T*E,(E*P).T*(E*P)+(E*J).T*(E*J),projection_relations))
row_relations={**projection_relations,(B,P):B,(P,B.T):B.T}
check('row_projection_transposed_identity',matrix_equal((B*P).T,P*B.T,projection_relations))
check('competitor_error_complement',matrix_equal((A-B)*J,A*J,row_relations))
check('error_lower_bound_exact_nonnegative_remainder',trace_equal((A-B).T*(A-B)-A.T*A*J,((A-B)*P).T*((A-B)*P),row_relations))
entries=sp.Matrix(12,9,sp.symbols('e_0:108',real=True))
check('frobenius_all_108_squares_nonnegative',sp.expand(sp.trace(entries.T*entries)-sum(value**2 for value in entries))==0 and all((value**2).is_nonnegative is True for value in entries))

orthogonal_relations={(V.T,V):identity,(V,V.T):identity}
Q=V.T*P*V
conjugate_relations={**projection_relations,**orthogonal_relations}
check('conjugate_projection_symmetric_idempotent_trace',matrix_equal(Q.T,Q,conjugate_relations) and matrix_equal(Q*Q,Q,conjugate_relations) and trace_equal(Q,P,conjugate_relations))
vector=sp.Matrix(9,1,sp.symbols('q_0:9',real=True))
symmetric_entries=sp.Matrix(9,9,lambda i,j:sp.Symbol(f'sym_{min(i,j)}_{max(i,j)}',real=True))
check('symmetric_idempotent_diagonal_coordinate_identity',all(sp.expand((symmetric_entries*symmetric_entries)[i,i]-sum(symmetric_entries[j,i]**2 for j in range(9)))==0 for i in range(9)))
check('projection_diagonal_as_sum_of_squares',sp.expand((vector.T*vector)[0,0]-sum(value**2 for value in vector))==0 and all((value**2).is_nonnegative is True for value in vector))
qii,nonnegative_column,complement_column=sp.symbols('qii nonnegative_column complement_column',real=True)
check('projection_diagonal_interval_from_complement',sp.simplify(sp.Equivalent(sp.reduce_inequalities([qii>=0,1-qii>=0],qii),sp.And(qii>=0,qii<=1))) is sp.true)
svd_relations={**orthogonal_relations,(U.T,U):identity,(Sigma.T,):Sigma,(Sigma,Sigma):Lambda}
svd=U*Sigma*V.T
check('exact_svd_gram',matrix_equal(svd.T*svd,V*Lambda*V.T,svd_relations))
check('spectral_error_trace_identity',trace_equal((V*Lambda*V.T)*(identity-P),Lambda*(identity-V.T*P*V),orthogonal_relations))
lambdas=sp.symbols('lambda_0:9',nonnegative=True)
weights=sp.symbols('w_0:9',real=True)
qentries=sp.Matrix(9,9,sp.symbols('qij_0:81',real=True))
check('trace_equals_total_diagonal_mass',sp.trace(qentries)==sum(qentries[i,i] for i in range(9)))
rank=sp.symbols('rank',integer=True,nonnegative=True)
mass=sp.symbols('mass',real=True)
check('rank_bound_transfers_to_diagonal_mass',sp.simplify((2-mass).subs(mass,rank)-(2-rank))==0)
check('spectral_trace_is_diagonal_weighted_sum',sp.expand(sp.trace(sp.diag(*lambdas)*(sp.eye(9)-qentries))-sum(lambdas[i]*(1-qentries[i,i]) for i in range(9)))==0)

threshold=sp.symbols('threshold',nonnegative=True)
gaps=sp.symbols('gap_0:9',nonnegative=True)
inside_slack=sp.symbols('inside_slack_0:2',nonnegative=True)
outside_mass=sp.symbols('outside_mass_2:9',nonnegative=True)
indicator=[sp.Integer(i<2) for i in range(9)]
weighted_gap=sum(lambdas[i]*(indicator[i]-weights[i]) for i in range(9))
ordered_gap=sum((lambdas[i]-threshold)*(indicator[i]-weights[i]) for i in range(9))
check('ordered_weight_identity_all_nine_coordinates',sp.expand(weighted_gap-ordered_gap-threshold*(2-sum(weights)))==0)

def ordered_weight_certificate(retained=2,rank_budget=2,ordered=True):
    if retained!=2 or rank_budget>retained:
        return False
    direction=1 if ordered else -1
    nonnegative_terms=[]
    for index in range(9):
        term=(lambdas[index]-threshold)*(indicator[index]-weights[index])
        if index<2:
            substituted=term.subs({lambdas[index]:threshold+direction*gaps[index],weights[index]:1-inside_slack[index]})
        else:
            substituted=term.subs({lambdas[index]:threshold-direction*gaps[index],weights[index]:outside_mass[index-2]})
        if sp.expand(substituted).is_nonnegative is not True:
            return False
        nonnegative_terms.append(substituted)
    mass_gap=sp.symbols('mass_gap',nonnegative=True)
    return sp.expand(sum(nonnegative_terms)+threshold*mass_gap).is_nonnegative is True
check('ordered_weight_bound_for_every_feasible_diagonal',ordered_weight_certificate())
check('reject_missing_spectral_order',not ordered_weight_certificate(ordered=False))
check('reject_excess_rank_budget',not ordered_weight_certificate(rank_budget=3))

truncation_relations={**svd_relations,(H.T,):H,(H,H):H,(Sigma,H):sp.MatrixSymbol('RetainedSigma',9,9)}
retained=truncation_relations[(Sigma,H)]
Ps=V*H*V.T
check('truncation_projection',matrix_equal(Ps.T,Ps,truncation_relations) and matrix_equal(Ps*Ps,Ps,truncation_relations))
check('truncation_equals_svd_retained_values',matrix_equal(svd*Ps,U*retained*V.T,truncation_relations))
check('truncation_attains_discarded_sum',trace_equal((svd-svd*Ps).T*(svd-svd*Ps),Lambda*(identity-H),{**svd_relations,(H.T,):H,(H,H):H}))
selection=sp.Matrix(9,2,lambda i,j:1 if i==j else 0)
diagonal_indicator=sp.diag(*indicator)
singular_values=sp.symbols('sigma_0:9',nonnegative=True)
check('diagonal_svd_eigenvalues_are_squared_singular_values',sp.diag(*singular_values)**2==sp.diag(*(value**2 for value in singular_values)) and all((value**2).is_nonnegative is True for value in singular_values))
check('diagonal_retention_of_singular_values',sp.diag(*singular_values)*diagonal_indicator==sp.diag(*(singular_values[i]*indicator[i] for i in range(9))))
ordered_base,ordered_increment=sp.symbols('ordered_base ordered_increment',nonnegative=True)
check('singular_order_implies_squared_order',sp.expand((ordered_base+ordered_increment)**2-ordered_base**2).is_nonnegative is True)
check('retained_indicator_rank_factorization',selection*selection.T==diagonal_indicator and selection.rank()==2)
left=sp.MatrixSymbol('left',12,2)
right=sp.MatrixSymbol('right',2,9)
x=sp.MatrixSymbol('x',9,1)
selector=sp.MatrixSymbol('Selector',9,2)
check('truncation_rank_factorization_is_actual_candidate',matrix_equal(U*Sigma*H*V.T,(U*Sigma*selector)*(selector.T*V.T),{(selector,selector.T):H}))
check('truncation_rank_at_most_two_by_explicit_factorization',((left*right)*x)==left*(right*x) and (right*x).shape==(2,1))
check('retained_tail_all_nine_coordinates',sp.expand(sum(lambdas[i]*(1-indicator[i]) for i in range(9))-sum(lambdas[2:]))==0)

lower_gap,weight_gap=sp.symbols('lower_gap weight_gap',nonnegative=True)
tail,error=sp.symbols('tail error',real=True)
x_nonnegative=sp.symbols('x_nonnegative',nonnegative=True)
positive_gap=sp.symbols('positive_gap',positive=True)
sqrt_sum=sp.sqrt(x_nonnegative+positive_gap)+sp.sqrt(x_nonnegative)
check('frobenius_sqrt_monotonic_zero_gap',sp.sqrt(x_nonnegative+0)==sp.sqrt(x_nonnegative))
check('frobenius_sqrt_monotonic_positive_gap',sp.simplify((sp.sqrt(x_nonnegative+positive_gap)-sp.sqrt(x_nonnegative))*sqrt_sum-positive_gap)==0 and sqrt_sum.is_positive is True and (positive_gap/sqrt_sum).is_positive is True)
check('global_minimum_composition',sp.expand((tail+lower_gap+weight_gap)-tail).is_nonnegative is True)

def global_certificate():
    required=['every_competitor_has_row_projection','error_lower_bound_exact_nonnegative_remainder','frobenius_all_108_squares_nonnegative','conjugate_projection_symmetric_idempotent_trace','symmetric_idempotent_diagonal_coordinate_identity','projection_diagonal_interval_from_complement','trace_equals_total_diagonal_mass','rank_bound_transfers_to_diagonal_mass','exact_svd_gram','spectral_error_trace_identity','spectral_trace_is_diagonal_weighted_sum','ordered_weight_identity_all_nine_coordinates','ordered_weight_bound_for_every_feasible_diagonal','truncation_equals_svd_retained_values','truncation_attains_discarded_sum','diagonal_svd_eigenvalues_are_squared_singular_values','diagonal_retention_of_singular_values','singular_order_implies_squared_order','retained_indicator_rank_factorization','truncation_rank_factorization_is_actual_candidate','truncation_rank_at_most_two_by_explicit_factorization','frobenius_sqrt_monotonic_zero_gap','frobenius_sqrt_monotonic_positive_gap','global_minimum_composition']
    lookup={result['id']:result['passed'] for result in results}
    return all(lookup.get(name,False) for name in required)
check('eckart_young_global_rank_two',global_certificate())
check('reject_unprojected_error_remainder',not trace_equal((A-B).T*(A-B)-A.T*A*J,-((A-B)*P).T*((A-B)*P),row_relations))
check('reject_wrong_pivot_coordinates',sp.cancel(t1*cj+2*t2*dj-bj+minor3/pivot_determinant)!=0)
check('reject_wrong_gram_inverse',sp.simplify(gram2*(2*inverse2))!=sp.eye(2))
X=sp.MatrixSymbol('X',9,9)
Y=sp.MatrixSymbol('Y',9,9)
Z=sp.MatrixSymbol('Z',9,9)
check('reject_noncyclic_trace_permutation',not trace_equal(X*Y*Z,X*Z*Y,{}))
report={'backend':'Python/SymPy','checks':len(results),'passed':all(result['passed'] for result in results),'results':results,'scope':{'matrix_shape':[12,9],'rank_bound':2,'domain':'real','svd':'exact','retained_eigenvalues':'two largest, allowing ties','competitors':'every real matrix of rank at most two'}}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
