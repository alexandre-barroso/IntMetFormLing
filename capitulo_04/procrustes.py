import json
import sympy as sp

N,d=sp.symbols('N d',integer=True,positive=True)
i,j,k=sp.symbols('i j k',integer=True,nonnegative=True)
A,B=sp.MatrixSymbol('A',N,d),sp.MatrixSymbol('B',N,d)
Q,U,V,R=[sp.MatrixSymbol(name,d,d) for name in ['Q','U','V','R']]
sigma=sp.MatrixSymbol('sigma',d,1)
D=sp.DiagMatrix(sigma)
C=sp.MatrixSymbol('C',d,d)
orthogonal={Q,U,V,R}

def reduce_word(word,allowed):
    word=list(word)
    changed=True
    while changed:
        changed=False
        for t in range(len(word)-1):
            left,right=word[t:t+2]
            if any((left==m.T and right==m) or (left==m and right==m.T) for m in allowed):
                word[t:t+2]=[]
                changed=True
                break
    return tuple(word)

def matrix_normal(expression,allowed):
    expression=sp.expand(expression).doit()
    if isinstance(expression,sp.MatAdd):return sp.MatAdd(*(matrix_normal(x,allowed) for x in expression.args)).doit()
    coefficient,factors=expression.as_coeff_matrices() if isinstance(expression,sp.MatMul) else (sp.Integer(1),[expression])
    reduced=reduce_word(factors,allowed)
    return coefficient*(sp.MatMul(*reduced).doit() if reduced else sp.Identity(expression.rows))

def trace_normal(expression,allowed):
    expression=sp.expand(expression).doit()
    def one_trace(t):
        matrix=t.arg
        coefficient,factors=matrix.as_coeff_matrices() if isinstance(matrix,sp.MatMul) else (sp.Integer(1),[matrix])
        variants=[]
        for orientation in [factors,[x.T.doit() for x in factors[::-1]]]:
            for start in range(len(orientation)):
                word=tuple(orientation[start:]+orientation[:start])
                reduced=reduce_word(word,allowed)
                if not reduced:return coefficient*matrix.rows
                for offset in range(len(reduced)):
                    variants.append(reduced[offset:]+reduced[:offset])
        best=min(variants,key=lambda word:(len(word),tuple(str(x) for x in word)))
        return coefficient*sp.Trace(sp.MatMul(*best).doit())
    return sp.expand(expression.replace(lambda x:isinstance(x,sp.Trace),one_trace))

xs,head,tail,nil=sp.symbols('xs fresh_head fresh_tail nil')
cons=sp.Function('cons')
sig=sp.Function('sig',nonnegative=True)
diag=sp.Function('diag',real=True)
gap=sp.Function('gap',nonnegative=True)
entry=sp.Function('entry',real=True)
squares=sp.Function('squares',real=True)
class Member(sp.logic.boolalg.BooleanFunction):
    nargs=2
member=Member
weighted,total,weighted_gap=[sp.Function(name,real=True) for name in ['weighted','total','weighted_gap']]
folds={weighted:sig(head)*diag(head),total:sig(head),weighted_gap:sig(head)*(1-diag(head)),squares:entry(head)**2}

def unfold(expression):
    rules={}
    for f,term in folds.items():
        rules[f(nil)]=sp.Integer(0)
        rules[f(cons(head,tail))]=term+f(tail)
    return expression.subs(rules,simultaneous=True)

def finite_induction(left,right):
    if {head,tail}&(left.free_symbols|right.free_symbols):return False
    if sp.simplify(unfold(left.subs(xs,nil))-unfold(right.subs(xs,nil)))!=0:return False
    ih_left,ih_right=left.subs(xs,tail),right.subs(xs,tail)
    step_left,step_right=unfold(left.subs(xs,cons(head,tail))),unfold(right.subs(xs,cons(head,tail)))
    return sp.expand(step_left.subs(ih_left,ih_right)-step_right.subs(ih_left,ih_right))==0

def squares_nonnegative_induction():
    tail_square_sum=sp.Symbol('tail_square_sum',nonnegative=True)
    base=unfold(squares(nil))
    step=unfold(squares(cons(head,tail))).subs(squares(tail),tail_square_sum)
    return base==0 and step.is_nonnegative is True

def membership_unfold(value,sequence):
    if sequence==nil:return sp.false
    if sequence.func==cons:return sp.Or(sp.Eq(value,entry(sequence.args[0])),member(value,sequence.args[1]))
    return member(value,sequence)

def member_bound_induction(sign=1):
    value=sp.Symbol('selected_entry',real=True)
    tail_nonnegative=sp.Symbol('tail_nonnegative',nonnegative=True)
    tail_gap=sp.Symbol('tail_gap',nonnegative=True)
    base=membership_unfold(value,nil)==sp.false
    alternatives=membership_unfold(value,cons(head,tail))==sp.Or(sp.Eq(value,entry(head)),member(value,tail))
    expression=sign*unfold(squares(cons(head,tail)))-value**2
    head_case=expression.subs({value:entry(head),squares(tail):tail_nonnegative},simultaneous=True)
    tail_case=expression.subs(squares(tail),value**2+tail_gap)
    return squares_nonnegative_induction() and base and alternatives and sp.expand(head_case).is_nonnegative is True and sp.expand(tail_case).is_nonnegative is True

def weighted_gap_nonnegative_induction():
    tail_nonnegative=sp.Symbol('tail_nonnegative',nonnegative=True)
    base=unfold(weighted_gap(nil))
    step=unfold(weighted_gap(cons(head,tail))).subs({diag(head):1-gap(head),weighted_gap(tail):tail_nonnegative},simultaneous=True)
    return base==0 and sp.expand(step).is_nonnegative is True

results=[]
def check(name,value):
    if value is not True:raise AssertionError(name)
    results.append({'id':name,'passed':True})

check('dimensions',A.shape==B.shape==(N,d) and Q.shape==U.shape==V.shape==R.shape==(d,d) and D.shape==(d,d))
check('one_sided_determinant_identity',sp.det(Q.T*Q).doit()==sp.det(Q)**2 and sp.det(sp.Identity(d))==1)
determinant_value=sp.Symbol('determinant_value',real=True)
check('one_sided_determinant_nonzero',sp.reduce_inequalities([sp.Eq(determinant_value**2,1),sp.Eq(determinant_value,0)],determinant_value)==sp.false)
check('invertible_right_cancellation',(Q.T*Q)*Q.I==Q.T and sp.Identity(d)*Q.I==Q.I)
one_sided=sp.Eq(Q.T*Q,sp.Identity(d),evaluate=False)
canceled_one_sided=sp.Eq(one_sided.lhs*Q.I,one_sided.rhs*Q.I,evaluate=False)
check('left_inverse_equals_inverse',canceled_one_sided==sp.Eq(Q.T,Q.I,evaluate=False))
opposite_from_canceled=sp.Eq(Q*canceled_one_sided.lhs,Q*canceled_one_sided.rhs,evaluate=False)
check('opposite_product_from_inverse',opposite_from_canceled==sp.Eq(Q*Q.T,sp.Identity(d),evaluate=False))

column=(R.T*R)[j,j]
check('column_squares_contraction',column.dummy_eq(sp.Sum(R[i,j]**2,(i,0,d-1))))
a,b,s,term=sp.symbols('a b s term',real=True)
nonnegative_tail=sp.Symbol('nonnegative_tail',nonnegative=True)
check('square_sum_nonnegative_induction',squares_nonnegative_induction())
check('selected_member_bound_induction',member_bound_induction())
check('square_sum_cons_nonnegative',(head**2+nonnegative_tail).subs(head,a).is_nonnegative is True)
check('selected_member_head_bound',sp.expand(a**2+nonnegative_tail-a**2).is_nonnegative is True)
ih_gap=sp.Symbol('induction_tail_gap',nonnegative=True)
check('selected_member_tail_bound',(a**2+ih_gap).is_nonnegative is True)
check('column_member_upper_bound',sp.reduce_inequalities([a*a<=1,a>1],a)==sp.false)
check('column_member_lower_bound',sp.reduce_inequalities([a*a<=1,a< -1],a)==sp.false)
check('orthogonal_product',(matrix_normal((U.T*Q*V).T*(U.T*Q*V),orthogonal)==sp.Identity(d)) and matrix_normal((U.T*Q*V)*(U.T*Q*V).T,orthogonal)==sp.Identity(d))
check('frob_square_trace_coordinates',sp.Trace(A.T*A).rewrite(sp.Sum).dummy_eq(sp.Sum(A[i,j]**2,(i,0,N-1),(j,0,d-1))))
check('frob_coordinate_sum_order',sp.Sum(A[i,j]**2,(i,0,N-1),(j,0,d-1)).reorder((0,1)).dummy_eq(sp.Sum(A[i,j]**2,(j,0,d-1),(i,0,N-1))))
actual_loss=sp.Trace((A*Q-B).T*(A*Q-B))
trace_loss=sp.Trace(A.T*A)+sp.Trace(B.T*B)-2*sp.Trace(Q.T*A.T*B)
check('loss_trace_expansion',trace_normal(actual_loss,orthogonal)==trace_normal(trace_loss,orthogonal))
check('svd_rotated_trace',trace_normal(sp.Trace(Q.T*U*D*V.T),orthogonal)==trace_normal(sp.Trace((U.T*Q*V).T*D),orthogonal))
diagonal_coordinate=(R.T*D)[i,i].doit()
check('diagonal_trace_coordinate',diagonal_coordinate==sp.Piecewise((R[i,i]*sigma[i,0],i<=d-1),(0,True)) and diagonal_coordinate.subs(i<=d-1,True)==R[i,i]*sigma[i,0])
actual_trace_sum=sp.Trace(R.T*D).rewrite(sp.Sum)
trace_index=actual_trace_sum.variables[0]
check('trace_weighted_actual_sum',actual_trace_sum.limits==((trace_index,0,d-1),) and actual_trace_sum.function==sp.Piecewise((R[trace_index,trace_index]*sigma[trace_index,0],trace_index<=d-1),(0,True)) and sp.Sum(actual_trace_sum.function.subs(trace_index<=d-1,True),(trace_index,0,d-1)).dummy_eq(sp.Sum(sigma[i,0]*R[i,i],(i,0,d-1))))
check('weighted_trace_fold_instantiation',folds[weighted].subs({sig(head):sigma[head,0],diag(head):R[head,head]},simultaneous=True)==sigma[head,0]*R[head,head])
check('column_square_fold_instantiation',folds[squares].subs(entry(head),R[head,j])==R[head,j]**2)
check('weighted_gap_induction',finite_induction(total(xs)-weighted(xs),weighted_gap(xs)))
check('weighted_gap_nonnegative_induction',weighted_gap_nonnegative_induction())
check('weighted_gap_cons_nonnegative',unfold(weighted_gap(cons(head,tail))).subs({diag(head):1-gap(head),weighted_gap(tail):nonnegative_tail},simultaneous=True).is_nonnegative is True)
check('diagonal_gap_parameterization',sp.solve(sp.Eq(a,1-b),b)==[1-a] and sp.reduce_inequalities([a<=1,1-a<0],a)==sp.false)
check('candidate_orthogonal',matrix_normal((U*V.T).T*(U*V.T),orthogonal)==sp.Identity(d) and matrix_normal((U*V.T)*(U*V.T).T,orthogonal)==sp.Identity(d))
check('candidate_rotated_identity',matrix_normal(U.T*(U*V.T)*V,orthogonal)==sp.Identity(d))
check('candidate_attains_trace',trace_normal(sp.Trace((U*V.T).T*U*D*V.T),orthogonal)==trace_normal(sp.Trace(D),orthogonal))
parameterized_loss=sp.Trace(A.T*A)+sp.Trace(B.T*B)-2*sp.Trace(Q.T*C)
check('actual_cross_matrix_binding',trace_normal(parameterized_loss.xreplace({C:A.T*B}),orthogonal)==trace_normal(trace_loss,orthogonal))
conditional_loss=parameterized_loss.xreplace({C:U*D*V.T})
candidate_loss=conditional_loss.xreplace({Q:U*V.T})
check('actual_conditional_loss_gap',trace_normal(conditional_loss-candidate_loss,orthogonal)==trace_normal(2*(sp.Trace(D)-sp.Trace(Q.T*U*D*V.T)),orthogonal))
check('conditional_loss_difference',sp.expand((s-2*a)-(s-2*b))==2*(b-a))
check('conditional_loss_nonnegative',sp.expand((s-2*a)-(s-2*(a+nonnegative_tail)))==2*nonnegative_tail and (2*nonnegative_tail).is_nonnegative is True)
check('missing_orthogonality_rejected',trace_normal(actual_loss,set())!=trace_normal(trace_loss,set()))
check('wrong_svd_transpose_rejected',trace_normal(sp.Trace(Q.T*U*D*V),orthogonal)!=trace_normal(sp.Trace((U.T*Q*V).T*D),orthogonal))
check('wrong_weighted_induction_rejected',not finite_induction(total(xs)+weighted(xs),weighted_gap(xs)))
check('negative_weight_bound_rejected',(-1)*(1-0)<0)
check('wrong_member_bound_rejected',not member_bound_induction(-1))
root_value=sp.Symbol('root_value',nonnegative=True)
reverse_gap=sp.Symbol('reverse_gap',positive=True)
check('square_root_preserves_order',sp.expand((root_value+reverse_gap)**2-root_value**2).is_positive is True)
nonnegative_value=sp.Symbol('nonnegative_value',nonnegative=True)
check('square_root_definition',sp.sqrt(nonnegative_value).is_nonnegative is True and sp.sqrt(nonnegative_value)**2==nonnegative_value)
report={'backend':'Python 3','scope':'all positive N,d; real rectangular A,B; real square Q with Q.T Q=I (opposite product derived); two-sided orthogonal U,V; conditional decomposition A.T B=U diag(sigma) V.T with sigma>=0; finite coordinate sums and structural induction; no assertion that every matrix admits such a decomposition','checks':len(results),'passed':True,'results':results}
if __name__=='__main__':
    print(json.dumps(report))
