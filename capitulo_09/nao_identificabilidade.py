import json
import sympy as sp

n=sp.Symbol('n',positive=True,integer=True)
i,j=sp.symbols('i j',integer=True,nonnegative=True)
M=sp.MatrixSymbol('M',n,n)
row=sp.Sum(M[i,j],(j,0,n-1))
column=sp.Sum(M[j,i],(j,0,n-1))
score=2*M[i,i]/(row+column)
transposed_score=2*M.T[i,i]/(sp.Sum(M.T[i,j],(j,0,n-1))+sp.Sum(M.T[j,i],(j,0,n-1)))
t=sp.Symbol('t',positive=True,integer=True)
C=sp.eye(9)
C[0,1]=t
def f1(matrix,k):
    return 2*matrix[k,k]/(sum(matrix[k,j] for j in range(9))+sum(matrix[j,k] for j in range(9)))

results=[]
def check(name,value):
    if not value:raise AssertionError(name)
    results.append({'id':name,'passed':True})

check('transpose_actual_symbolic_f1',sp.cancel(transposed_score-score)==0)
check('nine_class_nonnegative_integer_counts',all(v.is_integer is True and v.is_nonnegative is True for v in C))
check('nine_class_positive_denominators',all((sum(C[k,j] for j in range(9))+sum(C[j,k] for j in range(9))).is_positive is True for k in range(9)))
check('nine_class_different_error_locations',C!=C.T and C[0,1]-C.T[0,1]==t)
check('all_nine_unrounded_scores_equal',all(sp.cancel(f1(C,k)-f1(C.T,k))==0 for k in range(9)))
check('macro_scores_equal',sp.cancel(sum(f1(C,k) for k in range(9))/9-sum(f1(C.T,k) for k in range(9))/9)==0)
check('same_total_and_correct_counts',sum(C)==sum(C.T) and sp.trace(C)==sp.trace(C.T))
check('claim_unique_matrix_rejected',C!=C.T and all(sp.cancel(f1(C,k)-f1(C.T,k))==0 for k in range(9)))
check('symmetric_matrix_not_a_counterexample',sp.eye(9)==sp.eye(9).T)
print(json.dumps({'backend':'Python 3','scope':'F1 per class with positive denominators; arbitrary-size symbolic transpose identity; concrete nine-class family with arbitrary positive integer error count, no reconstruction of a published confusion matrix','checks':len(results),'passed':True,'results':results}))
