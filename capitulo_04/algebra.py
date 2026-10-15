import json
import sympy as sp

results=[]
def check(identifier,condition):
    results.append({'id':identifier,'passed':bool(condition)})
d,n=sp.symbols('d n',integer=True,positive=True)
u=sp.MatrixSymbol('u',1,d)
v=sp.MatrixSymbol('v',1,d)
q=sp.MatrixSymbol('q',d,d)
check('transpose_product',(v*q).T==q.T*v.T)
raw_product=(u*q)*(v*q).T
expanded_product=u*q*q.T*v.T
gram=sp.MatMul(q,q.T,evaluate=False)
grouped_product=sp.MatMul(u,gram,v.T,evaluate=False)
orthogonal_product=grouped_product.xreplace({gram:sp.Identity(d)})
check('orthogonal_product_chain',sp.simplify(raw_product-expanded_product)==sp.ZeroMatrix(1,1) and sp.simplify(expanded_product-grouped_product)==sp.ZeroMatrix(1,1) and orthogonal_product.doit()==u*v.T)
w1=sp.MatrixSymbol('w1',n,d)
w2=sp.MatrixSymbol('w2',n,d)
i,j,k=sp.symbols('i j k',integer=True)
entry_sum=sp.Sum(w1[i,k]*q[k,j],(k,0,d-1))
check('alignment_entry_general',(w1*q)[i,j].as_dummy()==entry_sum.as_dummy() and sp.simplify((w1*q-w2)[i,j].as_dummy()-(entry_sum-w2[i,j]).as_dummy())==0)
report={'backend':'Python/SymPy','checks':len(results),'passed':all(r['passed'] for r in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
