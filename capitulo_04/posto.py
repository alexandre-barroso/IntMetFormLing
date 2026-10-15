import json
import sympy as sp

m,n=sp.symbols('m n',integer=True,positive=True)
u=sp.MatrixSymbol('u',m,2)
v=sp.MatrixSymbol('v',n,2)
sigma=sp.MatrixSymbol('sigma',2,2)
inverse=sp.MatrixSymbol('inverse',2,2)
x=sp.MatrixSymbol('x',n,1)
c=sp.MatrixSymbol('c',2,1)
i2=sp.Identity(2)
relations={(u.T,u):i2,(v.T,v):i2,(sigma,inverse):i2,(inverse,sigma):i2}
def reduce_relations(expression):
    if not isinstance(expression,sp.MatMul):
        return expression
    factors=list(expression.doit().args)
    while True:
        changed=False
        for index in range(len(factors)-1):
            pair=(factors[index],factors[index+1])
            if pair in relations:
                factors[index:index+2]=[relations[pair]]
                changed=True
                break
        expression=sp.MatMul(*factors).doit()
        if not changed:
            return expression
        factors=list(expression.args) if isinstance(expression,sp.MatMul) else [expression]
s1,s2=sp.symbols('s1 s2',positive=True)
diagonal=sp.diag(s1,s2)
diagonal_inverse=sp.diag(1/s1,1/s2)
reconstruction=u*sigma*v.T
coordinate_map=sigma*v.T*x
preimage=v*inverse*c
results=[]
def check(identifier,condition):
    results.append({'id':identifier,'passed':bool(condition)})
check('positive_diagonal_inverse',diagonal*diagonal_inverse==sp.eye(2) and diagonal_inverse*diagonal==sp.eye(2) and diagonal.det().is_positive is True)
check('rank_image_contained_in_two_columns',reconstruction*x==u*coordinate_map and coordinate_map.shape==(2,1))
check('rank_every_two_coordinate_image_attained',reduce_relations(reconstruction*preimage)==u*c and preimage.shape==(n,1))
check('rank_two_coordinate_uniqueness',reduce_relations(u.T*(u*c))==c)
a,b,first,second=sp.symbols('a b first second',real=True)
check('rank_column_coefficients_unique',sp.linsolve([s1*a,s2*b],(a,b))==sp.FiniteSet((0,0)) and sp.linsolve([a-first,b-second],(a,b))==sp.FiniteSet((first,second)))
check('rank_coordinate_space_dimension',sp.eye(2).rank()==2 and diagonal.rank()==2 and u.shape[1]==2)
check('rank_zero_column_counterexample',sp.zeros(2,2).rank()!=2)
report={'backend':'Python/SymPy','checks':len(results),'passed':all(r['passed'] for r in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
