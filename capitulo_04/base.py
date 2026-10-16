import json
import sys
import sympy as sp

results=[]
def check(identifier,condition):
    results.append({"id":identifier,"passed":bool(condition)})
identity=sp.eye(9)
x=sp.Matrix(sp.symbols("x1:10",real=True))
check("c04_p02_coordinate",identity*x==x)
check("c04_p02_independent",sp.linsolve((identity,sp.zeros(9,1)))==sp.FiniteSet(sp.Tuple(*([0]*9))))
check("c04_p02_orthonormal",identity.T*identity==sp.eye(9))
check("c04_p02_basis_reconstruction",sum((x[i]*identity[:,i] for i in range(9)),sp.zeros(9,1))==x)
check("c04_p02_unit_norm",all(identity[:,i].norm()==1 for i in range(9)))
check("c04_p02_orthogonal",all(identity[:,i].dot(identity[:,j])==0 for i in range(9) for j in range(9) if i!=j))
report={"backend":"Python/SymPy","checks":len(results),"passed":all(item["passed"] for item in results),"results":results}
print(json.dumps(report))
sys.exit(0 if report["passed"] else 1)
