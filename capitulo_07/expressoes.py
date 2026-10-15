import json
import sympy as sp

results=[]
def check(identifier,condition):
    results.append({"id":identifier,"passed":bool(condition)})
Q=sp.Rational
X=sp.Matrix([[1,0]]*3+[[1,1]]*3)
y=sp.Matrix([233,204,242,130,112,142]);beta=sp.Matrix([Q(679,3),Q(-295,3)])
a,b,c,h,q=sp.symbols('a b c h q',real=True)
check("predictions",X*sp.Matrix([a,b])==sp.Matrix([a,a,a,a+b,a+b,a+b]))
check("normal_matrix",X.T*X==sp.Matrix([[6,3],[3,3]]))
check("normal_target",X.T*y==sp.Matrix([1063,384]))
check("normal_equation",X.T*X*beta==X.T*y)
r=y-X*beta
check("residuals_from_matrix",r==sp.Matrix([Q(20,3),Q(-67,3),Q(47,3),2,-16,14]))
check("residual_orthogonality",X.T*r==sp.zeros(2,1))
check("residual_loss",r.dot(r)==Q(3734,3))
rab=y-X*sp.Matrix([a,b])
check("loss_from_matrix",sp.expand(rab.dot(rab)-(6*a*a+6*a*b+3*b*b-2126*a-768*b+204077))==0)
n=sp.symbols('n',integer=True,positive=True)
sA,sB,tA,tB=sp.symbols('sA sB tA tB',real=True)
check("paired_mean_base",(0-0)/n==0)
check("paired_mean_step",sp.expand((sA+tA)-(sB+tB)-(sA-sB)-(tA-tB))==0)
check("paired_mean_general",sp.cancel((sA-sB)/n-sA/n+sB/n)==0)
check("swap_count_base",2**0==1)
check("swap_count_step",sp.simplify(2*2**n-2**(n+1))==0)
check("correlation_simplification",sp.simplify(Q(-295,2)/sp.sqrt(Q(3,2)*Q(94493,6))+295/sp.sqrt(94493))==0)
check("indicator_product", a*0==0 and 1*1==1)
check("nonidentifiable_coefficients",sp.expand(b*q+c*q-(b+c)*q)==0 and sp.expand((b+h)*q+(c-h)*q-(b+c)*q)==0)
plotted=sp.Matrix([Q(2263333333333,10000000000)]*3+[128]*3)
check("fitted_graph_rounding",all(abs(a-b)<Q(1,20000000000) for a,b in zip(plotted,X*beta)))
check("residual_segments",y-plotted==(y-X*beta)+(X*beta-plotted))
report={"backend":"Python/SymPy","checks":len(results),"passed":all(r['passed'] for r in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
