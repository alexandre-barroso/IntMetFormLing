import json
import sympy as sp

results=[]
def check(identifier,condition):
    results.append({"id":identifier,"passed":bool(condition)})
Q=sp.Rational
C=sp.Matrix([[8,10,1],[5,60,50],[3,30,200]])
tp=[C[i,i] for i in range(3)]
fp=[sum(C.row(i))-tp[i] for i in range(3)]
fn=[sum(C.col(i))-tp[i] for i in range(3)]
precision=[tp[i]/(tp[i]+fp[i]) for i in range(3)]
recall=[tp[i]/(tp[i]+fn[i]) for i in range(3)]
f1=[2*tp[i]/(2*tp[i]+fp[i]+fn[i]) for i in range(3)]
check("confusion_totals",sum(C)==367 and sum(tp)==268)
check("confusion_components",tp==[8,60,200] and fp==[11,55,33] and fn==[8,40,51])
check("urgent_metrics",(precision[0],recall[0],f1[0])==(Q(8,19),Q(1,2),Q(16,35)))
check("f1_classes",f1==[Q(16,35),Q(24,43),Q(100,121)])
check("micro_f1",2*sum(tp)/(2*sum(tp)+sum(fp)+sum(fn))==Q(268,367))
check("macro_f1",sum(f1)/3==(Q(16,35)+Q(24,43)+Q(100,121))/3)
safe=lambda a,b:None if b==0 else Q(a,b)
check("undefined_precision",safe(0,0) is None and safe(0,100)==0)
x1,x2=sp.symbols('x1 x2',real=True)
W=sp.ones(2);bias=sp.Matrix([0,-1]);x=sp.Matrix([x1,x2])
check("neural_matrix",W*x+bias==sp.Matrix([x1+x2,x1+x2-1]))
h=(W*x+bias).applyfunc(lambda z:sp.Max(0,z))
check("neural_hidden",h==sp.Matrix([sp.Max(0,x1+x2),sp.Max(0,x1+x2-1)]))
y=sp.Max(0,h[0]-2*h[1])
check("neural_all_inputs",[y.subs({x1:a,x2:b}) for a,b in [(0,0),(0,1),(1,0),(1,1)]]==[0,1,1,0])
n,d,dk,dv=sp.symbols('n d dk dv',integer=True,positive=True)
i,j,r=sp.symbols('i j r',integer=True,nonnegative=True)
X=sp.MatrixSymbol('X',n,d);WQ=sp.MatrixSymbol('WQ',d,dk)
queries=sp.MatrixSymbol('Q',n,dk);keys=sp.MatrixSymbol('K',n,dk);values=sp.MatrixSymbol('V',n,dv)
check("projection_entry",(X*WQ).shape==(n,dk) and (X*WQ)[i,j].dummy_eq(sp.Sum(X[i,r]*WQ[r,j],(r,0,d-1))))
check("score_entry",(queries*keys.T).shape==(n,n) and (queries*keys.T)[i,j].dummy_eq(sp.Sum(queries[i,r]*keys[j,r],(r,0,dk-1))))
alpha=sp.MatrixSymbol('alpha',n,n)
check("attention_entry",(alpha*values).shape==(n,dv) and (alpha*values)[i,j].dummy_eq(sp.Sum(alpha[i,r]*values[r,j],(r,0,n-1))))
s=sp.symbols('s',positive=True)
check("attention_weights",s/s==1)
a,b=sp.symbols('a b',real=True)
check("attention_sum_step",sp.cancel(a/s+b/s-(a+b)/s)==0)
width=sp.symbols('width',integer=True,positive=True)
W1=sp.MatrixSymbol('W1',d,width);W2=sp.MatrixSymbol('W2',width,d)
xrow=sp.MatrixSymbol('x',1,d);b1=sp.MatrixSymbol('b1',1,width);b2=sp.MatrixSymbol('b2',1,d)
hidden=sp.MatrixSymbol('rho',1,width)
check("feed_forward_entry",(xrow*W1+b1).shape==(1,width) and (hidden*W2+b2).shape==(1,d) and (hidden*W2+b2)[0,j].dummy_eq(sp.Sum(hidden[0,r]*W2[r,j],(r,0,width-1))+b2[0,j]))
v0,v1,v2,v3,p,y=sp.symbols('v0 v1 v2 v3 p y',real=True)
check("cbow_coordinate",sp.expand((v0+v1+v2+v3)/4-Q(1,4)*(v0+v1+v2+v3))==0)
check("brier_binary",sp.expand((p-y)**2+((1-p)-(1-y))**2-2*(p-y)**2)==0)
nc,ne,sc,se=sp.symbols('nc ne sc se',positive=True)
check("grouped_mean",sp.cancel((nc*(sc/nc)+ne*(se/ne))/(nc+ne)-(sc+se)/(nc+ne))==0)
p,q=sp.symbols('p q',positive=True)
check("likelihood_log",sp.simplify(sp.expand_log(sp.log(p**608*q**319))-608*sp.log(p)-319*sp.log(q))==0)

w1,w2=sp.symbols("w1 w2",real=True)
check('ot_first_preference', sp.simplify((-w1-w2)-(-2*w1)-(w1-w2))==0)
check('ot_second_preference', sp.simplify(-w1-(-w2)-(w2-w1))==0)
check('ot_margin_sum', sp.simplify((w1-w2)+(w2-w1))==0)
gap=sp.Symbol("gap",real=True)
check('ot_incompatible_preferences', sp.reduce_inequalities([gap>0,-gap>0],gap)==sp.false)
check('ot_incompatible_margins', sp.reduce_inequalities([gap>=1,-gap>=1],gap)==sp.false)


report={"backend":"Python/SymPy","checks":len(results),"passed":all(r['passed'] for r in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
