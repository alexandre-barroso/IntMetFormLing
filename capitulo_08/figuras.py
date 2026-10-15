import json
import sympy as sp
Q=sp.Rational
results=[]
def check(identity,condition):
    results.append({'id':identity,'passed':bool(condition)})
def close(actual,published,digits):
    return abs(sp.N(actual,80)-Q(published))<Q(1,2*10**digits)
check('loss_positive_point',close(-sp.log(Q(7,10)),'0.356674944',9))
check('loss_negative_point',close(-sp.log(Q(3,10)),'1.203972804',9))
check('loss_start_point',close(sp.log(2),'0.693147181',9))
check('sigmoid_point',close(1/(1+sp.exp(Q(-833,1000))),'0.6969888901',10))
check('gradient_loss_point',close(sp.log(1+sp.exp(Q(7,10)))-Q(7,10),'0.403186049',9))
z=sp.symbols('z',real=True)
check('gradient_loss_identity',sp.simplify(sp.expand_log(sp.log((1+sp.exp(-z))*sp.exp(z)),force=True)-z-sp.log(1+sp.exp(-z)))==0)
a=sp.symbols('a',nonnegative=True)
check('relu_negative',sp.Max(0,-a)==0)
check('relu_positive',sp.Max(0,a)==a)
check('relu_graph_points',[sp.Max(0,x) for x in [-Q(12,10),0,2]]==[0,0,2])
w=sp.symbols('w',real=True)
check('constraint_arrows',sp.simplify((w+1+Q(2,5))-(w-Q(2,5)))>1 and sp.simplify((w+Q(2,5))-(w-1-Q(2,5)))>1)
report={'backend':'Python/SymPy','checks':len(results),'passed':all(r['passed'] for r in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
