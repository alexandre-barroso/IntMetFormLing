import json
import sympy as sp
Q=sp.Rational
results=[]
def check(identity,condition):
    results.append({'id':identity,'passed':bool(condition)})
t=sp.symbols('t',positive=True)
density=sp.exp(-(sp.log(t)+Q(268,100))**2/(2*Q(59,100)**2))/(t*Q(59,100)*sp.sqrt(2*sp.pi))
check('density_endpoints',all(abs(sp.N(density.subs(t,x),80)-y)<Q(1,2000000) for x,y in [(Q(3,100),Q('8.447984')),(Q(14,100),Q('2.322823'))]))
check('density_nonnegative',density.is_positive is True)
check('shaded_interval',0<Q(3,100)<Q(14,100)<Q(8,10))
check('lognormal_model',sp.simplify(density-sp.exp(-(sp.log(t)-Q(-268,100))**2/(2*Q(59,100)**2))/(t*Q(59,100)*sp.sqrt(2*sp.pi)))==0)
report={'backend':'Python/SymPy','checks':len(results),'passed':all(r['passed'] for r in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
