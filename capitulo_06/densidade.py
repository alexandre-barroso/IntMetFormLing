import json
import sympy as s

results=[]
def check(name,condition):
    results.append({'id':name,'passed':bool(condition)})
a,t=s.symbols('a t',real=True)
f=s.Function('f')
check('zero_width',s.simplify(a-a)==0)
check('point_mass_zero',s.Integral(f(t),(t,a,a)).doit()==0)
report={'backend':'Python/SymPy','checks':len(results),'passed':all(x['passed'] for x in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
