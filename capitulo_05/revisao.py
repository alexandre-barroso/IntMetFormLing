import json
import sympy as sp
results=[]
def check(identifier,condition):
    results.append({'id':identifier,'passed':bool(condition)})
def chain(values):
    return all(sp.expand(a-b)==0 for a,b in zip(values,values[1:]))
Q=sp.Rational
c,d,x,y,m,h,a=sp.symbols('c d x y m h a',real=True)
check('trimmed_mean_rounding',abs(Q(23,6)-Q(383,100))<Q(1,200))
check('square_expansion_chain',chain([(c+d)**2,(c+d)*(c+d),c*c+c*d+d*c+d*d,c**2+c*d+c*d+d**2,c**2+2*c*d+d**2]))
check('midpoint_recovery_chain',chain([(x+y)/2+(x-y)/2,(x+y+x-y)/2,2*x/2,x]) and chain([(x+y)/2-(x-y)/2,(x+y-(x-y))/2,(x+y-x+y)/2,2*y/2,y]))
check('recover_candidate',sp.expand(m+(a-m)-a)==0)
check('shifted_deviation_chains',chain([(m+d)-(m+h),d-h]) and chain([(m-d)-(m+h),-d-h]))
check('symmetric_loss_chain',chain([(d-h)**2+(-d-h)**2,(d*d-2*d*h+h*h)+(d*d+2*d*h+h*h),2*d*d+2*h*h]))
check('loss_penalty_nonnegative',(2*h*h).is_nonnegative is True)
mid=(x+y)/2
check('mean_minimum',(sp.expand((x-a)**2+(y-a)**2-(x-mid)**2-(y-mid)**2-2*(a-mid)**2)==0) and (2*(a-mid)**2).is_nonnegative is True)
k=sp.symbols('k',positive=True)
o=sp.symbols('o0:4',positive=True)
e=sp.symbols('e0:4',positive=True)
check('statistic_scale_four_cells',sp.simplify(2*sum(k*oi*sp.log(k*oi/(k*ei)) for oi,ei in zip(o,e))-k*2*sum(oi*sp.log(oi/ei) for oi,ei in zip(o,e)))==0)
t,E=sp.symbols('t E',positive=True)
check('statistic_scale_zero_extension',sp.limit(t*sp.log(t/E),t,0,dir='+')==0 and sp.limit(k*t*sp.log(k*t/(k*E)),t,0,dir='+')==0)
check("total_scale",sp.expand(sum(k*oi for oi in o)-k*sum(o))==0)
check("variance_rounding",abs(Q(29,95)-Q(3053,10000))<Q(1,20000))
report={'backend':'Python/SymPy','checks':len(results),'passed':all(r['passed'] for r in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
