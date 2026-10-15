import json
import sympy as sp
Q=sp.Rational
results=[]
def check(identity,condition):
    results.append({'id':identity,'passed':bool(condition)})
n=sp.symbols('n',positive=True)
velocity=1/(Q(364,1000)*n**Q(-227,1000)*sp.exp(Q(67,10000)*n))
maximum=Q(227,1000)/Q(67,10000)
check('maximum_position',maximum==Q(2270,67) and abs(maximum-Q(33880597,1000000))<Q(1,2000000))
check('stationary_velocity',sp.simplify(sp.diff(velocity,n).subs(n,maximum))==0)
check('maximum_velocity_point',abs(sp.N(velocity.subs(n,maximum),80)-Q(4870938636,1000000000))<Q(1,2000000000))
check('log_velocity',sp.simplify(sp.expand_log(sp.log(velocity),force=True)+sp.log(Q(364,1000))-Q(227,1000)*sp.log(n)+Q(67,10000)*n)==0)
check('rational_log_scaling',Q(364,1000)==Q(182,125)/2**2 and maximum==Q(1135,1072)*2**5)
check('velocity_derivative',sp.simplify(sp.diff(velocity,n)-velocity*(Q(227,1000)/n-Q(67,10000)))==0)
check('velocity_positive',velocity.is_positive is True)
check('velocity_derivative_positive_domain',sp.reduce_inequalities(Q(227,1000)/n-Q(67,10000)>0,n)==(n<Q(2270,67)))
check('velocity_derivative_negative_domain',sp.reduce_inequalities(Q(227,1000)/n-Q(67,10000)<0,n)==(Q(2270,67)<n))
report={'backend':'Python/SymPy','checks':len(results),'passed':all(r['passed'] for r in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
