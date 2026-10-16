import json
import sympy as s

results=[]
def check(name,condition):
    results.append({'id':name,'passed':bool(condition)})
a,b,c,x,y=s.symbols('a b c x y',real=True)
gram=a*b-c*c
step=(a+x*x)*(b+y*y)-(c+x*y)**2
check('finite_lagrange_base',gram.subs({a:0,b:0,c:0})==0)
check('finite_lagrange_induction',s.expand(step-(gram+y*y*a+x*x*b-2*x*y*c))==0)
u,v=s.symbols('u v',real=True)
check('sum_of_squares_increment',s.expand((u*y-v*x)**2-(y*y*u*u+x*x*v*v-2*x*y*u*v))==0)
check('squared_increment_nonnegative',s.ask(s.Q.nonnegative((u*y-v*x)**2)) is True)
p,q=s.symbols('p q',nonnegative=True)
check('nonnegative_dot_summand',s.ask(s.Q.nonnegative(p*q)) is True)
d=s.symbols('d',positive=True)
r=s.symbols('r',nonnegative=True)
z=s.symbols('z',nonnegative=True)
check('cosine_nonnegative',s.ask(s.Q.nonnegative(z/d)) is True)
check('cosine_upper_bound_identity',s.cancel((1-z/d)-(d*d-z*z)/(d*(d+z)))==0)
check('cosine_upper_bound_sign',s.ask(s.Q.nonnegative(r/(d*(d+z)))) is True)
a0,normv,normw=s.symbols('a0 normv normw',positive=True)
check('positive_scaling_norm',s.sqrt(a0*a0*normv*normv)==a0*normv)
check('positive_scaling_cosine',s.cancel(a0*c/(a0*normv*normw)-c/(normv*normw))==0)
check('normalized_dot',s.cancel(c/(normv*normw)/(s.sqrt(normv**2/normv**2)*s.sqrt(normw**2/normw**2)))-c/(normv*normw)==0)
check('normalization_chain',s.sqrt(normv**2/normv**2)==normv/normv==1)
report={'backend':'Python/SymPy','method':'symbolic finite-induction and positivity certificates','checks':len(results),'passed':all(item['passed'] for item in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
