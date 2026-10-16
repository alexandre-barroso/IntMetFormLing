import json
import sympy as sp

checks=[]
def check(name, proposition):
    if proposition is not True and proposition != sp.true:
        raise AssertionError((name, proposition))
    checks.append({"id":name,"passed":True})

x,C,alpha,D,beta=sp.symbols("x C alpha D beta",positive=True)
zipf=C*x**(-alpha)
zipf_derivative=sp.diff(zipf,x)
check("zipf_derivative",sp.simplify(zipf_derivative-(-alpha*C*x**(-alpha-1)))==0)
check("zipf_derivative_negative",zipf_derivative.is_negative)
heaps=D*x**beta
check("heaps_derivative",sp.simplify(sp.diff(heaps,x)-beta*D*x**(beta-1))==0)
check("heaps_derivative_positive",sp.diff(heaps,x).is_positive)
k,delta=sp.symbols("k delta",positive=True)
check("heaps_sublinear_log_ratio",sp.simplify(sp.expand_log(sp.log((1+k)**(1-delta)/(1+k)),force=True)+delta*sp.log(1+k))==0)
check("heaps_sublinear_log_ratio_negative",(-delta*sp.log(1+k)).is_negative)
check("fractional_power_equation",sp.powdenest((x**sp.Rational(63,100))**100)==x**63)
z=sp.Symbol("z",positive=True)
check("fractional_power_unique_log_step",sp.expand_log(sp.log(z**100),force=True)==100*sp.log(z))
p=sp.Symbol("p",positive=True)
surprise=-sp.log(p)/sp.log(2)
check("surprise_derivative",sp.simplify(sp.diff(surprise,p)+1/(p*sp.log(2)))==0)
check("surprise_derivative_negative",sp.diff(surprise,p).is_negative)
u,d=sp.symbols("u d",positive=True)
check("inverse_duration_difference",sp.cancel(1/u-1/(u+d)-d/(u*(u+d)))==0)
check("inverse_duration_order",(d/(u*(u+d))).is_positive)
a,b,c=sp.symbols("a b c",real=True)
F=sp.Function("F")
check("primitive_constant_cancels",sp.expand((F(b)+c)-(F(a)+c))==F(b)-F(a))
check("normalization_scale",sp.solve(c*c-1,c)==[-1,1])
print(json.dumps({"backend":"Python/SymPy","scope":"general symbolic derivatives, signs, power and integral-scaling identities; arbitrary-function Newton–Leibniz theorem is formalized in Exposicao.lean", "checks":len(checks),"passed":True,"results":checks}))
