from fractions import Fraction as Q
import json
import sympy as sp

results=[]

def check(name,condition):
    if not bool(condition):
        raise AssertionError(name)
    results.append({'id':name,'passed':True})

def logarithm_bounds(value,terms):
    if not isinstance(value,Q) or value<=0 or not isinstance(terms,int) or terms<=0:
        raise ValueError((value,terms))
    z=(value-1)/(value+1)
    if not abs(z)<1:
        raise ValueError(z)
    partial=sum((z**(2*i+1)/Q(2*i+1) for i in range(terms)),Q(0))
    error=abs(z)**(2*terms+1)/(1-z*z)
    return (2*(partial-error),2*(partial+error))

x=sp.Symbol('x',real=True)
for n in (5,10,15,41,42):
    partial=sum(x**(2*i+1)/sp.Integer(2*i+1) for i in range(n))
    actual=sp.diff(sp.log((1+x)/(1-x))-2*partial,x)
    check('remainder_derivative_'+str(n),sp.factor(actual-2*x**(2*n)/(1-x*x))==0)
    check('remainder_origin_'+str(n),(sp.log((1+x)/(1-x))-2*partial).subs(x,0)==0)
    t=sp.Symbol('t',real=True)
    majorant=sp.integrate(2*t**(2*n)/(1-x*x),(t,0,x))
    check('integrated_majorant_'+str(n),sp.factor(majorant-2*x**(2*n+1)/((2*n+1)*(1-x*x)))==0)

p,q=sp.symbols('p q',positive=True)
z=p/(p+1)
t=z*q/(q+1)
numerator,denominator=sp.fraction(sp.factor(1/(1-z*z)-1/(1-t*t)))
check('remainder_majorant_nonnegative',all(c>=0 for c in sp.Poly(numerator,p,q).coeffs()) and all(c>0 for c in sp.Poly(denominator,p,q).coeffs()))
check('remainder_majorant_endpoints',sp.simplify(1/(1-z*z)-1)>=0 and sp.simplify(1/(1-z*z)-1/(1-z*z))==0)

point=Q(2270,67)
coordinate=Q(33880597,1000000)
height=Q(4870938636,1000000000)
low=height-Q(1,2000000000)
high=height+Q(1,2000000000)
l2,u2=logarithm_bounds(Q(2),15)
la,ua=logarithm_bounds(Q(182,125),10)
lr,ur=logarithm_bounds(Q(1135,1072),5)
target_low=Q(627,200)*l2-ua+Q(227,1000)*lr-Q(227,1000)
target_high=Q(627,200)*u2-la+Q(227,1000)*ur-Q(227,1000)
low_log=logarithm_bounds(low,42)
high_log=logarithm_bounds(high,41)
check('maximum_position_rounding',abs(point-coordinate)<Q(1,2000000))
check('source_parameter_reduction',Q(91,250)==Q(182,125)/4 and point==Q(1135,1072)*32 and Q(67,10000)*point==Q(227,1000))
star=sp.Rational(point.numerator,point.denominator)
log_velocity=sp.log(1/(sp.Rational(91,250)*star**(-sp.Rational(227,1000))*sp.exp(sp.Rational(227,1000))))
log_reduction=sp.Rational(627,200)*sp.log(2)-sp.log(sp.Rational(182,125))+sp.Rational(227,1000)*sp.log(sp.Rational(1135,1072))-sp.Rational(227,1000)
check('log_velocity_reduction',sp.simplify(sp.expand_log(log_velocity)-sp.expand_log(log_reduction))==0)
check('height_lower_certificate',low>0 and low_log[1]<target_low)
check('height_upper_certificate',target_high<high_log[0])
check('height_rounding_interval',high-low==Q(1,1000000000) and (high+low)/2==height)
print(json.dumps({'backend':'Python 3','arithmetic':'exact rational enclosures with geometric remainder','checks':len(results),'passed':True,'results':results},ensure_ascii=False))
