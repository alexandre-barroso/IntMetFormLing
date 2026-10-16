from fractions import Fraction as Q
from math import factorial
import json
import sympy as sp

results = []

def check(name, condition):
    if not bool(condition):
        raise AssertionError(name)
    results.append({'id': name, 'passed': True})

def exponential_bounds(value, terms=40):
    if not isinstance(value, Q) or not isinstance(terms, int) or terms < 1:
        raise ValueError((value, terms))
    if value < 0:
        lower, upper = exponential_bounds(-value, terms)
        return Q(1)/upper, Q(1)/lower
    if value >= terms + 2:
        raise ValueError((value, terms))
    partial = sum((value**i / factorial(i) for i in range(terms + 1)), Q(0))
    first = value**(terms + 1)/factorial(terms + 1)
    ratio = value / (terms + 2)
    return partial, partial + first/(1-ratio)

def unit_logarithm_bounds(value, terms=30):
    if not isinstance(value, Q) or not Q(1) <= value <= Q(2) or not isinstance(terms, int) or terms < 1:
        raise ValueError((value, terms))
    z = (value-1)/(value+1)
    partial = sum((z**(2*i+1)/Q(2*i+1) for i in range(terms)), Q(0))
    error = z**(2*terms+1)/(1-z*z)
    return 2*partial, 2*(partial+error)

def logarithm_bounds(value):
    if not isinstance(value, Q) or value <= 0:
        raise ValueError(value)
    power = 0
    while value > 2:
        value /= 2
        power += 1
    while value < 1:
        value *= 2
        power -= 1
    lower, upper = unit_logarithm_bounds(value)
    l2, u2 = unit_logarithm_bounds(Q(2))
    if power < 0:
        return lower+power*u2, upper+power*l2
    return lower+power*l2, upper+power*u2

def negative_logarithm_bounds(value):
    lower, upper = logarithm_bounds(value)
    return -upper, -lower

def sigmoid_bounds(value):
    lower, upper = exponential_bounds(value)
    return lower/(1+lower), upper/(1+upper)

def softplus_loss_bounds(value):
    lower, upper = exponential_bounds(value)
    return logarithm_bounds(1+lower)[0]-value, logarithm_bounds(1+upper)[1]-value

def encloses_rounding(interval, printed, half_place):
    lower, upper = interval
    return isinstance(printed, Q) and isinstance(half_place, Q) and half_place > 0 and printed-half_place < lower <= upper < printed+half_place

x = sp.Symbol('x', real=True)
k = sp.Symbol('k', integer=True, nonnegative=True)
q, s, n = sp.symbols('q s n', positive=True)
term = q**k/sp.factorial(k)
check('exponential_term_ratio', sp.simplify(term.subs(k, k+1)/term-q/(k+1)) == 0)
ratio_gap = sp.factor(q/(n+2)-q/(n+2+s))
check('exponential_tail_ratio_majorant', ratio_gap == q*s/((n+2)*(n+s+2)) and ratio_gap.is_nonnegative is True)
partial_exp = sum(x**i/sp.factorial(i) for i in range(41))
check('exponential_taylor_remainder_identity', sp.simplify(sp.diff(sp.exp(x)-partial_exp, x)-(sp.exp(x)-partial_exp)-x**40/sp.factorial(40)) == 0)
check('exponential_taylor_initial_value', (sp.exp(x)-partial_exp).subs(x, 0) == 0)
r = sp.Symbol('r', positive=True)
geometric = sp.summation(r**k, (k, 0, sp.oo))
check('exponential_geometric_tail', geometric.args[0] == (1/(1-r), r < 1))
check('negative_exponential_reciprocal', sp.simplify(sp.exp(-x)*sp.exp(x)) == 1)
partial_log = sum(x**(2*i+1)/sp.Integer(2*i+1) for i in range(30))
check('logarithm_remainder_derivative', sp.factor(sp.diff(sp.log((1+x)/(1-x))-2*partial_log, x)-2*x**60/(1-x*x)) == 0)
check('logarithm_remainder_origin', (sp.log((1+x)/(1-x))-2*partial_log).subs(x, 0) == 0)
p, t = sp.symbols('p t', positive=True)
z = p/(1+p)
u = z*t/(1+t)
num, den = sp.fraction(sp.factor(1/(1-z*z)-1/(1-u*u)))
check('logarithm_majorant_nonnegative', all(c >= 0 for c in sp.Poly(num, p, t).coeffs()) and all(c > 0 for c in sp.Poly(den, p, t).coeffs()))
check('logarithm_integrated_majorant', sp.factor(sp.integrate(2*x**60/(1-z*z), (x, 0, z))-2*z**61/(61*(1-z*z))) == 0)
positive = sp.Symbol('positive', positive=True)
integer = sp.Symbol('integer', integer=True)
check('logarithm_scale_identity', sp.expand_log(sp.log(positive*2**integer)) == sp.log(positive)+integer*sp.log(2))
check('sigmoid_increasing', sp.diff(positive/(1+positive), positive).simplify() == 1/(1+positive)**2)
check('logarithm_increasing', sp.diff(sp.log(positive), positive) == 1/positive)

def log2_bounds(value):
    lower, upper = logarithm_bounds(value)
    l2, u2 = logarithm_bounds(Q(2))
    if lower < 0:
        raise ValueError(value)
    return lower/u2, upper/l2

def coarse_bounds(interval, precision=15):
    lower, upper = interval
    denominator = 10**precision
    return Q(lower.numerator*denominator//lower.denominator,denominator), Q(-((-upper.numerator*denominator)//upper.denominator),denominator)

def arctangent_bounds(value, terms=20):
    if not isinstance(value,Q) or not 0 <= value < 1 or not isinstance(terms,int) or terms<1:
        raise ValueError((value,terms))
    partial = sum(((-1)**i*value**(2*i+1)/Q(2*i+1) for i in range(terms)),Q(0))
    next_term = (-1)**terms*value**(2*terms+1)/Q(2*terms+1)
    return min(partial,partial+next_term),max(partial,partial+next_term)

forward = log2_bounds(Q(450000000,266305))
reverse = log2_bounds(Q(90000000,266305))
three = log2_bounds(Q(3))
check('pmi_forward_rounding', encloses_rounding(forward,Q('10.7'),Q('.05')))
check('pmi_reverse_rounding', encloses_rounding(reverse,Q('8.4'),Q('.05')))
check('log2_three_interval', Q('1.5845')<three[0]<=three[1]<Q('1.585'))
conditional = tuple(Q(3,8)*v for v in three)
initial = (Q(11,4)-Q(3,8)*three[1],Q(11,4)-Q(3,8)*three[0])
class_conditional = tuple(v-Q(2,3) for v in three)
check('conditional_entropy_rounding', encloses_rounding(conditional,Q('.594'),Q('.0005')))
check('initial_entropy_rounding', encloses_rounding(initial,Q('2.156'),Q('.0005')))
check('within_class_entropy_rounding', encloses_rounding(class_conditional,Q('.918'),Q('.0005')))

atan_partial = sum((-1)**i*x**(2*i+1)/sp.Integer(2*i+1) for i in range(20))
check('arctangent_remainder_derivative', sp.factor(sp.diff(sp.atan(x)-atan_partial,x)-x**40/(1+x*x))==0)
check('arctangent_remainder_origin', (sp.atan(x)-atan_partial).subs(x,0)==0)
check('arctangent_remainder_majorant', sp.factor(x**40-x**40/(1+x*x))==x**42/(1+x*x))
check('arctangent_integrated_majorant', sp.integrate(x**40,(x,0,positive))==positive**41/41)
check('arctangent_positive_lower_bound', sp.factor(1/(1+u*u)-1/(1+z*z))==sp.factor((z*z-u*u)/((1+u*u)*(1+z*z))) and sp.factor(z*z-u*u).is_positive is True)
angle = 4*sp.atan(sp.Rational(1,5))-sp.atan(sp.Rational(1,239))
angle_a,angle_b=sp.symbols('angle_a angle_b',real=True)
check('machin_tangent_identity', sp.expand_trig(sp.tan(4*angle_a-angle_b)).subs({angle_a:sp.atan(sp.Rational(1,5)),angle_b:sp.atan(sp.Rational(1,239))})==1)
check('machin_principal_range', 4*Q(1,5)/(1+Q(1,5)**2)-Q(1,239)>0 and 4*Q(1,5)<1)
check('pi_quarter_arctangent', sp.atan(1)==sp.pi/4)
check('pi_half_greater_than_one', sp.diff(sp.atan(x),x)==1/(1+x*x) and sp.factor(1/(1+u*u)-Q(1,2)).is_positive is True)
a5,b5=arctangent_bounds(Q(1,5))
a239,b239=arctangent_bounds(Q(1,239))
pi_bounds=(16*a5-4*b239,16*b5-4*a239)
sqrt_two_pi=(Q('2.50662827463100'),Q('2.50662827463101'))
check('sqrt_two_pi_enclosure', 0<sqrt_two_pi[0]<sqrt_two_pi[1] and sqrt_two_pi[0]**2<2*pi_bounds[0] and 2*pi_bounds[1]<sqrt_two_pi[1]**2)

def density_bounds(time):
    if not isinstance(time,Q) or time<=0:
        raise ValueError(time)
    lower,upper=coarse_bounds(logarithm_bounds(time))
    lower+=Q(268,100)
    upper+=Q(268,100)
    squared=(Q(0) if lower<=0<=upper else min(lower*lower,upper*upper),max(lower*lower,upper*upper))
    variance=2*Q(59,100)**2
    exponent=coarse_bounds((-squared[1]/variance,-squared[0]/variance))
    numerator=(exponential_bounds(exponent[0])[0],exponential_bounds(exponent[1])[1])
    denominator=(time*Q(59,100)*sqrt_two_pi[0],time*Q(59,100)*sqrt_two_pi[1])
    return numerator[0]/denominator[1],numerator[1]/denominator[0]

check('density_endpoint0', encloses_rounding(density_bounds(Q(3,100)),Q('8.447984'),Q(1,2000000)))
check('density_endpoint1', encloses_rounding(density_bounds(Q(7,50)),Q('2.322823'),Q(1,2000000)))
print(json.dumps({'backend':'Python 3','arithmetic':'exact rational enclosures with geometric and alternating remainders','checks':len(results),'passed':True,'results':results},ensure_ascii=False))
