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

observed = [Q(29), Q(13), Q(123), Q(31612)]
expected = [Q(6384,31777), Q(1328250,31777), Q(4823720,31777), Q(1003619375,31777)]
ratios = [o/e for o,e in zip(observed, expected, strict=True)]
check('source_ratios', ratios == [Q(921533,6384), Q(413101,1328250), Q(3908571,4823720), Q(1004534524,1003619375)])
contributions = [(o*lower,o*upper) for o,(lower,upper) in zip(observed, map(logarithm_bounds,ratios), strict=True)]
printed = [Q('144.1951'), Q('-15.1830'), Q('-25.8760'), Q('28.8122')]
check('four_log_contributions', all(encloses_rounding(interval, value, Q(1,20000)) for interval,value in zip(contributions,printed,strict=True)))
g_squared = tuple(2*sum((interval[j] for interval in contributions), Q(0)) for j in (0,1))
check('g_squared_rounding', encloses_rounding(g_squared, Q('263.90'), Q(1,200)))
print(json.dumps({'backend':'Python 3','arithmetic':'exact rational enclosures with geometric remainder','checks':len(results),'passed':True,'results':results},ensure_ascii=False))
