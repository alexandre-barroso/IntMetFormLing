import json
import sympy as sp

u,m=sp.symbols('u m',real=True)
expectation=sp.Function('expectation')
def variance(x):return expectation((x-expectation(x))**2)
results=[]
def check(name,value):
    if not value:raise AssertionError(name)
    results.append({'id':name,'passed':True})
check('zero_centered_integrand',sp.expand((u-0)**2-u**2)==0)
check('expectation_of_identical_integrands',expectation((u-0)**2)==expectation(u**2))
check('variance_definition',variance(u)==expectation((u-expectation(u))**2))
check('mean_zero_variance_chain',variance(u).subs(expectation(u),0)==expectation((u-0)**2)==expectation(u**2))
check('nonzero_mean_cannot_be_erased',variance(u).subs(expectation(u),1)!=expectation(u**2))
check('unspecified_mean_cannot_be_erased',variance(u).subs(expectation(u),m)!=expectation(u**2))
print(json.dumps({'backend':'Python 3','scope':'definitional identity for a square-integrable real random variable with mean0; expectation kept as an arbitrary operator on integrands; no Gaussian or independence premise','checks':len(results),'passed':True,'results':results}))
