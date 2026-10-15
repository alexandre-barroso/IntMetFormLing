import json
import sympy as sp

results=[]
def check(identifier,condition):
    results.append({"id":identifier,"passed":bool(condition)})
    if not condition:
        raise AssertionError(identifier)

def fit(x,y):
    if len(x)==0 or len(x)!=len(y):
        raise ValueError('nonempty paired observations required')
    n=sp.Integer(len(x));mx=sum(x)/n;my=sum(y)/n
    xx=sum((v-mx)**2 for v in x)
    if xx.is_positive is not True:
        raise ValueError('Sxx>0 required for slope identification')
    xy=sum((v-mx)*(w-my) for v,w in zip(x,y))
    slope=xy/xx
    return sp.simplify(my-slope*mx),sp.simplify(slope)

def rejects(call):
    try:
        call()
    except ValueError:
        return True
    return False

n,xx=sp.symbols('n xx',positive=True)
xy,yy,mx,my,a,b=sp.symbols('xy yy mx my a b',real=True)
loss=yy-2*b*xy+b*b*xx+n*(my-a-b*mx)**2
minimum=yy-xy**2/xx
excess=xx*(b-xy/xx)**2+n*(my-a-b*mx)**2
check('general_completed_square',sp.cancel(loss-minimum-excess)==0)
check('general_excess_nonnegative',excess.is_nonnegative)
H=sp.hessian(loss,(a,b))
check('general_hessian_positive_definite',H[0,0].is_positive and sp.factor(H.det()).is_positive)
solution=sp.solve([sp.diff(loss,a),sp.diff(loss,b)],(a,b))
check('general_critical_unique',set(solution)=={a,b} and sp.cancel(solution[a]-my+mx*xy/xx)==0 and sp.cancel(solution[b]-xy/xx)==0)
check('general_critical_loss',sp.cancel(loss.subs({a:my-mx*xy/xx,b:xy/xx})-minimum)==0)
xs=sp.symbols('x0:6',real=True);ys=sp.symbols('y0:6',real=True)
xbar=sum(xs)/6;ybar=sum(ys)/6
sxx=sum((x-xbar)**2 for x in xs);sxy=sum((x-xbar)*(y-ybar) for x,y in zip(xs,ys));syy=sum((y-ybar)**2 for y in ys)
original=sum((y-a-b*x)**2 for x,y in zip(xs,ys))
check('source_size_centered_loss_identity',sp.expand(original-(syy-2*b*sxy+b*b*sxx+6*(ybar-a-b*xbar)**2))==0)
check('source_group_coefficients',fit([0,0,0,1,1,1],[233,204,242,130,112,142])==(sp.Rational(679,3),sp.Rational(-295,3)))
check('source_age_coefficients',fit([14,23,35,48,52,67],[252,244,240,233,212,204])==(sp.Rational(3087671,11561),sp.Rational(-10519,11561)))
check('reject_empty_pairs',rejects(lambda:fit([],[])))
check('reject_mismatched_pairs',rejects(lambda:fit([0,0,0,1,1,1],[233,204,242])))
check('reject_constant_covariate',rejects(lambda:fit([0,0,0],[233,204,242])))
source_loss=sum((y-a-b*x)**2 for x,y in zip([0,0,0,1,1,1],[233,204,242,130,112,142]))
source_excess=3*(a-sp.Rational(679,3))**2+3*(a+b-128)**2
check('source_completed_square',sp.expand(source_loss-sp.Rational(3734,3)-source_excess)==0)
check('source_unique_zero_squares',sp.solve([a-sp.Rational(679,3),a+b-128],(a,b))=={a:sp.Rational(679,3),b:sp.Rational(-295,3)})
check('source_excess_nonnegative',source_excess.is_nonnegative)
vu,vv,ve,vw,vf=sp.symbols('vu vv ve vw vf',nonnegative=True)
Sigma=sp.diag(vu,vv,ve,vw,vf)
left=sp.Matrix([[1,1,1,0,0]]);right=sp.Matrix([[1,0,0,1,1]])
check('distribution_free_shared_covariance',(left*Sigma*right.T)[0,0]==vu)
ni=sp.symbols('ni',integer=True,positive=True)
i,j=sp.symbols('i j',integer=True,positive=True)
v=sp.symbols('variance',nonnegative=True)
diagonal_row=sp.Sum(sp.KroneckerDelta(i,j)*v,(i,1,ni)).doit()
row_on_domain=sp.refine(diagonal_row,j<=ni)
check('covariance_row_on_index_domain',row_on_domain==v)
variance_sum=sp.Sum(row_on_domain,(j,1,ni)).doit()
check('distribution_free_mean_variance',sp.simplify(variance_sum/ni**2-v/ni)==0)
check('variance_scaling',sp.expand((sp.Symbol('c',real=True)*sp.Symbol('centered',real=True))**2-sp.Symbol('c',real=True)**2*sp.Symbol('centered',real=True)**2)==0)
report={"backend":"Python/SymPy","checks":len(results),"passed":all(r['passed'] for r in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
