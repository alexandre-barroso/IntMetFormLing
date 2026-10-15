import json
import sympy as sp

results=[]
def check(identifier,condition,hypotheses):
    results.append({'id':identifier,'hypotheses':hypotheses,'passed':bool(condition)})

def finite_slope(m,l1,l2):
    return None if l2==l1 else sp.cancel((m*l2-m*l1)/(l2-l1))

def linear_increment(m,l,h):
    return None if h==0 else sp.cancel((m*(l+h)-m*l)/h)

def reciprocal_increment(u,h):
    return None if u==0 or h==0 or u+h==0 else sp.cancel((1/(u+h)-1/u)/h)

m,l=sp.symbols('m l',real=True)
h,u,v=sp.symbols('h u v',real=True,nonzero=True)
check('finite_slope_valid',finite_slope(m,l,l+h)==m,{'m,L1':'real','L2-L1':'nonzero real h'})
check('finite_slope_reject_zero',finite_slope(m,l,l) is None,{'L2=L1':True})
check('linear_increment_valid',linear_increment(m,l,h)==m,{'m,L':'real','h':'nonzero real'})
check('linear_increment_reject_zero',linear_increment(m,l,0) is None,{'h':0})
check('reciprocal_increment_algebra',sp.cancel((1/v-1/u)/(v-u)+1/(u*v))==0,{'u':'nonzero real','v=u+h':'nonzero real','h=v-u':'nonzero'})
check('reciprocal_increment_reject_u_zero',reciprocal_increment(0,h) is None,{'u':0})
check('reciprocal_increment_reject_h_zero',reciprocal_increment(u,0) is None,{'h':0})
check('reciprocal_increment_reject_u_plus_h_zero',reciprocal_increment(u,-u) is None,{'u+h':0})
check('reciprocal_derivative_domain',sp.calculus.util.continuous_domain(1/u,u,sp.S.Reals)==sp.Complement(sp.S.Reals,sp.FiniteSet(0)),{'derivative domain':'R minus {0}'})
check('reciprocal_derivative',sp.diff(1/u,u)==-1/u**2,{'u':'nonzero real'})
x=sp.Symbol('x',real=True)
xpos=sp.Symbol('xpos',positive=True)
check('logarithm_real_domain',sp.calculus.util.continuous_domain(sp.log(x),x,sp.S.Reals)==sp.Interval.open(0,sp.oo),{'real logarithm':'x>0'})
check('logarithm_inverse_domain',sp.exp(sp.log(xpos))==xpos,{'x':'positive real'})
b,a=sp.symbols('b a',real=True)
n=sp.Symbol('n',positive=True,integer=True)
k=sp.Symbol('k',integer=True)
check('grid_domain_integer_positive',n.is_integer is True and n.is_positive is True,{'N':'positive integer'})
check('grid_inside_lower',sp.cancel((a+k*(b-a)/n-a)-k*(b-a)/n)==0,{'a<=b':True,'0<=k<=N':True,'N':'positive integer'})
check('grid_inside_upper',sp.cancel((b-a-k*(b-a)/n)-(n-k)*(b-a)/n)==0,{'a<=b':True,'0<=k<=N':True,'N':'positive integer'})
bn=sp.Symbol('bn',real=True)
cn,nn=sp.symbols('cn nn',real=True,nonzero=True)
check('stationary_equivalence',sp.solveset(bn/nn-cn,bn,domain=sp.S.Reals)==sp.FiniteSet(cn*nn) and sp.solveset(nn-bn/cn,bn,domain=sp.S.Reals)==sp.FiniteSet(cn*nn),{'b':'real','c,n':'nonzero real'})
up=sp.Symbol('up',positive=True)
hr=sp.Symbol('hr',real=True)
check('reciprocal_limit',sp.limit((1/(up+hr)-1/up)/hr,hr,0)==-1/up**2,{'u>0':True,'h tends to zero':'punctured neighborhood'})
aa,nn=sp.symbols('aa nn',positive=True)
bb,cc=sp.symbols('bb cc',real=True)
log_steps=[sp.log(aa*nn**bb*sp.exp(-cc*nn)),sp.log(aa)+sp.log(nn**bb)+sp.log(sp.exp(-cc*nn)),sp.log(aa)+bb*sp.log(nn)-cc*nn]
check('logarithm_mal_chain',all(sp.simplify(sp.expand_log(left-right))==0 for left,right in zip(log_steps,log_steps[1:])),{'a,n':'positive real','b,c':'real'})
tt=sp.Symbol('tt',real=True)
end=sp.Symbol('end',positive=True)
scale=sp.Symbol('scale',real=True)
wfun,ffun=sp.Function('w'),sp.Function('f')
check('integral_product_scaling',sp.Integral((scale*wfun(tt))*ffun(tt),(tt,0,end)).doit()==scale*sp.Integral(wfun(tt)*ffun(tt),(tt,0,end)).doit(),{'T>0':True,'c':'real constant','w,f':'continuous on [0,T]'})
check('integral_square_scaling',sp.Integral((scale*wfun(tt))**2,(tt,0,end)).doit()==scale**2*sp.Integral(wfun(tt)**2,(tt,0,end)).doit(),{'T>0':True,'c':'real constant','w':'continuous on [0,T]'})
yfun=sp.Function('y')
argument=sp.Symbol('argument',real=True)
check('chain_reciprocal',sp.diff(1/yfun(argument),argument)==-sp.diff(yfun(argument),argument)/yfun(argument)**2,{'y differentiable at n':True,'y(n)!=0':True})
uu,vv=sp.symbols('uu vv',real=True)
check('logarithm_powers_sum',sp.simplify(sp.expand_log(sp.log(2**uu*2**vv,2))-uu-vv)==0 and sp.simplify(sp.log(2**uu,2)+sp.log(2**vv,2)-uu-vv)==0,{'u,v':'real','x=2^u and y=2^v':True})
la,lc,lr,alpha=sp.symbols('la lc lr alpha',real=True)
lam=sp.Symbol('lam',real=True,nonzero=True)
ell=(alpha*lr+la-lc)/lam
check('composition_rearrangement_steps',all(sp.cancel(v)==0 for v in [-lam*ell-(lc-la-alpha*lr),lam*ell-(alpha*lr+la-lc),ell-alpha*lr/lam-(la-lc)/lam]),{'a-lnA,c-lnC,r-lnr':'real values of logarithms','lambda':'nonzero real','ell':'solution previously derived from log equality'})
report={'backend':'Python/SymPy','checks':len(results),'passed':all(r['passed'] for r in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
