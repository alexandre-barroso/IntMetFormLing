from fractions import Fraction as Q
from math import factorial
import json
import sympy as s

results=[]
def check(name,condition):
    results.append({'id':name,'passed':bool(condition)})
def log_unit(x,n=24):
    if not 1<=x<=2 or n<1:raise ValueError((x,n))
    z=(x-1)/(x+1)
    v=2*sum((z**(2*k+1)/Q(2*k+1) for k in range(n)),Q(0))
    return v,v+2*z**(2*n+1)/(1-z*z)
def log_bounds(x):
    if x<=0:raise ValueError(x)
    k=0
    while x<1:x*=2;k-=1
    while x>2:x/=2;k+=1
    a,b=log_unit(x);c,d=log_unit(Q(2))
    return (a+k*d,b+k*c) if k<0 else (a+k*c,b+k*d)
def coarse(bounds,n=10):
    a,b=bounds;d=10**n
    return Q(a.numerator*d//a.denominator,d),Q(-((-b.numerator*d)//b.denominator),d)
def exp_bound(x,n=16):
    if abs(x)>1 or n<1:raise ValueError((x,n))
    v=sum((x**k/Q(factorial(k)) for k in range(n)),Q(0))
    error=abs(x)**n*Q(n+1,factorial(n)*n)
    return v-error,v+error
def atan_bound(x,n=20):
    if not 0<=x<1:raise ValueError(x)
    a=sum(((-1)**k*x**(2*k+1)/Q(2*k+1) for k in range(n)),Q(0))
    b=a+(-1)**n*x**(2*n+1)/Q(2*n+1)
    return min(a,b),max(a,b)
a5,b5=atan_bound(Q(1,5));a239,b239=atan_bound(Q(1,239))
pi=(16*a5-4*b239,16*b5-4*a239)
sqrtpi=(Q('2.50662827463100'),Q('2.50662827463101'))
check('F02_sqrt_two_pi_interval',sqrtpi[0]**2<2*pi[0]<2*pi[1]<sqrtpi[1]**2)
def density_bounds(t):
    if t<=0:raise ValueError(t)
    l,h=coarse(log_bounds(t));l+=Q('2.68');h+=Q('2.68')
    square=(Q(0) if l<=0<=h else min(l*l,h*h),max(l*l,h*h))
    e=coarse((-square[1]/(2*Q('.59')**2),-square[0]/(2*Q('.59')**2)))
    return exp_bound(e[0])[0]/(t*Q('.59')*sqrtpi[1]),exp_bound(e[1])[1]/(t*Q('.59')*sqrtpi[0])
def integral_polynomial(a,b,n=12):
    return sum((Q(-1,2)**k/Q(factorial(k))*(b**(2*k+1)-a**(2*k+1))/Q(2*k+1) for k in range(n)),Q(0))
za=tuple((z+Q('2.68'))/Q('.59') for z in log_bounds(Q('.03')))
zb=tuple((z+Q('2.68'))/Q('.59') for z in log_bounds(Q('.14')))
outer=(Q('-1.400945589'),Q('1.209978210'))
inner=(Q('-1.400945588'),Q('1.209978209'))
check('F02_transformed_limits',outer[0]<za[0]<za[1]<inner[0]<inner[1]<zb[0]<zb[1]<outer[1])
epsilon=Q(13,12*factorial(12))
lower=(integral_polynomial(*inner)-(inner[1]-inner[0])*epsilon)/sqrtpi[1]
upper=(integral_polynomial(*outer)+(outer[1]-outer[0])*epsilon)/sqrtpi[0]
check('F02_interval_domain',all(abs(z)<=Q('1.41') for z in (*outer,*inner)) and Q('1.41')**2/2<1)
check('F02_area_rounding',Q('.8062405')<lower<upper<Q('.8062415'))
check('F02_empirical_eighty_percent_distinct',lower>Q('.8'))
x=s.symbols('x',real=True)
poly=sum(s.Rational(-1,2)**k/s.factorial(k)*x**(2*k) for k in range(12))
primitive=sum(s.Rational(-1,2)**k/s.factorial(k)*x**(2*k+1)/s.Integer(2*k+1) for k in range(12))
check('F02_polynomial_antiderivative',s.expand(s.diff(primitive,x)-poly)==0)
check('F02_polynomial_matches_exponential_terms',s.expand(poly-sum((-x*x/2)**k/s.factorial(k) for k in range(12)))==0)
a,b,N,j=s.symbols('a b N j',real=True,nonzero=True)
grid=a+j*(b-a)/N
check('F02_grid_endpoints',s.cancel(grid.subs(j,0)-a)==0 and s.cancel(grid.subs(j,N)-b)==0)
check('F02_grid_step',s.cancel(grid.subs(j,j+1)-grid-(b-a)/N)==0)
intervals={}
partitions={}
for n,v in [(4,Q('.6941')),(8,Q('.7572')),(32,Q('.7953'))]:
    step=Q('.11')/n
    points=[Q('.03')+j*step for j in range(1,n+1)]
    heights=[density_bounds(t) for t in points]
    bounds=tuple(step*sum(h[i] for h in heights) for i in [0,1])
    intervals[n]=bounds
    partitions[n]=points[-1]==Q('.14') and len(points)==n and all(Q('.03')<t<=Q('.14') for t in points)
check('F02_right_sum_4',Q('.6941')-Q('.00005')<intervals[4][0]<intervals[4][1]<Q('.6941')+Q('.00005'))
check('F02_partition_4',partitions[4])
check('F02_right_sum_8',Q('.7572')-Q('.00005')<intervals[8][0]<intervals[8][1]<Q('.7572')+Q('.00005'))
check('F02_partition_8',partitions[8])
check('F02_right_sum_32',Q('.7953')-Q('.00005')<intervals[32][0]<intervals[32][1]<Q('.7953')+Q('.00005'))
check('F02_partition_32',partitions[32])
check('F02_displayed_errors_decrease',intervals[4][1]<intervals[8][0]<intervals[8][1]<intervals[32][0]<intervals[32][1]<lower)
report={'backend':'Python/exact interval certificates','checks':len(results),'passed':all(x['passed'] for x in results),'area_interval':[str(lower),str(upper)],'right_sum_intervals':{str(k):[str(x) for x in v] for k,v in intervals.items()},'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
