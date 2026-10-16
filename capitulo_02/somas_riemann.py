import json
import sympy as sp

results=[]
def check(identifier,condition):
    results.append({"id":identifier,"passed":bool(condition)})
a=sp.symbols('a',real=True)
length,delta,epsilon=sp.symbols('length delta epsilon',positive=True)
N,k=sp.symbols('N k',integer=True,positive=True)
grid=lambda k:a+k*length/N
check("grid_start",grid(0)==a)
check("grid_finish",sp.cancel(grid(N)-(a+length))==0)
check("grid_step",sp.cancel(grid(k+1)-grid(k)-length/N)==0)
check("grid_monotone",(length/N).is_positive)
q=sp.symbols('q',positive=True)
check("grid_inside",sp.cancel((grid(N)-grid(k))-(N-k)*length/N)==0)
F0,Fn,Fn1=sp.symbols('F0 Fn Fn1',real=True)
check("partition_integral_base",F0-F0==0)
check("partition_integral_step",sp.expand((Fn-F0)+(Fn1-Fn)-(Fn1-F0))==0)
e0,e1,w0,w1,eta=sp.symbols('e0 e1 w0 w1 eta',positive=True)
check("partition_error_step",sp.expand(eta*w0+eta*w1-eta*(w0+w1))==0)
check("right_sum_widths",sp.summation(length/N,(k,1,N))==length)
check("right_sum_epsilon",sp.cancel((epsilon/(2*length))*length-epsilon/2)==0)
excess=sp.symbols('excess',positive=True)
check("right_sum_mesh",sp.simplify(delta-length/(length/delta+excess)).is_positive)
t=sp.symbols('t',real=True)
f,w=sp.Function('f'),sp.Function('w')
right_sum=sp.Sum(f(grid(k))*length/N,(k,1,N))
weighted_sum=sp.Sum(w(grid(k))*f(grid(k))*length/N,(k,1,N))
check("right_sum_definition",right_sum.limits==((k,1,N),) and right_sum.function==f(a+k*length/N)*length/N)
check("weighted_right_sum_definition",weighted_sum.function==w(a+k*length/N)*f(a+k*length/N)*length/N)
theta,phi=sp.symbols('theta phi',real=True)
cell_left=grid(k)
tag=cell_left+theta*length/N
point=cell_left+phi*length/N
check("tagged_cell_lower",sp.expand(tag-cell_left-theta*length/N)==0)
check("tagged_cell_upper",sp.expand(grid(k+1)-tag-(1-theta)*length/N)==0)
check("tagged_distance_upper",sp.minimum(sp.minimum(1-(theta-phi),theta,sp.Interval(0,1)),phi,sp.Interval(0,1))==0)
check("tagged_distance_lower",sp.minimum(sp.minimum(1+(theta-phi),theta,sp.Interval(0,1)),phi,sp.Interval(0,1))==0)
check("tagged_cell_scaling",sp.expand((tag-point)-(theta-phi)*length/N)==0)
report={"backend":"Python/SymPy","checks":len(results),"passed":all(r['passed'] for r in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
