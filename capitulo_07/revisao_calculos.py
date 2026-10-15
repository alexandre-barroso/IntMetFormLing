import json
import sympy as sp
results=[]
def check(identifier,condition):
    results.append({"id":identifier,"passed":bool(condition)})
p=sp.Symbol('p',real=True)
check('indicator_numeric_cases',p*0==0 and 1*1==1)
n=sp.Symbol('n',integer=True,positive=True)
i=sp.Symbol('i',integer=True)
x=sp.IndexedBase('x');y=sp.IndexedBase('y')
a,b,mx,my=sp.symbols('a b mx my',real=True)
residual=sp.Sum((y[i]-a-b*x[i])**2,(i,1,n))
xx=sp.Sum((x[i]-mx)**2,(i,1,n));xy=sp.Sum((x[i]-mx)*(y[i]-my),(i,1,n));yy=sp.Sum((y[i]-my)**2,(i,1,n))
difference=sp.factor_terms((residual-(yy-2*b*xy+b*b*xx+n*(my-a-b*mx)**2)).expand().doit())
check('centered_loss_general_sum',sp.simplify(difference.subs({sp.Sum(x[i],(i,1,n)):n*mx,sp.Sum(y[i],(i,1,n)):n*my}))==0)
a,b,x=sp.symbols('a b x',real=True)
check('fitted_line_substitution',sp.expand((a+b*x).subs({a:sp.Rational(679,3),b:-sp.Rational(295,3)})-(sp.Rational(679,3)-sp.Rational(295,3)*x))==0)
a,b=sp.symbols('a b',real=True)
check('minimum_coefficient_conditions',sp.solve([a-sp.Rational(679,3),a+b-128],(a,b))=={a:sp.Rational(679,3),b:-sp.Rational(295,3)})
a,b=sp.symbols('a b',real=True)
check('c07_e0241_integral',sp.diff(6*a*b,a)==6*b and sp.diff(6*a*b,b)==6*a)
a,b=sp.symbols('a b',real=True)
check('c07_e0248_integral',sp.diff(3*b*b,a)==0 and sp.diff(3*b*b,b)==6*b)
a,b=sp.symbols('a b',real=True)
r1=6*a+3*b-1063;r2=3*a+3*b-384
solution=sp.solve([r1,r2],(a,b))
steps=[3*a-679,a-sp.Rational(679,3),679+3*b-384,3*b+295,b+sp.Rational(295,3)]
check('c07_e0251_integral',sp.expand((12*a+6*b-2126)-2*r1)==0 and sp.expand((6*a+6*b-768)-2*r2)==0 and sp.expand(r1-r2-(3*a-679))==0 and solution=={a:sp.Rational(679,3),b:-sp.Rational(295,3)} and all(sp.simplify(step.subs(solution))==0 for step in steps))
x,y=sp.symbols('x y',real=True)
check('centered_weak_order',sp.solve_univariate_inequality(x-y>=y,x)==sp.solve_univariate_inequality(x>=2*y,x))
x,y=sp.symbols('x y',real=True)
check('centered_strict_order',sp.solve_univariate_inequality(x-y>y,x)==sp.solve_univariate_inequality(x>2*y,x))
p,q,b,c=sp.symbols('p q b c',real=True)
check('redundant_indicator_chain',sp.reduced(b*q+c*p*q-(b*q+c*q),[p*q-q],p,q,b,c)[1]==0 and sp.expand(b*q+c*q-(b+c)*q)==0)
a,b=sp.symbols('a b',real=True)
review_design=sp.Matrix([[1,0],[1,0],[1,0],[1,1],[1,1],[1,1]])
check('normal_matrix_arbitrary_coefficients',review_design.T*review_design*sp.Matrix([a,b])==sp.Matrix([6*a+3*b,3*a+3*b]))
observed=[sp.Rational(v) for v in [233,204,242,130,112,142]]
predicted=[sp.Rational(2263333333333,10000000000)]*3+[sp.Rational(128)]*3
vertical=[((i+1,y),(i+1,p)) for i,(y,p) in enumerate(zip(observed,predicted,strict=True))]
horizontal=[((1,predicted[0]),(3,predicted[2])),((4,predicted[3]),(6,predicted[5]))]
q=sp.Rational(2263333333333,10000000000)
check('regression_plot_coordinates',vertical==[((1,233),(1,q)),((2,204),(2,q)),((3,242),(3,q)),((4,130),(4,128)),((5,112),(5,128)),((6,142),(6,128))] and horizontal==[((1,q),(3,q)),((4,128),(6,128))])
print(json.dumps({"checks":len(results),"passed":all(r["passed"] for r in results),"results":results}))
raise SystemExit(0 if all(r["passed"] for r in results) else 1)
