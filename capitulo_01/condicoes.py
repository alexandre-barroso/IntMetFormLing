import json
import sympy as sp

results=[]
def check(identifier,condition,hypotheses):
    results.append({'id':identifier,'hypotheses':hypotheses,'passed':bool(condition)})

def safe_rate(c,n):
    if not isinstance(n,int) or n<0:
        raise ValueError(n)
    return None if n==0 else sp.Rational(120000,n)*c

def safe_mean(values):
    return None if len(values)==0 else sum(values)/sp.Integer(len(values))

n=sp.Symbol('n',integer=True,positive=True)
i=sp.Symbol('i',integer=True)
t=sp.Function('t')
x,y,c=sp.symbols('x y c',real=True)
ynz=sp.Symbol('ynz',real=True,nonzero=True)
q=sp.Symbol('q',real=True)
check('rate_zero',safe_rate(c,0) is None,{'c':'real','N':0})
check('mean_zero',safe_mean(()) is None,{'values':'empty sequence'})
check('rate_defined',sp.cancel(c/n*120000-c*120000/n)==0,{'c':'real','N':'positive integer'})
check('mean_defined',sp.simplify(sp.Sum(t(i)/n,(i,1,n))-sp.Sum(t(i),(i,1,n))/n)==0,{'N':'positive integer','t':'real indexed sequence'})
check('mean_weights',sp.summation(1/n,(i,1,n))==1,{'N':'positive integer'})
check('relative_change_denominator',sp.cancel(((x-ynz)/ynz)*ynz-(x-ynz))==0,{'x':'real','y':'real and nonzero'})
check('ratio_determined',sp.solveset(ynz*q-x,q,domain=sp.S.Reals)==sp.FiniteSet(x/ynz),{'x':'real','y':'real and nonzero'})
check('ratio_zero_no_unique',sp.solveset(0*q,q,domain=sp.S.Reals)==sp.S.Reals,{'numerator':0,'denominator':0})
check('rate_actual_validity',all(isinstance(n,int) and n>0 for n in [168799,4623107,1012985,1009304]),{'N':'published corpus sizes'})
check('rate_actual_values',[safe_rate(c,n) for c,n in [(14,168799),(242,4623107),(180,1012985),(236,1009304)]]==[sp.Rational(1680000,168799),sp.Rational(29040000,4623107),sp.Rational(21600000,1012985),sp.Rational(28320000,1009304)],{'N':'positive published corpus sizes'})
report={'backend':'Python/SymPy','checks':len(results),'passed':all(r['passed'] for r in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
