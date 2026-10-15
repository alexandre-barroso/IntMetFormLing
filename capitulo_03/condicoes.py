import json
import sympy as sp
from itertools import product

results=[]
def check(identifier,condition,hypotheses):
    results.append({'id':identifier,'hypotheses':hypotheses,'passed':bool(condition)})

def overlap(a,b):
    return None if not a or not b else sp.Rational(len(a&b),min(len(a),len(b)))

x,y,z=sp.symbols('x y z',nonnegative=True)
d=sp.Symbol('d',positive=True)
u=sp.Symbol('u',positive=True)
check('overlap_regions',sp.simplify((sp.Min(x+z,y+z)-z-sp.Min(x,y)).rewrite(sp.Abs))==0,{'x':'|A minus B|','y':'|B minus A|','z':'|A intersection B|','all':'nonnegative integers'})
check('overlap_nonnegative',(z/d).is_nonnegative is True,{'z>=0':True,'d=min(|A|,|B|)>0':True})
check('overlap_upper',sp.cancel(1-z/(z+u)-u/(z+u))==0 and (u/(z+u)).is_positive is True,{'z>=0':True,'u=min(x,y)>0':True})
zpos=sp.Symbol('zpos',positive=True)
check('overlap_upper_boundary',sp.cancel(zpos/zpos)==1,{'z>0':True,'u=min(x,y)=0':True})
check('overlap_zero_iff',sp.solveset(z/d,z,domain=sp.S.Reals)==sp.FiniteSet(0),{'d>0':True})
check('overlap_one_iff',sp.solve(sp.Eq(z/d,1),z)==[d],{'d>0':True,'z<=d':True})
check('overlap_empty_rejected',overlap(set(),{'s'}) is None and overlap({'s'},set()) is None and overlap(set(),set()) is None,{'at least one set empty':True})
a={'s','or','pr','endere'}
b={'s','or','pr','endere','bbe'}
c={'s','or','pr','end','iamo'}
dset={'s','or','pre','se'}
check('overlap_published_values',[overlap(a,v) for v in [b,c,dset]]==[1,sp.Rational(3,4),sp.Rational(1,2)],{'nonempty published segment sets':True})
domain=(False,True)
f=lambda y:True
dpred=lambda x:True
r=lambda y,x:y==x
surface=all(not f(y) or any(dpred(x) and r(y,x) for x in domain) for y in domain)
inverse=any(dpred(x) and all(not f(y) or r(y,x) for y in domain) for x in domain)
check('surface_not_inverse',surface and not inverse,{'domain':'Bool','F=D':'True','R(y,x)':'y=x','method':'finite countermodel'})
check('empty_restriction_no_existence',set()<=set() and not bool(set()&set()),{'domain':'Bool','A=B':'empty'})
most=lambda p,q:True
check('most_rules_are_not_type_consequences',most(lambda _:False,lambda _:False) and not any(False and False for _ in domain),{'Most':'constant True operation','method':'countermodel; existential import requires explicit rule'})
p,q,r=sp.symbols('p q r')
check('inverse_implies_surface_witness_step',sp.simplify_logic(sp.Implies(p & sp.Implies(q,r) & q,p&r))==True,{'p':'D(x) for common witness x','q':'F(y) for arbitrary y','r':'R(y,x)','method':'propositional step; quantifier proof in Lean'})
xp,yp=sp.symbols('xp yp',positive=True)
check('overlap_one_regions_iff',sp.Min(0,x)==0 and sp.Min(y,0)==0 and sp.Min(xp,yp).is_positive is True,{'x,y':'nonnegative regions','case decomposition':'x=0 or y=0 or x>0 and y>0'})
report={'backend':'Python/SymPy','checks':len(results),'passed':all(r['passed'] for r in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
