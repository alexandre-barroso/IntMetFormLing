import json
from fractions import Fraction as Q
from collections import Counter
import sympy as s

results=[]
def check(name,condition):
    results.append({'id':name,'passed':bool(condition)})
acc=('us','es','es','is','a','a','i','a')
gen=('u','zero','s','s','u','u','us','os')
origins=('us','es','is','a','i')
groups=[tuple(i+1 for i,a in enumerate(acc) if a==x) for x in origins]
weights=[Q(len(g),8) for g in groups]
counts=[Counter(gen[i-1] for i in g) for g in groups]
probs=[{k:Q(v,len(g)) for k,v in c.items()} for c,g in zip(counts,groups)]
check('F07_class_partition',groups==[(1,),(2,3),(4,),(5,6,8),(7,)] and sorted(sum(groups,()))==list(range(1,9)))
check('F07_group_weights',weights==[Q(1,8),Q(2,8),Q(1,8),Q(3,8),Q(1,8)] and sum(weights)==1)
check('F07_conditional_edges',probs==[{'u':Q(1)},{'zero':Q(1,2),'s':Q(1,2)},{'s':Q(1)},{'u':Q(2,3),'os':Q(1,3)},{'us':Q(1)}])
def entropy(p):
    return s.simplify(-sum(s.Rational(x.numerator,x.denominator)*s.log(s.Rational(x.numerator,x.denominator),2) for x in p if x))
h=[entropy(p.values()) for p in probs]
check('F07_group_entropies',all(s.simplify(x-y)==0 for x,y in zip(h,[0,1,0,s.log(3,2)-s.Rational(2,3),0])))
conditional=s.simplify(sum(s.Rational(w.numerator,w.denominator)*v for w,v in zip(weights,h)))
initial=entropy(Q(v,8) for v in Counter(gen).values())
check('F07_conditional_entropy',s.simplify(conditional-s.Rational(3,8)*s.log(3,2))==0)
check('F07_initial_entropy',s.simplify(initial-(s.Rational(11,4)-s.Rational(3,8)*s.log(3,2)))==0)
check('F07_decimals',s.Rational(9175,10000)<h[3]<s.Rational(9185,10000) and s.Rational(5935,10000)<conditional<s.Rational(5945,10000) and s.Rational(21555,10000)<initial<s.Rational(21565,10000))
check('F07_unweighted_mean_rejected',s.simplify(sum(h)/5-conditional)!=0)
report={'backend':'Python/SymPy','checks':len(results),'passed':all(x['passed'] for x in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
