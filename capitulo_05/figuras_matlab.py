from fractions import Fraction as Q
from itertools import accumulate
import json

results=[]
def check(name,condition):
    results.append({'id':name,'passed':bool(condition)})
s=(Q(4,10),Q(3,10),Q(3,10));o=(Q(6,10),Q(2,10),Q(2,10))
d=tuple(a-b for a,b in zip(o,s));dp=sum(map(abs,d))/2
check('F06_distributions',sum(s)==sum(o)==1 and all(x>0 for x in (*s,*o)))
check('F06_differences',d==(Q(1,5),Q(-1,10),Q(-1,10)))
check('F06_balanced_excess',sum(d)==0 and sum(x for x in d if x>0)==-sum(x for x in d if x<0)==Q(1,5))
check('F06_dp',dp==Q(1,5))
check('F06_minimum',min(s)==Q(3,10))
check('F06_normalized',dp/(1-min(s))==Q(2,7))
check('F06_material_percentages',tuple(100*x for x in s)==(40,30,30))
check('F06_occurrence_percentages',tuple(100*x for x in o)==(60,20,20))
check('F06_band_boundaries',tuple(accumulate((Q(0),*s)))==(0,Q(2,5),Q(7,10),1) and tuple(accumulate((Q(0),*o)))==(0,Q(3,5),Q(4,5),1))
report={'backend':'Python/exact rational','checks':len(results),'passed':all(x['passed'] for x in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
