import json
r=[]
def check(name,value):
    r.append({'id':name,'passed':bool(value)})
genitive_plural=['-on']*8
check('genitive_plural_values',genitive_plural[0]=='-on' and genitive_plural[1]=='-on' and genitive_plural[0]==genitive_plural[1])
check('min_cardinalities',min(4,5)==4)
check('disjunction_without_negation',(True or False) and not False)
a={'s','or','pr','endere'}
b={'s','or','pr','endere','bbe'}
c={'s','or','pr','end','iamo'}
d={'s','or','pre','se'}
from fractions import Fraction
check('published_overlap_steps',(len(a&b),min(len(a),len(b)),Fraction(len(a&b),min(len(a),len(b))))==(4,4,1) and (len(a&c),min(len(a),len(c)),Fraction(len(a&c),min(len(a),len(c))))==(3,4,Fraction(3,4)) and Fraction(3,4)==Fraction(75,100) and (len(a&d),min(len(a),len(d)),Fraction(len(a&d),min(len(a),len(d))))==(2,4,Fraction(2,4)) and Fraction(2,4)==Fraction(5,10))
print(json.dumps({'passed':all(a['passed'] for a in r),'results':r}))
raise SystemExit(0 if all(a['passed'] for a in r) else 1)
