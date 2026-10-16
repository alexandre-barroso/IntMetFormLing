import json
from itertools import product

checks=[]
def check(name, proposition):
    if not proposition:
        raise AssertionError(name)
    checks.append({"id":name,"passed":True})

def readings(relation):
    return (all(any(row) for row in relation), any(all(row[j] for row in relation) for j in range(len(relation[0]))))

left=[[i==j for j in range(3)] for i in range(3)]
right=[[True] for _ in range(3)]
check("figure_F03_left",readings(left)==(True,False))
check("figure_F03_right",readings(right)==(True,True))
check("figure_F03_exact_left_edges",[(i+1,j+1) for i,row in enumerate(left) for j,v in enumerate(row) if v]==[(1,1),(2,2),(3,3)])
check("figure_F03_exact_right_edges",[(i+1,j+1) for i,row in enumerate(right) for j,v in enumerate(row) if v]==[(1,1),(2,1),(3,1)])
relations=[list(map(list,(bits[:3],bits[3:6],bits[6:]))) for bits in product((False,True),repeat=9)]
check("figure_F03_all_512_relations",len(relations)==512 and all(not readings(R)[1] or readings(R)[0] for R in relations))
classes=tuple(range(1,9))
outputs={c:"on" for c in classes}
check("genitive_plural_not_invertible",all(any(preimage!=c for c in classes) for preimage in classes) and len(set(outputs.values()))==1)
M={False};H={False,True};P={False}
check("widening_restriction_countermodel",M<=H and M<=P and not H<=P)
print(json.dumps({"backend":"Python 3","scope":"exact finite models displayed in F03; exhaustive 512 relations as finite check, not general quantifier theorem; paradigm inverse obstruction", "checks":len(checks),"passed":True,"results":checks}))
