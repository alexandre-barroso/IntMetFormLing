import json
import sympy as s
from itertools import product

results=[]
def check(name,condition):
    results.append({'id':name,'passed':bool(condition)})
profiles=s.Matrix([[442,8,2],[5,1683,1670],[5,3982,3325]])
norms=[s.sqrt(sum(v*v for v in profiles.row(i))) for i in range(3)]
units=[profiles.row(i)/norms[i] for i in range(3)]
check('F04_full_source_table',list(profiles)==[442,8,2,5,1683,1670,5,3982,3325])
check('F04_all_norms_positive',all(n>0 for n in norms))
check('F04_all_units',all(s.simplify(v.dot(v))==1 for v in units))
c1=s.simplify(units[0].dot(units[2]));c2=s.simplify(units[1].dot(units[2]))
check('F04_exact_cosseno_cherry',c1==40716/s.sqrt(195432*26911974))
check('F04_exact_cosseno_digital',c2==12254481/s.sqrt(5621414*26911974))
check('F04_cossenos_rounding',s.Rational(175,10000)<c1<s.Rational(185,10000) and s.Rational(9955,10000)<c2<s.Rational(9965,10000))
check('F04_directions_preserved',all(s.simplify(units[i][j]*norms[i]-profiles[i,j])==0 for i,j in product(range(3),repeat=2)))
own=s.Matrix([[40,s.Rational('85.3'),s.Rational('3.2')],[s.Rational('16.7'),s.Rational('73.4'),8],[s.Rational('5.2'),s.Rational('9.3'),s.Rational('48.4')]])
use=s.Matrix([[s.Rational('82.1'),s.Rational('44.8'),s.Rational('3.3')],[s.Rational('69.5'),s.Rational('51.9'),s.Rational('10.1')],[7,s.Rational('4.7'),s.Rational('53.6')]])
tensor={(i,j,k):[own,use][j][i,k] for i,j,k in product(range(3),range(2),range(3))}
columns={(j,k):2*k+j for j,k in product(range(2),range(3))}
matrix=s.Matrix(3,6,lambda i,c:tensor[i,c%2,c//2])
check('F05_column_bijection',set(columns.values())==set(range(6)) and len(columns)==6)
check('F05_all_18_entries',all(matrix[i,columns[j,k]]==tensor[i,j,k] for i,j,k in tensor))
check('F05_full_matrix',matrix==s.Matrix([[40,s.Rational('82.1'),s.Rational('85.3'),s.Rational('44.8'),s.Rational('3.2'),s.Rational('3.3')],[s.Rational('16.7'),s.Rational('69.5'),s.Rational('73.4'),s.Rational('51.9'),8,s.Rational('10.1')],[s.Rational('5.2'),7,s.Rational('9.3'),s.Rational('4.7'),s.Rational('48.4'),s.Rational('53.6')]]))
check('F05_highlighted_entry',tensor[2,1,2]==matrix[2,5]==s.Rational('53.6'))
check('F05_workshop_entry',tensor[0,1,1]==matrix[0,3]==s.Rational('44.8'))
a,e=s.symbols('a e',real=True)
projection=s.Matrix([[s.cos(a),-s.sin(a),0],[s.sin(a)*s.sin(e),s.cos(a)*s.sin(e),s.cos(e)]])
check('F05_orthographic_projection',s.simplify(projection*projection.T)==s.eye(2))
report={'backend':'Python/SymPy','checks':len(results),'passed':all(x['passed'] for x in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
