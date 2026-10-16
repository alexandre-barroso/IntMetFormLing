import json
import sympy as sp
Q=sp.Rational
results=[]
def check(identity,condition):
    results.append({'id':identity,'passed':bool(condition)})
rows=['100100000','101000000','110000000','011010000','011200000','010010000','010010000','001100000','010000001','000001110','000000111','000000011']
M=sp.Matrix([[int(value) for value in row] for row in rows])
G=M.T*M
x=sp.symbols('x',real=True)
p=sp.Poly(x**9-31*x**8+374*x**7-2286*x**6+7697*x**5-14557*x**4+15014*x**3-7755*x**2+1732*x-124,x)
check('characteristic_from_source',G.charpoly(x).as_expr().subs(G.charpoly(x).gen,x)==p.as_expr())
check('symmetric_gram',G==G.T)
check('positive_definite_gram',G.is_positive_definite is True)
published=list(map(Q,['3.34','2.54','2.35','1.64','1.50','1.31','0.85','0.56','0.36']))
intervals=[((v-Q(1,200))**2,(v+Q(1,200))**2) for v in published]
check('sign_changes',all(p.eval(a)*p.eval(b)<0 for a,b in intervals))
check('intervals_disjoint',all(b1<a2 or b2<a1 for i,(a1,b1) in enumerate(intervals) for a2,b2 in intervals[i+1:]))
check('exact_root_count',p.degree()==9 and sum(p.count_roots(a,b) for a,b in intervals)==9 and all(p.count_roots(a,b)==1 for a,b in intervals))
check('no_other_roots',p.count_roots(-sp.oo,sp.oo)==9 and p.count_roots(0,sp.oo)==9)
check('singular_value_intervals',all(a>0 and sp.sqrt(a)==v-Q(1,200) and sp.sqrt(b)==v+Q(1,200) for v,(a,b) in zip(published,intervals)))
U=sp.MatrixSymbol('U',12,2)
V=sp.MatrixSymbol('V',9,2)
s0,s1=sp.symbols('sigma0 sigma1',positive=True)
S=sp.diag(s0,s1)
check('reconstruction_coordinate',(U*S*V.T)[0,0]==U[0,0]*s0*V[0,0]+U[0,1]*s1*V[0,1])
check('published_diagonal_inverse',sp.diag(Q(100,334),Q(100,254))*sp.diag(Q(334,100),Q(254,100))==sp.eye(2))
check('rank_two_diagonal',sp.diag(s0,s1).rank()==2)
a00,a01,a10,a11,b00,b01,b10,b11=sp.symbols('a00 a01 a10 a11 b00 b01 b10 b11',real=True)
gram_u=sp.Matrix([[a00,a01],[a10,a11]])
gram_v=sp.Matrix([[b00,b01],[b10,b11]])
orthonormal={a00:1,a01:0,a10:0,a11:1,b00:1,b01:0,b10:0,b11:1}
left_inverse_certificate=sp.diag(1/s0,1/s1)*gram_u*S*gram_v
check('rank_two_left_inverse_under_orthonormality',left_inverse_certificate.subs(orthonormal)==sp.eye(2))
check('positive_singular_values_nonzero',s0.is_positive is True and s1.is_positive is True and sp.det(S).is_positive is True)
zero_u=sp.zeros(12,2)
check('rank_two_requires_column_independence',(zero_u*S*V.T).as_explicit().rank()==0)
check('source_singular_values_complete',G==M.T*M and sp.Poly((x*sp.eye(9)-G).det(),x)==p and all(a>0 and p.count_roots(a,b)==1 for a,b in intervals) and sum(p.count_roots(a,b) for a,b in intervals)==9 and p.count_roots(-sp.oo,sp.oo)==9)
report={'backend':'Python/SymPy','checks':len(results),'passed':all(r['passed'] for r in results),'results':results}
print(json.dumps(report))
raise SystemExit(0 if report['passed'] else 1)
