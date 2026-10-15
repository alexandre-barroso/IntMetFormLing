import json
import sympy as sp

results=[]
def check(name,condition):
    if condition is not True:
        raise AssertionError((name,condition))
    results.append({'id':name,'passed':True})

rows=['100100000','101000000','110000000','011010000','011200000','010010000','010010000','001100000','010000001','000001110','000000111','000000011']
M=sp.Matrix([[int(value) for value in row] for row in rows])
G=M.T*M
x,y=sp.symbols('x y',real=True)
p=sp.Poly(x**9-31*x**8+374*x**7-2286*x**6+7697*x**5-14557*x**4+15014*x**3-7755*x**2+1732*x-124,x)
check('svd_source_gram_and_characteristic',G==G.T and sp.Poly(G.charpoly(x).as_expr().subs(G.charpoly(x).gen,x),x)==p)
published=list(map(sp.Rational,['3.34','2.54','2.35','1.64','1.50','1.31','0.85','0.56','0.36']))
intervals=sorted([((s-sp.Rational(1,200))**2,(s+sp.Rational(1,200))**2) for s in published])
check('svd_nine_distinct_positive_roots',p.degree()==9 and sp.gcd(p,p.diff()).degree()==0 and all(a>0 and p.eval(a)*p.eval(b)<0 and p.count_roots(a,b)==1 for a,b in intervals) and all(intervals[i][1]<intervals[i+1][0] for i in range(8)) and p.count_roots(-sp.oo,sp.oo)==9)
eigenvalues=tuple(sp.CRootOf(p.as_expr(),i) for i in range(9))
coefficients=p.all_coeffs()
blocks=[sp.eye(9)]
for k in range(1,9):
    blocks.append(G*blocks[-1]+coefficients[k]*sp.eye(9))
adjugate=sum((blocks[k]*x**(8-k) for k in range(9)),sp.zeros(9))
check('svd_polynomial_adjugate',((x*sp.eye(9)-G)*adjugate-p.as_expr()*sp.eye(9)).applyfunc(sp.expand)==sp.zeros(9))
w=adjugate[:,0]
e0=sp.eye(9)[:,0]
check('svd_polynomial_eigenvectors',(G*w-x*w+p.as_expr()*e0).applyfunc(sp.expand)==sp.zeros(9,1))
u,v,gcd=sp.gcdex(p,sp.Poly(w[0],x))
check('svd_eigenvector_never_zero',gcd.as_expr()==1 and sp.expand(u.as_expr()*p.as_expr()+v.as_expr()*w[0])==1)
norm_squared=sp.expand((w.T*w)[0])
check('svd_norm_is_sum_of_squares',norm_squared==sp.expand(sum(entry**2 for entry in w)))
nz=sp.Symbol('nonzero_coordinate',real=True,nonzero=True)
others=sp.symbols('coordinate1:9',real=True)
check('svd_norm_positive_from_nonzero_coordinate',(nz**2+sum(t**2 for t in others)).is_positive is True)
wy=w.subs(x,y)
inner=sp.expand((w.T*wy)[0])
check('svd_distinct_roots_orthogonal',sp.expand((x-y)*inner-p.as_expr()*wy[0]+p.as_expr().subs(x,y)*w[0])==0)
a,b=sp.symbols('a b',positive=True)
c=sp.symbols('c',real=True)
check('svd_normalization_scalar_identities',sp.simplify(a/sp.sqrt(a)**2-1)==0 and sp.Integer(0)/(sp.sqrt(a)*sp.sqrt(b))==0 and sp.sqrt(a).is_positive is True)
check('svd_gram_norm_eigenvalue',sp.rem(sp.Poly((w.T*G*w)[0]-x*norm_squared,x),p).is_zero)
norm_inverse=sp.invert(sp.Poly(norm_squared,x),p)
check('svd_norm_denominator_nonzero',sp.rem(norm_inverse*sp.Poly(norm_squared,x),p).as_expr()==1)
projector=(w*w.T).applyfunc(lambda entry:sp.rem(sp.Poly(entry,x)*norm_inverse,p).as_expr())
check('svd_projector_reduction',all(sp.rem(sp.Poly(projector[i,j]*norm_squared-w[i]*w[j],x),p).is_zero for i in range(9) for j in range(9)))
root_powers=tuple(sp.RootSum(p,sp.Lambda(x,x**k)) for k in range(9))
check('svd_exact_root_power_sums',root_powers[0]==9 and all(root_powers[k]+sum(coefficients[i]*root_powers[k-i] for i in range(1,k))+k*coefficients[k]==0 for k in range(1,9)))
def root_sum(entry):
    poly=sp.Poly(entry,x)
    if poly.degree()>8:
        raise ValueError('root_sum_requires_reduced_polynomial')
    return sp.Add(*(poly.nth(k)*root_powers[k] for k in range(9)))
projector_sum=projector.applyfunc(root_sum)
check('svd_exact_right_completeness',projector_sum==sp.eye(9))
scaled_left=M*w
left_diagonal=sp.Poly((scaled_left.T*scaled_left)[0]-x*norm_squared,x)
check('svd_exact_left_unit_columns',sp.rem(left_diagonal,p).is_zero and sp.simplify((a*b)/(sp.sqrt(a)*sp.sqrt(b))**2)==1)
check('svd_exact_left_cross_columns',sp.expand((w.T*G*wy)[0]-y*inner+p.as_expr().subs(x,y)*w[0])==0)
reconstruction=(scaled_left*w.T).applyfunc(lambda entry:sp.rem(sp.Poly(entry,x)*norm_inverse,p).as_expr())
reconstructed=reconstruction.applyfunc(root_sum)
check('svd_exact_source_reconstruction',reconstructed==M)
check('svd_reconstruction_scalar_cancellation',sp.simplify((c/(sp.sqrt(a)*sp.sqrt(b)))*sp.sqrt(a)/sp.sqrt(b)-c/b)==0)
V=sp.Matrix.hstack(*(w.subs(x,root)/sp.sqrt(norm_squared.subs(x,root)) for root in eigenvalues))
sigma=sp.diag(*(sp.sqrt(root) for root in eigenvalues))
U=sp.Matrix.hstack(*(scaled_left.subs(x,root)/(sp.sqrt(root)*sp.sqrt(norm_squared.subs(x,root))) for root in eigenvalues))
check('svd_exact_factor_dimensions',M.shape==(12,9) and U.shape==(12,9) and sigma.shape==(9,9) and V.shape==(9,9))
check('svd_wrong_source_reconstruction_rejected',reconstructed!=M+sp.ones(12,9))
check('svd_wrong_projector_normalization_rejected',projector_sum*2!=sp.eye(9))
check('svd_wrong_eigenvalue_rejected',not all(sp.rem(sp.Poly(entry,x),p).is_zero for entry in G*w-(x+1)*w))
report={'backend':'Python/SymPy','checks':len(results),'passed':True,'scope':'Exact thin SVD of the published 12 by 9 integer matrix. Nine distinct positive real algebraic roots of its characteristic polynomial, polynomial eigenvectors, Bezout nonvanishing, positive normalization, pairwise orthogonality and exact RootSum projectors give U^T U=I, V^T V=I, V V^T=I and U Sigma V^T=M. No rounded factor is assumed orthogonal.','results':results}
if __name__=='__main__':
    print(json.dumps(report))
