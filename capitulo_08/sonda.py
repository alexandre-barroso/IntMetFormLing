import json
import sympy as sp

k,m=sp.symbols('k m',integer=True,positive=True)
r=sp.Symbol('r',integer=True,nonnegative=True)
B=sp.MatrixSymbol('B',k,m)
h=sp.MatrixSymbol('h',m,1)
g=sp.MatrixSymbol('g',m,1)
u=sp.MatrixSymbol('u',k,1)
transformed=B*(h-g)
squared=(transformed.T*transformed)[0,0]
norm_expansion=sp.Sum(transformed[r,0]**2,(r,0,k-1))
swapped=B*(g-h)
nil=sp.Symbol('nil')
head=sp.Symbol('head',real=True)
tail,xs=sp.symbols('tail xs')
cons=sp.Function('cons')
square_sum=sp.Function('square_sum')
square_sum_negated=sp.Function('square_sum_negated')
rules={square_sum(nil):0,square_sum(cons(head,tail)):head**2+square_sum(tail),square_sum_negated(nil):0,square_sum_negated(cons(head,tail)):(-head)**2+square_sum_negated(tail)}
tail_sum=sp.Symbol('tail_sum',nonnegative=True)
results=[]
def check(name,value):
    if not value:raise AssertionError(name)
    results.append({'id':name,'passed':True})

check('probe_arbitrary_dimensions',transformed.shape==(k,1) and (transformed.T*transformed).shape==(1,1))
check('probe_squared_coordinate_expansion',(u.T*u)[0,0].dummy_eq(sp.Sum(u[r,0]**2,(r,0,k-1))) and (u.T*u).xreplace({u:transformed}).doit()==transformed.T*transformed and sp.Sum(u[r,0]**2,(r,0,k-1)).xreplace({u:transformed}).doit().dummy_eq(norm_expansion))
check('u_transpose_u_is_sum_of_squares',(u.T*u)[0,0].dummy_eq(sp.Sum(u[r,0]**2,(r,0,k-1))))
check('swap_negates_actual_linear_transform',sp.expand(swapped+transformed)==sp.ZeroMatrix(k,1))
check('swap_preserves_actual_squared_norm',sp.expand(swapped.T*swapped-transformed.T*transformed)==sp.ZeroMatrix(1,1))
check('equal_vectors_have_zero_squared_norm',sp.expand(squared.subs(g,h)).doit()==0)
check('finite_square_fold_base',sp.sympify(square_sum(nil)).xreplace(rules)==0)
step=square_sum(cons(head,tail)).xreplace(rules).xreplace({square_sum(tail):tail_sum})
check('finite_square_fold_nonnegative_step',step.is_nonnegative is True)
symmetry_step=(square_sum_negated(cons(head,tail)).xreplace(rules)-square_sum(cons(head,tail)).xreplace(rules)).xreplace({square_sum_negated(tail):square_sum(tail)})
check('finite_square_fold_symmetry_base',square_sum_negated(nil).xreplace(rules)==square_sum(nil).xreplace(rules))
check('finite_square_fold_symmetry_step',sp.expand(symmetry_step)==0)
check('negative_square_claim_rejected',(-head**2+tail_sum).subs({head:1,tail_sum:0})<0)
check('norm_square_is_not_metric',(sp.Integer(0)-2)**2>(sp.Integer(0)-1)**2+(sp.Integer(1)-2)**2)
singular=sp.Matrix([[1,0]])
distinct=sp.Matrix([0,1])
check('noninjective_probe_can_collapse_distinct_vectors',distinct!=sp.zeros(2,1) and singular*distinct==sp.zeros(1,1))
print(json.dumps({'backend':'Python 3','scope':'arbitrary positive integer matrix dimensions; real components; finite sum induction; no injectivity or metric claim','checks':len(results),'passed':True,'results':results}))
