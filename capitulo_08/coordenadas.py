import json
import sympy as sp
from sympy.matrices.expressions.applyfunc import ElementwiseApplyFunction

n,d,dk,dv,width=sp.symbols('n d dk dv width',integer=True,positive=True)
i,j,k,r,s=sp.symbols('i j k r s',integer=True,nonnegative=True)
X=sp.MatrixSymbol('X',n,d)
WQ=sp.MatrixSymbol('WQ',d,dk)
WK=sp.MatrixSymbol('WK',d,dk)
WV=sp.MatrixSymbol('WV',d,dv)
Q=X*WQ
K=X*WK
V=X*WV
queries=sp.MatrixSymbol('Q',n,dk)
keys=sp.MatrixSymbol('K',n,dk)
values=sp.MatrixSymbol('V',n,dv)
weights=sp.MatrixSymbol('alpha',n,n)
x=sp.MatrixSymbol('x',1,d)
W1=sp.MatrixSymbol('W1',d,width)
W2=sp.MatrixSymbol('W2',width,d)
b1=sp.MatrixSymbol('b1',1,width)
b2=sp.MatrixSymbol('b2',1,d)
z=sp.Symbol('z',real=True)
relu=sp.Lambda(z,sp.Max(0,z))
h=ElementwiseApplyFunction(relu,x*W1+b1)
ffn=h*W2+b2
class RowSoftmax(sp.MatrixExpr):
    @property
    def shape(self):return self.args[0].shape
    def _entry(self,row,column,**kwargs):
        matrix=self.args[0]
        index=sp.Dummy('position',integer=True,nonnegative=True)
        return sp.exp(matrix[row,column])/sp.Sum(sp.exp(matrix[row,index]),(index,0,matrix.cols-1))
attention=RowSoftmax(queries*keys.T/sp.sqrt(dk))*values
results=[]
def check(name,value):
    if not value:raise AssertionError(name)
    results.append({'id':name,'passed':True})

check('projection_shapes',Q.shape==(n,dk) and K.shape==(n,dk) and V.shape==(n,dv))
check('projection_arbitrary_coordinate',Q[i,j].dummy_eq(sp.Sum(X[i,r]*WQ[r,j],(r,0,d-1))))
X512=sp.MatrixSymbol('X512',n,512)
W512=sp.MatrixSymbol('W512',512,64)
check('projection_512_first_coordinate',(X512*W512)[i,0].dummy_eq(sp.Sum(X512[i,r]*W512[r,0],(r,0,511)).doit()))
check('scaled_score_arbitrary_coordinate',(queries*keys.T/sp.sqrt(dk))[i,j].dummy_eq(sp.Sum(queries[i,r]*keys[j,r],(r,0,dk-1))/sp.sqrt(dk)) and sp.sqrt(dk).is_positive is True)
check('attention_output_arbitrary_coordinate',(weights*values)[i,k].dummy_eq(sp.Sum(weights[i,j]*values[j,k],(j,0,n-1))))
check('ffn_relu_hidden_coordinate',h.shape==(1,width) and h[0,j].dummy_eq(sp.Max(0,sp.Sum(x[0,r]*W1[r,j],(r,0,d-1))+b1[0,j])))
check('ffn_composed_arbitrary_coordinate',ffn.shape==(1,d) and ffn[0,k].dummy_eq(sp.Sum(sp.Max(0,sp.Sum(x[0,r]*W1[r,j],(r,0,d-1))+b1[0,j])*W2[j,k],(j,0,width-1))+b2[0,k]))
check('ffn_public_dimensions',h.subs({d:512,width:2048}).shape==(1,2048) and ffn.subs({d:512,width:2048}).shape==(1,512))
check('omitted_relu_rejected',not ffn[0,k].dummy_eq(((x*W1+b1)*W2+b2)[0,k]))
expected_score=sp.Sum(queries[i,r]*keys[j,r],(r,0,dk-1))/sp.sqrt(dk)
normalizer=sp.Sum(sp.exp(sp.Sum(queries[i,r]*keys[s,r],(r,0,dk-1))/sp.sqrt(dk)),(s,0,n-1))
expected_attention=sp.Sum(sp.exp(expected_score)*values[j,k]/normalizer,(j,0,n-1))
check('attention_composed_arbitrary_coordinate',attention.shape==(n,dv) and attention[i,k].dummy_eq(expected_attention))
check('attention_rows_normalized_separately',not attention[i,k].dummy_eq(sp.Sum(sp.exp(expected_score)*values[j,k],(j,0,n-1))))
print(json.dumps({'backend':'Python 3','scope':'symbolic matrix dimensions; zero-based indices correspond to printed one-based indices; real entries and positive integer dimensions','checks':len(results),'passed':True,'results':results}))
