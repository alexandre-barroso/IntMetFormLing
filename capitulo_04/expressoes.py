import json
import itertools
import sympy as sp

results=[]
def check(identifier, condition):
    results.append({"id":identifier,"passed":bool(condition)})
Q=sp.Rational
edges={(2,1),(2,3),(2,5),(5,4)}
A=sp.Matrix(5,5,lambda i,j:int((i+1,j+1) in edges))
check("adjacency", A==sp.Matrix([[0,0,0,0,0],[1,0,1,0,1],[0,0,0,0,0],[0,0,0,0,0],[0,0,0,1,0]]))
check("degree_vectors", [sum(A.row(i)) for i in range(5)]==[0,3,0,0,1] and [sum(A.col(i)) for i in range(5)]==[1,0,1,1,1])
check("adjacency_entries", (A[1,4],A[4,1],A[1,3],sum(A))==(1,0,0,4))
B=sp.zeros(5);B[1,3]=1
check("two_steps", A*A==B)
check("no_three_steps", A**3==sp.zeros(5))
linked=lambda i,j:(i,j) in edges or (j,i) in edges
walk=lambda n,i,j:i==j if n==0 else any(linked(i,k) and walk(n-1,k,j) for k in range(1,6))
check("graph_distance", walk(2,1,5) and not walk(0,1,5) and not walk(1,1,5))
pa=[1,2,3,4,5];pb=[1,2,5,3,4]
length=lambda p:sum(abs(p[i-1]-p[j-1]) for i,j in edges)
check("order_lengths", (length(pa),length(pb))==(6,7))
check("permutationB", sorted(pb)==pa)
T=sp.Matrix([[1,1,1,1,1,1,0,0],[0,0,0,0,1,1,1,1]])
R=sp.Matrix([[1,0,0,0]]*4+[[1,1,0,1],[1,1,1,1],[0,0,0,1],[0,0,0,1]])
check("polysemy", T*R==sp.Matrix([[6,2,1,2],[2,2,1,4]]))
cherry=sp.Matrix([442,8,2]);digital=sp.Matrix([5,1683,1670]);information=sp.Matrix([5,3982,3325])
check("dot_products", (cherry.dot(information),digital.dot(information))==(40716,12254481))
check("squared_lengths", [v.dot(v) for v in [cherry,digital,information]]==[195432,5621414,26911974])
d,a,b=sp.symbols("d a b",positive=True)
check("cosine_square", sp.simplify((d/(sp.sqrt(a)*sp.sqrt(b)))**2-d**2/(a*b))==0)
cosine=lambda v,w:v.dot(w)/(v.norm()*w.norm())
check("cosine_cherry_bounds",cherry.dot(information)>0 and cherry.dot(cherry)>0 and information.dot(information)>0 and Q(175,10000)**2<cherry.dot(information)**2/(cherry.dot(cherry)*information.dot(information))<Q(185,10000)**2)
check("cosine_digital_bounds",digital.dot(information)>0 and digital.dot(digital)>0 and information.dot(information)>0 and Q(9955,10000)**2<digital.dot(information)**2/(digital.dot(digital)*information.dot(information))<Q(9965,10000)**2)
s=sp.symbols("s",positive=True)
check("length_positive", sp.sqrt(s).is_positive)
check("unit_normalization", sp.simplify(sp.sqrt(s/sp.sqrt(s)**2))==1)
rows=['100100000','101000000','110000000','011010000','011200000','010010000','010010000','001100000','010000001','000001110','000000111','000000011']
M=sp.Matrix([[int(x) for x in row] for row in rows])
indices=list(M.T.rref()[1]);N=M[indices,:];left=sp.zeros(9,12)
for j,k in enumerate(indices):left[:,k]=N.inv()[:,j]
check("full_rank_certificate", left*M==sp.eye(9))
check("original_rank", M.rank()==9)
u=sp.Matrix([[Q(22,100),Q(-11,100)]])
sigma=sp.diag(Q(334,100),Q(254,100))
v=sp.Matrix([[Q(20,100),Q(-6,100)],[Q(61,100),Q(17,100)]])
check("reconstruction_entries", u*sigma*v.T==sp.Matrix([[Q(163724,1000000),Q(40073,100000)]]))
i,j=sp.symbols("i j",integer=True)
E=sp.IndexedBase("E")
frobenius=sp.Sum(E[i,j]**2,(i,0,11),(j,0,8))
error_left=sp.Matrix(12,9,lambda i,j:sp.Symbol(f"a_{i}_{j}",real=True))
error_right=sp.Matrix(12,9,lambda i,j:sp.Symbol(f"b_{i}_{j}",real=True))
error_matrix=error_left-error_right
error_entries=sum((error_left[i,j]-error_right[i,j])**2 for i in range(12) for j in range(9))
check("reconstruction_error",sp.expand(sp.trace(error_matrix.T*error_matrix)-error_entries)==0)
marine=[Q(400,10),Q(821,10),Q(853,10),Q(448,10),Q(32,10),Q(33,10)]
teacher=[Q(52,10),Q(70,10),Q(93,10),Q(47,10),Q(484,10),Q(536,10)]
unfold=lambda j,k:2*k+j
check("tensor_indices", (unfold(1,1),unfold(1,2),marine[unfold(1,1)],teacher[unfold(1,2)])==(3,5,Q(448,10),Q(536,10)))
check("tensor_bijection", sorted(unfold(j,k) for j in range(2) for k in range(3))==list(range(6)))
sv=sorted((sp.sqrt(x).evalf(50) for x in (M.T*M).eigenvals()),reverse=True)
published=list(map(Q,['3.34','2.54','2.35','1.64','1.50','1.31','0.85','0.56','0.36']))
check("singular_value_roundings", len(sv)==9 and all(abs(x-y)<Q(1,200) for x,y in zip(sv,published)))
countries=sp.Matrix([[-677709,1874645],[-885794,1253283],[-1305110,-84347],[-1716295,-1397095]])/1000000
capitals=sp.Matrix([[1119508,1726213],[1546941,902989],[1135124,-402403],[852681,-1576851]])/1000000
differences=capitals-countries
check("projected_differences",differences==sp.Matrix([[1797217,-148432],[2432735,-350294],[2440234,-318056],[2568976,-179756]])/1000000)
check("projected_arrow_endpoint",countries+differences==capitals)
check("projected_common_direction",all(differences[i,0]>0>differences[i,1] for i in range(4)))
check("projected_slopes_not_identical",differences[0,1]/differences[0,0]!=differences[1,1]/differences[1,0])
k=sp.symbols('k',integer=True,positive=True)
check('possible_pairs_general',sp.combsimp(sp.binomial(k,2)-k*(k-1)/2)==0 and sp.binomial(0,2)==0 and sp.binomial(1,2)==0)
dimension=sp.symbols('dimension',integer=True,positive=True)
coordinate=sp.symbols('coordinate',integer=True)
coordinates=sp.IndexedBase('coordinates',real=True)
squared_length=sp.Sum(coordinates[coordinate]**2,(coordinate,1,dimension))
normalized_squared_length=sp.Sum((coordinates[coordinate]/sp.sqrt(squared_length))**2,(coordinate,1,dimension))
check("unit_normalization_arbitrary_sum",sp.simplify(normalized_squared_length.doit())==1 and sp.simplify(sp.sqrt(normalized_squared_length.doit()))==1)
model_A=sp.MatrixSymbol('model_A',350,350)
model_B=sp.MatrixSymbol('model_B',350,350)
model_u=sp.MatrixSymbol('model_u',350,1)
model_v=sp.MatrixSymbol('model_v',350,1)
model_i,model_j=sp.symbols('model_i model_j',integer=True)
check("affix_product_coordinate",sp.simplify((model_A*model_v)[model_i,0]-sp.Sum(model_A[model_i,model_j]*model_v[model_j,0],(model_j,0,349)))==0)
check("full_additive_coordinate",sp.simplify((model_A*model_u+model_B*model_v)[model_i,0]-sp.Sum(model_A[model_i,model_j]*model_u[model_j,0]+model_B[model_i,model_j]*model_v[model_j,0],(model_j,0,349)))==0)
check("weighted_additive_coordinate",sp.expand((Q(16,100)*model_u+Q(33,100)*model_v)[model_i,0]-Q(16,100)*model_u[model_i,0]-Q(33,100)*model_v[model_i,0])==0)
check("composition_dimensions",(model_A*model_u+model_B*model_v).shape==(350,1) and M.shape==(12,9) and M.T.shape==(9,12) and (M*M.T).shape==(12,12) and (M.T*M).shape==(9,9))
check("two_step_entry_formula",all((A*A)[i,j]==sum(A[i,k]*A[k,j] for k in range(5)) for i in range(5) for j in range(5)))
check("two_step_terms",[A[1,k]*A[k,3] for k in range(5)]==[0,0,0,0,1])
bag_words=["John","threw","out","the","trash"]
bag_orders=["John threw out the trash".split(),"John threw the trash out".split()]
check("bag_counts",all([words.count(word) for word in bag_words]==[1,1,1,1,1] for words in bag_orders))
report={"backend":"Python/SymPy","checks":len(results),"passed":all(x["passed"] for x in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report["passed"] else 1)
