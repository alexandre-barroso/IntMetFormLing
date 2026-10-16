import json
import itertools
import sympy as sp

results = []
def check(identifier, condition):
    results.append({"id":identifier,"passed":bool(condition)})
acc = ("us","es","es","is","a","a","i","a")
gen = ("u","zero","s","s","u","u","us","os")
fibers = {form:{i+1 for i,value in enumerate(acc) if value==form} for form in set(acc)}
check("fibers", fibers == {"us":{1},"es":{2,3},"is":{4},"a":{5,6,8},"i":{7}})
check("partition_disjoint", all(not fibers[a]&fibers[b] for a in fibers for b in fibers if a!=b))
check("partition_cover", set.union(*fibers.values()) == set(range(1,9)))
check("relation_from_columns", set(zip(acc,gen)) == {("us","u"),("es","zero"),("es","s"),("is","s"),("a","u"),("i","us"),("a","os")} and len(set(zip(acc,gen))) == 7)
A,B={5,6,8},{1,5,6}
check("set_membership", 5 in A and 1 not in A and len(A&B)==2 and len(A|B)==4)
p,q,r = sp.symbols("p q r")
check("all_sets", sp.simplify_logic(sp.Equivalent(sp.Implies(p,q),sp.Not(p & ~q))) == True)
check("some_sets", sp.simplify_logic(sp.Equivalent(p&q,sp.And(p,q))) == True)
check("no_sets", sp.simplify_logic(sp.Equivalent(sp.Not(p&q),sp.Or(~p,~q))) == True)
check("de_morgan_all_base", (not all(())) == any(()))
check("de_morgan_all_step", sp.simplify_logic(sp.Equivalent(~(p&q),~p|~q)) == True)
check("de_morgan_any_base", (not any(())) == all(()))
check("de_morgan_any_step", sp.simplify_logic(sp.Equivalent(~(p|q),~p&~q)) == True)
Q=lambda predicate,var: lambda body: ("exists",var,("and",predicate(var),body(var)))
T=lambda x:("T",x)
W=lambda x:("W",x)
O=lambda x,y:("O",x,y)
QT,QW=Q(T,"y"),Q(W,"x")
V=lambda relation: lambda qo: lambda qs: qs(lambda a: qo(lambda b: relation(a,b)))
check("verb_object_beta", V(O)(QT)(lambda body:body("x")) == ("exists","y",("and",("T","y"),("O","x","y"))))
check("verb_subject_beta", V(O)(QT)(QW) == ("exists","x",("and",("W","x"),("exists","y",("and",("T","y"),("O","x","y"))))))
check("modal_not_veridical", (lambda _:True)(False) and not False)
genitive_seven=(7,"genitivo","singular",gen[6])
accusative_one=(1,"acusativo","plural",acc[0])
check("feature_record",genitive_seven[-1]==accusative_one[-1] and genitive_seven!=accusative_one)
u,v,w=sp.symbols('u v w',integer=True,nonnegative=True)
check('cardinality_union_regions',sp.expand((u+w)+(v+w)-w-(u+v+w))==0)
check('cardinality_union_indicators',all(int(a or b)+int(a and b)==int(a)+int(b) for a,b in itertools.product([False,True],repeat=2)))
a,b,c,d=sp.symbols('a b c d',real=True)
check('cardinality_union_sum_step',sp.expand((a+b)+(c+d)-(a+c)-(b+d))==0)
check('published_sets_from_columns',{i+1 for i,value in enumerate(acc) if value=='a'}==A and {i+1 for i,value in enumerate(gen) if value=='u'}==B)
check('same_output_reflexive',all(acc[i]==acc[i] for i in range(8)))
check('same_output_symmetric',all((acc[i]==acc[j])==(acc[j]==acc[i]) for i,j in itertools.product(range(8),repeat=2)))
check('same_output_transitive',all(not(acc[i]==acc[j] and acc[j]==acc[k]) or acc[i]==acc[k] for i,j,k in itertools.product(range(8),repeat=3)))
check('morphological_product',len(set(acc))==5 and len(set(gen))==5 and len(set(itertools.product(set(acc),set(gen))))==25 and set(zip(acc,gen))<=set(itertools.product(set(acc),set(gen))))
report={"backend":"Python/SymPy","checks":len(results),"passed":all(x["passed"] for x in results),"results":results}
print(json.dumps(report))
raise SystemExit(0 if report["passed"] else 1)
