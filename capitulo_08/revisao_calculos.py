import json
import sympy as sp
results=[]
def check(identifier,condition):
    results.append({"id":identifier,"passed":bool(condition)})
time,coordinate=sp.symbols('time coordinate',integer=True)
embedding=sp.IndexedBase('embedding')
offsets=(-2,-1,1,2)
positions=tuple(time+offset for offset in offsets)
selected_context=tuple(embedding[position,coordinate] for position in positions)
cbow_selected=sum(selected_context)/4
check('cbow_selected_coordinate',sp.expand(cbow_selected-(embedding[time-2,coordinate]+embedding[time-1,coordinate]+embedding[time+1,coordinate]+embedding[time+2,coordinate])/4)==0)
check('cbow_excludes_center',len(set(offsets))==4 and all(sp.Ne(position,time)==sp.true for position in positions))
z=sp.Symbol('z',real=True)
check('c08_e0112_integral',sp.exp(-z).is_positive is True)
a,w=sp.symbols('a w',real=True)
check('c08_e0135_integral',sp.simplify(sp.exp(a+w)-sp.exp(a)*sp.exp(w))==0)
p=sp.Symbol('p',positive=True)
check('c08_e0222_integral',p**1*(1-p)**0==p and p**0*(1-p)**1==1-p)
z=sp.Symbol('z',real=True)
p=sp.exp(z)/(1+sp.exp(z))
check('c08_e0239_integral',sp.simplify(sp.expand_log(sp.log(p))-z+sp.log(1+sp.exp(z)))==0 and sp.simplify(sp.expand_log(sp.log(1-p))+sp.log(1+sp.exp(z)))==0)
check('c08_e0250_integral',1/(1+sp.exp(0))==sp.Rational(1,2))
w1,w2,x1,x2,b=sp.symbols('w1 w2 x1 x2 b',real=True)
z=w1*x1+w2*x2+b
check('c08_e0253_integral',tuple(sp.diff(z,u) for u in (w1,w2,b))==(x1,x2,1))
w=sp.Symbol('w',positive=True)
check('c08_e0281_integral',sp.Abs(w)==w and sp.Abs(-w)==w)
a,b=sp.symbols('a b',real=True)
check('c08_e0324_integral',sp.expand((a-b-1)-(a-1-b))==0 and sp.expand((b-a-1)-(b-(a+1)))==0)
a,b=sp.symbols('a b',real=True)
check('c08_e0326_integral',sp.expand((a-b)+(b-a))==0 and sp.reduce_inequalities([sp.Symbol('gap',real=True)>=1,-sp.Symbol('gap',real=True)>=1],sp.Symbol('gap',real=True))==sp.false)
p=sp.Symbol('p',positive=True)
q=sp.Symbol('q',positive=True)
v=p/(p+q)
check('c08_e0382_integral',sp.cancel(v-1).is_negative is True and v.is_positive is True)
check('c08_e0496_integral',sp.sqrt(64)==8)
r,p=sp.symbols('r p',positive=True)
check('odds_all_steps',sp.solve(sp.Eq(r,p/(1-p)),p)==[r/(1+r)] and sp.expand(r*(1-p)-p-(r-r*p-p))==0 and sp.expand(r-r*p-p-(r-p*(1+r)))==0 and (1+r).is_positive)
o,e,n=sp.symbols('observed expected total',positive=True)
check('log_ratio_per_cell',sp.simplify(sp.expand_log(sp.log(o/n)-sp.log(e/n))-sp.expand_log(sp.log(o/e)))==0)
count=sp.Symbol('count',integer=True,positive=True)
j=sp.Symbol('j',integer=True)
c=sp.Symbol('c',real=True)
z=sp.IndexedBase('score')
shifted=sp.factor_terms(sp.Sum(sp.expand_power_exp(sp.exp(z[j]+c)),(j,1,count)))
base=sp.Sum(sp.exp(z[j]),(j,1,count))
check('softmax_shift_general',sp.simplify(shifted-sp.exp(c)*base)==0 and sp.simplify(sp.exp(z[1]+c)/shifted-sp.exp(z[1])/base)==0)
positive=sp.Symbol('positive',positive=True)
check('relu_branches',sp.Max(0,positive)==positive and sp.Max(0,-positive)==0 and sp.Max(0,0)==0)
a,b,c,total=sp.symbols('a b c total',real=True)
scores=(a,a+c,a+b,a+b+c)
check('xor_affine_scores',sp.expand(scores[0]+scores[3]-(2*a+b+c))==0 and sp.expand(scores[1]+scores[2]-(2*a+b+c))==0 and sp.reduce_inequalities([total<=0,total>0],total)==sp.false)
base,gap=sp.symbols('base gap',positive=True)
positive_ratio=sp.log(1+gap/base)
check('log_ratio_sign',positive_ratio.is_positive is True and (-positive_ratio).is_negative is True and sp.log(base)-sp.log(base)==0)
check('c08_e0630_integral',abs(sp.N(sp.sympify('1/(1+exp(-833/1000))',rational=True),60)-sp.sympify('6969888901/10000000000',rational=True))<sp.sympify('1/10000000000',rational=True))
check('c08_e0639_integral',abs(sp.N(sp.sympify('-log(3/10)',rational=True),60)-sp.sympify('1203972804/1000000000',rational=True))<sp.sympify('1/1000000000',rational=True))
check('c08_e0640_integral',abs(sp.N(sp.sympify('-log(7/10)',rational=True),60)-sp.sympify('356674944/1000000000',rational=True))<sp.sympify('1/1000000000',rational=True))
values=[sp.log(2),sp.log(1+sp.exp(sp.Rational(7,10)))-sp.Rational(7,10)]
printed=[sp.Rational(693147181,10**9),sp.Rational(403186049,10**9)]
check('c08_e0648_integral',all(abs(sp.N(a,60)-b)<sp.Rational(1,10**9) for a,b in zip(values,printed)))
label=sp.Symbol('label',real=True)
check('loss_zero_exact',sp.log(1+sp.exp(0))-label*0==sp.log(2))
p,r=sp.symbols('precision recall',positive=True)
check('harmonic_intermediate',sp.simplify(1/((1/p+1/r)/2)-2/(1/p+1/r))==0 and sp.simplify(2/(1/p+1/r)-2*p*r/(p+r))==0)
center=sp.Rational(6969888901,10**10);radius=sp.Rational(1,2*10**10)
check('sigmoid_text_roundings',sp.Rational(697,1000)-sp.Rational(1,2000)<center-radius and center+radius<sp.Rational(697,1000)+sp.Rational(1,2000) and sp.Rational(7,10)-sp.Rational(1,200)<center-radius and center+radius<sp.Rational(7,10)+sp.Rational(1,200) and abs(sp.Rational(697,1000)-sp.Rational(7,10))<sp.Rational(1,200))
lo=sp.Rational(36441,20000);hi=sp.Rational(36443,20000);slo=sp.Rational(664697,20000);shi=sp.Rational(664699,20000);r=sp.sympify('18221/332349',rational=True);out=sp.sympify('548/10000',rational=True)
check('first_decimal_quotient',0<lo and 0<slo and r-sp.Rational(1,20000)<lo/shi and hi/slo<r+sp.Rational(1,20000) and abs(r-out)<sp.Rational(1,20000))
lo=sp.Rational(490649,20000);hi=sp.Rational(490651,20000);slo=sp.Rational(664697,20000);shi=sp.Rational(664699,20000);r=sp.sympify('245325/332349',rational=True);out=sp.sympify('7382/10000',rational=True)
check('fifth_decimal_quotient',0<lo and 0<slo and r-sp.Rational(1,20000)<lo/shi and hi/slo<r+sp.Rational(1,20000) and abs(r-out)<sp.Rational(1,20000))
dimension=sp.Symbol('dimension',integer=True,positive=True)
i=sp.Symbol('i',integer=True);j=sp.Symbol('j',integer=True,positive=True)
u=sp.IndexedBase('u');v=sp.IndexedBase('v');label=sp.Symbol('label',real=True)
score=sp.Sum(u[i]*v[i],(i,1,dimension))
coordinate_derivative=sp.refine(sp.diff(score,u[j]).doit(),sp.Q.is_true(j<=dimension))
loss=sp.log(1+sp.exp(score))-label*score
actual=sp.refine(sp.diff(loss,u[j]).doit(),sp.Q.is_true(j<=dimension))
check('sgns_arbitrary_coordinate',coordinate_derivative==v[j] and sp.simplify(actual-(sp.exp(score)/(1+sp.exp(score))-label)*v[j])==0)
rows1=[('ban.tan',(-2,0)),('ba.tan',(-1,-1))];rows2=[('ban',(-1,0)),('ba',(0,-1))]
scores1=[(name,2*violations[0]+violations[1]) for name,violations in rows1]
scores2=[(name,violations[0]+2*violations[1]) for name,violations in rows2]
winner=lambda scores:[name for name,score in scores if all(other<=score for _,other in scores)]
check('labeled_tableau_winners',scores1==[('ban.tan',-4),('ba.tan',-3)] and scores2==[('ban',-1),('ba',-2)] and winner(scores1)==['ba.tan'] and winner(scores2)==['ban'])
def review_transitions(q,c):
    if q not in (0,1):return []
    if c=='d':return [(1,'d'),(2,'t')]
    if c in ('t','a'):return [(0,c)]
    return []
def review_traces(q,word):
    if not word:return [([q],'')]
    return [([q]+states,out+suffix) for state,out in review_transitions(q,word[0]) for states,suffix in review_traces(state,word[1:])]
def accepted_review_traces(word):
    return [(states,out) for states,out in review_traces(0,word) if states[-1] in (0,2)]
check('published_transduction_traces',accepted_review_traces('tad')==[([0,0,0,2],'tat')] and accepted_review_traces('tada')==[([0,0,0,1,0],'tada')])
check('edit_table_minimum_steps',min(1+1,1+1,0+2)==min(2,2,2) and min(2,2,2)==2 and min(4+1,4+1,3+0)==3)
key_dimension=sp.Symbol('key_dimension',positive=True,integer=True)
check('positive_key_dimension',sp.sqrt(key_dimension).is_positive is True)
def bigram_product(q,previous,following):
    if not following:return sp.Integer(1)
    return q(previous,following[0])*bigram_product(q,following[0],following[1:])
bigram_q=sp.Function('bigram_q')
start,first,want,english,food,stop=sp.symbols('start first want english food stop')
bigram_sequence=[first,want,english,food,stop]
check('bigram_boundary_expansion',sp.expand(bigram_product(bigram_q,start,bigram_sequence)-bigram_q(start,first)*bigram_q(first,want)*bigram_q(want,english)*bigram_q(english,food)*bigram_q(food,stop))==0)
print(json.dumps({"checks":len(results),"passed":all(r["passed"] for r in results),"results":results}))
raise SystemExit(0 if all(r["passed"] for r in results) else 1)
