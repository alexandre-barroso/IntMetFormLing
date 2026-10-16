import json

E='E'
P='Prop'
def arrow(a,b):return ('arrow',a,b)
pred=arrow(E,P)
quant=arrow(pred,P)

def var(name):return ('var',name)
def app(f,x):return ('app',f,x)
def lam(name,typ,body):return ('lam',name,typ,body)
def exists(name,body):return ('exists',name,body)
def both(a,b):return ('and',a,b)

def free(term):
    tag=term[0]
    if tag=='var':return {term[1]}
    if tag=='lam':return free(term[3])-{term[1]}
    if tag=='exists':return free(term[2])-{term[1]}
    return free(term[1])|free(term[2])

def substitute(term,name,value):
    if name not in free(term):return term
    tag=term[0]
    if tag=='var':return value
    if tag in ('lam','exists'):
        binder=term[1]
        if binder in free(value):raise ValueError(('capture',binder))
        if tag=='lam':return lam(binder,term[2],substitute(term[3],name,value))
        return exists(binder,substitute(term[2],name,value))
    return (tag,substitute(term[1],name,value),substitute(term[2],name,value))

def type_of(term,environment):
    tag=term[0]
    if tag=='var':return environment[term[1]]
    if tag=='lam':return arrow(term[2],type_of(term[3],dict(environment,**{term[1]:term[2]})))
    if tag=='exists':
        assert type_of(term[2],dict(environment,**{term[1]:E}))==P
        return P
    left=type_of(term[1],environment)
    right=type_of(term[2],environment)
    if tag=='and':
        assert left==right==P
        return P
    assert left[0]=='arrow' and left[1]==right
    return left[2]

def beta(term):
    assert term[0]=='app' and term[1][0]=='lam'
    return substitute(term[1][3],term[1][1],term[2])

W,T,O,x,y,z,F,G,Q1,Q2,QT,QW,H=[var(a) for a in ('W','T','O','x','y','z','F','G','Q1','Q2','QT','QW','H')]
def relation(a,b):return app(app(O,a),b)
article=lam('F',pred,lam('G',pred,exists('x',both(app(F,x),app(G,x)))))
qw=lam('G',pred,exists('x',both(app(W,x),app(G,x))))
qt=lam('F',pred,exists('y',both(app(T,y),app(F,y))))
h=lam('z',E,exists('y',both(app(T,y),relation(z,y))))
v=lam('Q1',quant,lam('Q2',quant,app(Q2,lam('x',E,app(Q1,lam('y',E,relation(x,y)))))))
lexical_left=app(lam('P',pred,lam('x',E,app(var('P'),x))),W)
lexical_right=lam('x',E,app(W,x))
obj_named=app(QT,lam('z',E,relation(x,z)))
obj_expanded=app(qt,lam('z',E,relation(x,z)))
obj_middle=exists('y',both(app(T,y),app(lam('z',E,relation(x,z)),y)))
obj_final=exists('y',both(app(T,y),relation(x,y)))
verb_object=lam('Q2',quant,app(Q2,lam('x',E,app(QT,lam('y',E,relation(x,y))))))
verb_subject=app(QW,lam('x',E,app(QT,lam('y',E,relation(x,y)))))
verb_final=app(QW,lam('x',E,exists('y',both(app(T,y),relation(x,y)))))
subject_named=app(QW,H)
subject_expanded=app(qw,H)
subject_middle=exists('x',both(app(W,x),app(H,x)))
subject_final=exists('x',both(app(W,x),exists('y',both(app(T,y),relation(x,y)))))
environment={'W':pred,'T':pred,'O':arrow(E,pred),'x':E,'y':E,'z':E,'F':pred,'G':pred,'Q1':quant,'Q2':quant,'QT':quant,'QW':quant,'H':pred}
results=[]
def check(name,value):
    if not value:raise AssertionError(name)
    results.append({'id':name,'passed':True})

check('lexical_beta',beta(lexical_left)==lexical_right)
check('subject_indefinite_beta',beta(app(article,W))==qw)
check('object_definition_expansion',substitute(obj_named,'QT',qt)==obj_expanded)
check('object_first_beta',beta(obj_expanded)==obj_middle)
check('object_second_beta',exists('y',both(app(T,y),beta(app(lam('z',E,relation(x,z)),y))))==obj_final)
check('verb_object_beta',beta(app(v,QT))==verb_object)
check('verb_subject_beta',beta(app(verb_object,QW))==verb_subject)
object_inside=beta(app(qt,lam('y',E,relation(x,y))))
check('verb_object_inside_first',object_inside==exists('y',both(app(T,y),app(lam('y',E,relation(x,y)),y))))
check('verb_object_inside_second',app(QW,lam('x',E,exists('y',both(app(T,y),beta(app(lam('y',E,relation(x,y)),y))))))==verb_final)
check('subject_definition_expansion',substitute(subject_named,'QW',qw)==subject_expanded)
check('subject_first_beta',beta(subject_expanded)==subject_middle)
check('subject_second_beta',exists('x',both(app(W,x),beta(app(h,x))))==subject_final)
check('renamed_argument',beta(app(lam('y',E,relation(x,y)),z))==relation(x,z))
terms=[(lexical_left,pred),(lexical_right,pred),(article,arrow(pred,quant)),(app(article,W),quant),(qw,quant),(qt,quant),(obj_named,P),(obj_expanded,P),(obj_middle,P),(obj_final,P),(v,arrow(quant,arrow(quant,P))),(verb_object,arrow(quant,P)),(verb_subject,P),(verb_final,P),(h,pred),(subject_named,P),(subject_expanded,P),(subject_middle,P),(subject_final,P)]
check('published_types',all(type_of(term,environment)==expected for term,expected in terms))
check('published_free_variables',free(lexical_left)==free(lexical_right)=={'W'} and free(app(article,W))==free(qw)=={'W'} and free(obj_expanded)==free(obj_middle)==free(obj_final)=={'T','O','x'} and free(substitute(subject_expanded,'H',h))==free(substitute(subject_middle,'H',h))==free(subject_final)=={'W','T','O'})
print(json.dumps({'backend':'Python 3','scope':'concrete published lambda terms, all displayed beta steps and types','checks':len(results),'passed':True,'results':results}))
