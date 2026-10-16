import json

BOT=('false',)
def atom(name,*terms):return ('atom',name,tuple(terms))
def conj(a,b):return ('and',a,b)
def disj(a,b):return ('or',a,b)
def impl(a,b):return ('imp',a,b)
def neg(a):return impl(a,BOT)
def iff(a,b):return conj(impl(a,b),impl(b,a))
def allf(x,a):return ('all',x,a)
def exf(x,a):return ('ex',x,a)

def free(f):
    if f[0]=='false':return set()
    if f[0]=='atom':return set(f[2])
    if f[0] in ('all','ex'):return free(f[2])-{f[1]}
    return free(f[1])|free(f[2])

def subst(f,x,t):
    if x not in free(f):return f
    if f[0]=='atom':return atom(f[1],*(t if a==x else a for a in f[2]))
    if f[0] in ('all','ex'):
        if f[1]==t:raise ValueError('capture')
        return (f[0],f[1],subst(f[2],x,t))
    return (f[0],subst(f[1],x,t),subst(f[2],x,t))

def canonical(f,bound=()):
    if f[0]=='false':return f
    if f[0]=='atom':
        return ('atom',f[1],tuple(('bound',bound[::-1].index(t)) if t in bound else ('free',t) for t in f[2]))
    if f[0] in ('all','ex'):return (f[0],canonical(f[2],bound+(f[1],)))
    return (f[0],canonical(f[1],bound),canonical(f[2],bound))

def same(a,b):return canonical(a)==canonical(b)
def require(test):
    if not test:raise ValueError('invalid deduction')
def extend(context,name,formula):
    require(name not in context)
    return dict(context,**{name:formula})

def verify(proof,context=None,variables=frozenset()):
    context={} if context is None else context
    rule=proof[0]
    if rule=='hyp':return context[proof[1]]
    if rule=='andI':return conj(verify(proof[1],context,variables),verify(proof[2],context,variables))
    if rule in ('andEL','andER'):
        f=verify(proof[1],context,variables);require(f[0]=='and');return f[1 if rule=='andEL' else 2]
    if rule=='impI':return impl(proof[2],verify(proof[3],extend(context,proof[1],proof[2]),variables))
    if rule=='impE':
        f=verify(proof[1],context,variables);g=verify(proof[2],context,variables)
        require(f[0]=='imp' and same(f[1],g));return f[2]
    if rule=='orIL':return disj(verify(proof[1],context,variables),proof[2])
    if rule=='orIR':return disj(proof[1],verify(proof[2],context,variables))
    if rule=='orE':
        f=verify(proof[1],context,variables);require(f[0]=='or')
        a=verify(proof[3],extend(context,proof[2],f[1]),variables)
        b=verify(proof[5],extend(context,proof[4],f[2]),variables)
        require(same(a,b));return a
    if rule=='falseE':require(verify(proof[2],context,variables)==BOT);return proof[1]
    if rule=='allI':
        x=proof[1];require(x not in variables and all(x not in free(f) for f in context.values()))
        return allf(x,verify(proof[2],context,variables|{x}))
    if rule=='allE':
        f=verify(proof[1],context,variables);require(f[0]=='all' and proof[2] in variables)
        return subst(f[2],f[1],proof[2])
    if rule=='exI':
        x,body,t,p=proof[1:];require(t in variables)
        require(same(verify(p,context,variables),subst(body,x,t)))
        return exf(x,body)
    if rule=='exE':
        f=verify(proof[1],context,variables);x=proof[2];require(f[0]=='ex')
        require(x not in variables and x not in free(f) and all(x not in free(g) for g in context.values()))
        g=verify(proof[4],extend(context,proof[3],subst(f[2],f[1],x)),variables|{x})
        require(x not in free(g));return g
    if rule=='dne':
        f=verify(proof[1],context,variables)
        require(f[0]=='imp' and f[2]==BOT and f[1][0]=='imp' and f[1][2]==BOT)
        return f[1][1]
    if rule=='lem':require(free(proof[1])<=variables);return disj(proof[1],neg(proof[1]))
    raise ValueError(rule)

def h(name):return ('hyp',name)
def ae(p):return ('andEL',p)
def be(p):return ('andER',p)
def ai(p,q):return ('andI',p,q)
def ii(name,formula,p):return ('impI',name,formula,p)
def ie(p,q):return ('impE',p,q)
def ui(x,p):return ('allI',x,p)
def ue(p,x):return ('allE',p,x)
def ei(x,formula,t,p):return ('exI',x,formula,t,p)
def ee(p,x,name,body):return ('exE',p,x,name,body)
def fi(goal,p):return ('falseE',goal,p)
def oi(p,b):return ('orIL',p,b)
def oj(a,p):return ('orIR',a,p)
def oe(p,a,pa,b,pb):return ('orE',p,a,pa,b,pb)
def P(x):return atom('P',x)
def S(x):return atom('S',x)
def L(x):return atom('L',x)
def U(x):return atom('U',x)
def N(x):return atom('N',x)
def F(x):return atom('F',x)
def D(x):return atom('D',x)
def R(y,x):return atom('R',y,x)
def A(x):return atom('A',x)
def B(x):return atom('B',x)
def ES(x):return atom('Es',x)
def TR(x):return atom('Tr',x)
def C(x):return atom('C',x)
def M(x):return atom('ManageCome',x)

subset=allf('x',impl(S('x'),L('x')))
diff=conj(S('x'),neg(L('x')))
difference=ii('subset',subset,ui('x',ai(ii('d',diff,ie(be(h('d')),ie(ue(h('subset'),'x'),ae(h('d'))))),ii('false',BOT,fi(diff,h('false'))))))
inter=conj(L('x'),conj(U('x'),neg(L('x'))))
disjoint=ui('x',ai(ii('d',inter,ie(be(be(h('d'))),ae(h('d')))),ii('false',BOT,fi(inter,h('false')))))
lu=allf('x',impl(L('x'),U('x')))
union=disj(L('x'),conj(U('x'),neg(L('x'))))
cover=ii('subset',lu,ui('x',ai(ii('union',union,oe(h('union'),'left',ie(ue(h('subset'),'x'),h('left')),'right',ae(h('right')))),ii('u',U('x'),oe(('lem',L('x')),'l',oi(h('l'),conj(U('x'),neg(L('x')))),'nl',oj(L('x'),ai(h('u'),h('nl'))))))))
sn=allf('x',impl(S('x'),L('x')))
ln=allf('x',impl(L('x'),N('x')))
transitivity=ii('sl',sn,ii('ln',ln,ui('x',ii('s',S('x'),ie(ue(h('ln'),'x'),ie(ue(h('sl'),'x'),h('s')))))))
inverse=exf('x',conj(D('x'),allf('y',impl(F('y'),R('y','x')))))
surface=allf('y',impl(F('y'),exf('x',conj(D('x'),R('y','x')))))
common_witness=ii('inverse',inverse,ee(h('inverse'),'u','witness',ui('y',ii('f',F('y'),ei('x',conj(D('x'),R('y','x')),'u',ai(ae(h('witness')),ie(ue(be(h('witness')),'y'),h('f'))))))))

def de_morgan_exists(predicate):
    exists=exf('x',predicate('x'))
    forward=ii('nex',neg(exists),ui('u',ii('p',predicate('u'),ie(h('nex'),ei('x',predicate('x'),'u',h('p'))))))
    reverse=ii('alln',allf('x',neg(predicate('x'))),ii('ex',exists,ee(h('ex'),'u','p',ie(ue(h('alln'),'u'),h('p')))))
    return ai(forward,reverse)

def de_morgan_all(predicate):
    universal=allf('x',predicate('x'))
    exists=exf('x',neg(predicate('x')))
    derive_all=ui('u',('dne',ii('np',neg(predicate('u')),ie(h('nex'),ei('x',neg(predicate('x')),'u',h('np'))))))
    forward=ii('nall',neg(universal),('dne',ii('nex',neg(exists),ie(h('nall'),derive_all))))
    reverse=ii('ex',exists,ii('all',universal,ee(h('ex'),'u','np',ie(h('np'),ue(h('all'),'u')))))
    return ai(forward,reverse)

restriction=allf('x',impl(conj(ES('x'),TR('x')),C('x')))
restricted=ii('rule',restriction,ui('x',ii('es',ES('x'),ii('tr',TR('x'),ie(ue(h('rule'),'x'),ai(h('es'),h('tr')))))))
manage_rule=allf('x',impl(M('x'),C('x')))
manage_premise=exf('x',conj(ES('x'),M('x')))
manage=ii('rule',manage_rule,ii('premise',manage_premise,ee(h('premise'),'u','w',ei('x',conj(ES('x'),C('x')),'u',ai(ae(h('w')),ie(ue(h('rule'),'u'),be(h('w'))))))))

certificates={
'difference_empty':(difference,impl(subset,allf('x',iff(diff,BOT)))),
'complement_disjoint':(disjoint,allf('x',iff(inter,BOT))),
'complement_cover':(cover,impl(lu,allf('x',iff(union,U('x'))))),
'subset_transitivity':(transitivity,impl(sn,impl(ln,allf('x',impl(S('x'),N('x')))))),
'common_witness_entails_surface':(common_witness,impl(inverse,surface)),
'not_exists_iff_all_not':(de_morgan_exists(P),iff(neg(exf('x',P('x'))),allf('x',neg(P('x'))))),
'not_all_iff_exists_not':(de_morgan_all(P),iff(neg(allf('x',P('x'))),exf('x',neg(P('x'))))),
'no_intersection':(de_morgan_exists(lambda x:conj(A(x),B(x))),iff(neg(exf('x',conj(A('x'),B('x')))),allf('x',neg(conj(A('x'),B('x')))))),
'restricted_universal':(restricted,impl(restriction,allf('x',impl(ES('x'),impl(TR('x'),C('x')))))),
'manage_inference':(manage,impl(manage_rule,impl(manage_premise,exf('x',conj(ES('x'),C('x'))))))
}

def membership(term,x):
    if term[0]=='set':return atom(term[1],x)
    if term[0]=='empty':return BOT
    if term[0]=='inter':return conj(membership(term[1],x),membership(term[2],x))
    if term[0]=='diff':return conj(membership(term[1],x),neg(membership(term[2],x)))
    if term[0]=='union':return disj(membership(term[1],x),membership(term[2],x))
    raise ValueError(term)

def equality_formula(a,b):return allf('x',iff(membership(a,'x'),membership(b,'x')))
def subset_formula(a,b):return allf('x',impl(membership(a,'x'),membership(b,'x')))
def nonempty_formula(a):return exf('x',membership(a,'x'))
def empty_formula(a):return allf('x',neg(membership(a,'x')))
def rejected(proof,context=None,variables=frozenset()):
    try:verify(proof,context,variables)
    except (ValueError,KeyError):return True
    return False

results=[]
def check(name,value):
    if not value:raise AssertionError(name)
    results.append({'id':name,'passed':True})

check('difference_empty',same(verify(certificates['difference_empty'][0]),certificates['difference_empty'][1]))
check('complement_disjoint',same(verify(certificates['complement_disjoint'][0]),certificates['complement_disjoint'][1]))
check('complement_cover',same(verify(certificates['complement_cover'][0]),certificates['complement_cover'][1]))
check('subset_transitivity',same(verify(certificates['subset_transitivity'][0]),certificates['subset_transitivity'][1]))
check('common_witness_entails_surface',same(verify(certificates['common_witness_entails_surface'][0]),certificates['common_witness_entails_surface'][1]))
check('not_exists_iff_all_not',same(verify(certificates['not_exists_iff_all_not'][0]),certificates['not_exists_iff_all_not'][1]))
check('not_all_iff_exists_not',same(verify(certificates['not_all_iff_exists_not'][0]),certificates['not_all_iff_exists_not'][1]))
check('no_intersection',same(verify(certificates['no_intersection'][0]),certificates['no_intersection'][1]))
check('restricted_universal',same(verify(certificates['restricted_universal'][0]),certificates['restricted_universal'][1]))
check('manage_inference',same(verify(certificates['manage_inference'][0]),certificates['manage_inference'][1]))
check('all_set_definition',same(allf('x',impl(A('x'),B('x'))),subset_formula(('set','A'),('set','B'))))
check('some_set_definition',same(exf('x',conj(A('x'),B('x'))),nonempty_formula(('inter',('set','A'),('set','B')))))
check('no_set_definition',same(certificates['no_intersection'][1],iff(neg(exf('x',conj(A('x'),B('x')))),empty_formula(('inter',('set','A'),('set','B'))))))
check('set_extensionality_definitions',same(certificates['difference_empty'][1],impl(subset_formula(('set','S'),('set','L')),equality_formula(('diff',('set','S'),('set','L')),('empty',)))) and same(certificates['complement_disjoint'][1],equality_formula(('inter',('set','L'),('diff',('set','U'),('set','L'))),('empty',))) and same(certificates['complement_cover'][1],impl(subset_formula(('set','L'),('set','U')),equality_formula(('union',('set','L'),('diff',('set','U'),('set','L'))),('set','U')))))
check('no_capture',rejected(ue(h('all'),'y'),{'all':allf('x',exf('y',R('x','y')))},frozenset({'y'})))
check('no_invalid_generalization',rejected(ui('x',h('p')),{'p':P('x')}))
check('no_escaping_existential_witness',rejected(ee(h('ex'),'u','p',h('p')),{'ex':exf('x',P('x'))}))
check('no_existential_without_term',rejected(ei('x',impl(P('x'),P('x')),'u',ii('p',P('u'),h('p')))))
check('no_invalid_modus_ponens',rejected(ie(h('imp'),h('q')),{'imp':impl(P('x'),P('x')),'q':atom('Q','x')},frozenset({'x'})))
check('no_undeclared_rule',rejected(('modalE',h('modal')),{'modal':atom('M')}))
check('no_universal_to_existential_without_inhabitant',rejected(ii('all',allf('x',P('x')),ei('x',P('x'),'u',ue(h('all'),'u')))))
check('no_quantifier_swap',rejected(ii('surface',allf('x',exf('y',R('x','y'))),ei('y',allf('x',R('x','y')),'u',ui('x',ee(ue(h('surface'),'x'),'v','r',h('r')))))))
check('empty_domain_countermodel',all([]) and not any([]))
check('quantifier_swap_countermodel',all(any(x==y for y in (False,True)) for x in (False,True)) and not any(all(x==y for x in (False,True)) for y in (False,True)))
check('modal_existential_countermodel',any(True and (lambda p:True)(False) for x in (False,True)) and not any(True and False for x in (False,True)))
check('normal_modal_countermodel',any(True and any(False!=v and v==True for v in (False,True)) for student in (0,)) and not any(True and False==True for student in (0,)))
check('normal_possibility_preserves_false',all(not any(w!=v and False for v in (False,True)) for w in (False,True)))

def Woman(x):return atom('Woman',x)
def Coffee(x):return atom('Coffee',x)
def Tea(x):return atom('Tea',x)
coffee_rule=allf('x',impl(Woman('x'),disj(Coffee('x'),Tea('x'))))
coffee_witness=exf('x',conj(Woman('x'),neg(Coffee('x'))))
coffee_goal=exf('x',conj(Woman('x'),Tea('x')))
coffee_case=oe(ie(ue(h('all'),'u'),ae(h('w'))),'coffee',fi(Tea('u'),ie(be(h('w')),h('coffee'))),'tea',h('tea'))
coffee_proof=ii('all',coffee_rule,ii('some',coffee_witness,ee(h('some'),'u','w',ei('x',conj(Woman('x'),Tea('x')),'u',ai(ae(h('w')),coffee_case)))))
certificates['coffee_tea_full']=(coffee_proof,impl(coffee_rule,impl(coffee_witness,coffee_goal)))
check('coffee_tea_full',same(verify(coffee_proof),certificates['coffee_tea_full'][1]))

print(json.dumps({'backend':'Python 3','scope':'checked natural-deduction certificates with capture and eigenvariable conditions','checks':len(results),'passed':True,'results':results}))
