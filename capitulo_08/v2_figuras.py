import json
import sympy as sp


def main():
    checks = []
    def check(name, expression):
        if not bool(expression):
            raise AssertionError(name)
        checks.append(name)
    u, v, a, b, eta = sp.symbols('u v a b eta', real=True)
    responses = (233, 204, 242, 130, 112, 142)
    check('F11_group_sufficient_statistics',len(responses[:3])==len(responses[3:])==3 and sum(responses[:3])==679 and sum(responses[3:])==384)
    loss = sum((y-a)**2 for y in responses[:3]) + sum((y-a-b)**2 for y in responses[3:])
    check('F11_response_loss_expansion',sp.expand(loss-(6*a**2+6*a*b+3*b**2-2126*a-768*b+sum(y**2 for y in responses)))==0)
    excess = 3*u**2+3*(u+v)**2
    shifted = loss.subs({a:u+sp.Rational(679,3), b:v-sp.Rational(295,3)})-sp.Rational(3734,3)
    check('F11_general_loss_centering', sp.expand(shifted-excess)==0)
    check('F11_optimum_sum', sp.Rational(679,3)-sp.Rational(295,3)==128)
    check('F11_shifted_second_predictor', sp.expand(a+b-128-((a-sp.Rational(679,3))+(b+sp.Rational(295,3))))==0)
    check('F11_unique_zero_squares', sp.solve([u,u+v], [u,v])=={u:0,v:0})
    g = sp.Matrix([sp.diff(excess,u), sp.diff(excess,v)])
    check('F11_gradient', g==sp.Matrix([12*u+6*v,6*u+6*v]))
    new = excess.subs({u:u-eta*g[0],v:v-eta*g[1]}, simultaneous=True)
    qg = excess.subs({u:g[0],v:g[1]}, simultaneous=True)
    check('F11_arbitrary_step_exact_identity', sp.expand(new-excess+eta*g.dot(g)-eta**2*qg)==0)
    A,B,H = sp.symbols('A B H', positive=True)
    check('F11_descent_under_exact_positive_bound', sp.simplify((-eta*A+eta**2*B).subs({eta:A/(B+H)})) == -A**2*H/(B+H)**2)
    point={u:-8,v:14}
    gp=g.subs(point)
    check('F11_plotted_point_and_gradient', excess.subs(point)==300 and gp==sp.Matrix([-12,36]) and gp.dot(gp)==1440)
    step=8/sp.sqrt(1440)
    direction=step*gp
    check('F11_step_length',sp.simplify(direction.dot(direction))==64)
    check('F11_step_direction_alignment',sp.simplify(direction[0]*gp[1]-direction[1]*gp[0])==0 and sp.simplify(direction.dot(gp))>0)
    check('F11_plotted_descent_condition', 0<step<sp.Rational(2,3))
    check('F11_plotted_endpoint', sp.simplify((new-excess).subs(point).subs(eta,step))<0)
    z,p,y,alpha=sp.symbols('z p y alpha', real=True)
    check('zero_context_no_update', sp.expand(z-alpha*(p-y)*0)==z)
    n,dk,dv=sp.symbols('n dk dv', integer=True, positive=True)
    Q,K,V=sp.MatrixSymbol('Q',n,dk),sp.MatrixSymbol('K',n,dk),sp.MatrixSymbol('V',n,dv)
    weights=sp.MatrixSymbol('weights',n,n)
    check('F10_symbolic_dimensions', (Q*K.T/sp.sqrt(dk)).shape==(n,n) and (weights*V).shape==(n,dv))
    source_word,target_word='intention','execution'
    route=((0,0),(1,0),(2,1),(3,2),(4,3),(5,4),(5,5),(6,6),(7,7),(8,8),(9,9))
    check('F09_all_path_adjacencies',all((end[0]-start[0],end[1]-start[1]) in ((1,0),(0,1),(1,1)) for start,end in zip(route,route[1:])))
    route_cost=0
    for start,end in zip(route,route[1:]):
        di,dj=end[0]-start[0],end[1]-start[1]
        check('F09_step_'+str(end),(di,dj) in ((1,0),(0,1),(1,1)))
        route_cost+=(0 if source_word[end[0]-1]==target_word[end[1]-1] else 2) if di==dj==1 else 1
    check('F09_complete_path_cost',route[0]==(0,0) and route[-1]==(9,9) and route_cost==8)
    print(json.dumps({'passed':True,'checks':len(checks),'results':checks,'scope':'Internally specified responses and gradient step; exact symbolic identities for all real offsets and steps, conditional descent with an explicit bound, exact radical comparison for the selected endpoint, dimensions for arbitrary positive integer sizes.'}))


if __name__=='__main__':
    main()
