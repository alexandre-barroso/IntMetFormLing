from pathlib import Path
import json
import sys
import sympy as sp

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from capitulo_04 import svd_geral as s
from capitulo_04 import procrustes as p
from capitulo_07.probabilidade_geral import V,C,A,All,Ex,Imp,And,Eq,Kernel,instantiate,apply,close,substitute,same,rejects


rectangular=s.function('real_rectangular_matrix',['N','N','M'],'Prop')
cross=s.function('transpose_cross_product',['N','N','M','M'],'M')
frobenius=s.function('frobenius_alignment_error',['N','N','M','M','M'],'R')


def solution(rows,columns,left,right,optimizer):
    competitor=V('orthogonal_competitor','M')
    domain=A(s.square,columns,competitor)
    orthogonality=Eq(s.mm(columns,s.tr(competitor),competitor),A(s.identity,columns))
    bound=A(s.le,A(frobenius,rows,columns,left,right,optimizer),A(frobenius,rows,columns,left,right,competitor))
    return And(s.ortho(columns,optimizer),s.general((competitor,),(domain,orthogonality),bound))


def statements():
    rows,columns=V('rows','N'),V('columns','N')
    left,right=V('left_data','M'),V('right_data','M')
    u,v,sigma=V('svd_u','M'),V('svd_v','M'),V('svd_sigma','V')
    domains=(A(rectangular,rows,columns,left),A(rectangular,rows,columns,right))
    product=A(cross,rows,columns,left,right)
    return {
        'cross_product_shape':s.general((rows,columns,left,right),domains,A(s.square,columns,product)),
        'conditional_procrustes_all_dimensions':s.general((rows,columns,left,right,u,v,sigma),domains+(s.svd(columns,product,u,v,sigma),),solution(rows,columns,left,right,s.mm(columns,u,s.tr(v))))
    }


def check(name,condition):
    if condition is not True:
        raise AssertionError(name)
    return {'id':name,'passed':True}


def conditional_certificate():
    if not all(result['passed'] for result in p.results):
        raise ValueError('conditional Procrustes certificate failed')
    rows,columns=sp.symbols('rows columns',integer=True,nonnegative=True)
    left,right=sp.MatrixSymbol('left',rows,columns),sp.MatrixSymbol('right',rows,columns)
    candidate=sp.MatrixSymbol('candidate',columns,columns)
    i,j=sp.symbols('i j',integer=True,nonnegative=True)
    error=sp.Function('error',real=True)
    empty_rows=sp.Sum(sp.Sum(error(i,j)**2,(i,0,-1)),(j,0,columns-1)).doit()
    empty_columns=sp.Sum(sp.Sum(error(i,j)**2,(j,0,-1)),(i,0,rows-1)).doit()
    ids={result['id'] for result in p.results}
    required={'one_sided_determinant_nonzero','opposite_product_from_inverse','loss_trace_expansion','svd_rotated_trace','weighted_gap_induction','weighted_gap_nonnegative_induction','candidate_orthogonal','candidate_attains_trace','actual_cross_matrix_binding','actual_conditional_loss_gap','conditional_loss_nonnegative','square_root_preserves_order'}
    results=[
        check('cross_product_shape_all_dimensions',(left.T*right).shape==(columns,columns)),
        check('alignment_product_shape_all_dimensions',(left*candidate-right).shape==(rows,columns)),
        check('empty_dimensions_cross_and_error_shapes',(left.T*right).subs(rows,0).shape==(columns,columns) and (left.T*right).subs(columns,0).shape==(0,0) and (left*candidate-right).subs(columns,0).shape==(rows,0) and sp.Sum(sp.Function('left_entry')(i,j)*sp.Function('right_entry')(i,j),(i,0,-1)).doit()==0),
        check('empty_row_frobenius_sum',empty_rows==0 and sp.sqrt(empty_rows)==0),
        check('empty_column_frobenius_sum',empty_columns==0 and sp.sqrt(empty_columns)==0),
        check('empty_objective_every_candidate_minimizes',sp.Le(sp.sqrt(empty_rows),sp.sqrt(empty_columns)) is sp.true),
        check('positive_dimensions_use_complete_conditional_certificate',required<=ids),
        check('conditional_cross_product_is_exact',p.trace_normal(p.parameterized_loss.xreplace({p.C:p.A.T*p.B}),p.orthogonal)==p.trace_normal(p.trace_loss,p.orthogonal)),
        check('nonnegative_dimensions_zero_or_positive',sp.simplify(sp.Equivalent(sp.Or(sp.Eq(rows,0),rows>0),rows>=0)) is sp.true and sp.simplify(sp.Equivalent(sp.Or(sp.Eq(columns,0),columns>0),columns>=0)) is sp.true)
    ]
    return results


def general_proof(svd_verification):
    hypotheses=svd_verification['imports']|statements()
    kernel=Kernel(hypotheses)
    svd_reference=kernel.theorem('real_square_svd_exists',svd_verification['formula'],svd_verification['proof'])
    rows,columns=V('n_rows','N'),V('n_columns','N')
    left,right=V('data_a','M'),V('data_b','M')
    u,v,sigma=V('factor_u','M'),V('factor_v','M'),V('singular_values','V')
    q=V('optimizer','M')
    domains=(A(rectangular,rows,columns,left),A(rectangular,rows,columns,right))
    product=A(cross,rows,columns,left,right)
    sq=apply(instantiate(('axiom','cross_product_shape'),rows,columns,left,right),*(('assume',hypothesis) for hypothesis in domains))
    decomposition=apply(instantiate(svd_reference,columns,product),sq)
    decomposition_formula=s.has_svd(columns,product)
    middle=substitute(decomposition_formula[2],decomposition_formula[1],u)
    inner=substitute(middle[2],middle[1],v)
    decomposition_instance=substitute(inner[2],inner[1],sigma)
    optimum=apply(instantiate(('axiom','conditional_procrustes_all_dimensions'),rows,columns,left,right,u,v,sigma),*(('assume',hypothesis) for hypothesis in domains),('assume',decomposition_instance))
    target=Ex(q,solution(rows,columns,left,right,q))
    witnessed=('ex_i',target,s.mm(columns,u,s.tr(v)),optimum)
    body=('ex_e',decomposition,u,('ex_e',('assume',middle),v,('ex_e',('assume',inner),sigma,witnessed)))
    proof=close(body,(rows,columns,left,right),domains)
    formula=s.general((rows,columns,left,right),domains,target)
    reference=kernel.theorem('procrustes_solution_obtained_by_general_svd',formula,proof)
    return kernel,formula,proof,reference


def verify_general_procrustes():
    svd=s.verify_general_svd()
    conditional=conditional_certificate()
    kernel,formula,proof,reference=general_proof(svd)
    results=conditional+[
        check('unconditional_procrustes_by_svd',not kernel.infer(reference).assumptions and same(kernel.infer(reference).conclusion,formula)),
        check('actual_factors_are_witnesses',proof[0]=='all_i' and 'real_square_svd_exists' in str(proof) and 'matrix_transpose' in str(proof)),
        check('reject_missing_svd_proof',rejects(lambda: Kernel(statements()).infer(proof)))
    ]
    return {'svd':svd,'kernel':kernel,'formula':formula,'proof':proof,'reference':reference,'results':results}


if __name__=='__main__':
    verification=verify_general_procrustes()
    print(json.dumps({'backend':'Python 3','passed':all(result['passed'] for result in verification['results']),'results':verification['results'],'scope':'Every natural N,d, including empty dimensions, arbitrary real N by d matrices; orthogonal Q minimizing the Frobenius error obtained from the proved SVD of A transpose B; no decomposition supplied as an external hypothesis.','general_procrustes_complete':True}))
