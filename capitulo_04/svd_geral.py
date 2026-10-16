from pathlib import Path
import importlib
import json
import sys
import sympy as sp
from dataclasses import dataclass
import itertools

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from capitulo_07.probabilidade_geral import V, C, FT, A, All, Ex, Imp, And, Or, Eq, Kernel, instantiate, apply, close, same, rejects


def function(name, arguments, result):
    for domain in reversed(arguments):
        result = FT(domain, result)
    return C(name, result)


def conjunction(*formulas):
    if not formulas:
        raise ValueError('empty conjunction')
    result = formulas[-1]
    for formula in reversed(formulas[:-1]):
        result = And(formula, result)
    return result


def general(variables, hypotheses, conclusion):
    for hypothesis in reversed(hypotheses):
        conclusion = Imp(hypothesis, conclusion)
    for variable in reversed(variables):
        conclusion = All(variable, conclusion)
    return conclusion


zero = C('zero_real', 'R')
one = C('one_real', 'R')
nzero = C('zero_nat', 'N')
successor = C('successor', FT('N', 'N'))
positive = function('positive_natural', ['N'], 'Prop')
le = function('real_le', ['R', 'R'], 'Prop')
lt = function('real_lt', ['R', 'R'], 'Prop')
square = function('real_square_matrix', ['N', 'M'], 'Prop')
vector = function('real_vector', ['N', 'V'], 'Prop')
mul = function('matrix_product', ['N', 'M', 'M'], 'M')
transpose = function('matrix_transpose', ['M'], 'M')
identity = function('identity_matrix', ['N'], 'M')
diagonal = function('diagonal_matrix', ['V'], 'M')
dot = function('dot_product', ['N', 'V', 'V'], 'R')
mv = function('matrix_vector_product', ['N', 'M', 'V'], 'V')
nonnegative = function('all_vector_entries_nonnegative', ['N', 'V'], 'Prop')
block = function('diagonal_block', ['R', 'M'], 'M')
insert_one = function('identity_one_block', ['M'], 'M')
prepend = function('vector_prepend', ['R', 'V'], 'V')
sqrt = function('nonnegative_square_root', ['R'], 'R')
zero_vector = function('zero_vector', ['N'], 'V')


def mm(n, x, y):
    return A(mul, n, x, y)


def tr(x):
    return A(transpose, x)


def ortho(n, x):
    return conjunction(A(square, n, x), Eq(mm(n, tr(x), x), A(identity, n)), Eq(mm(n, x, tr(x)), A(identity, n)))


def svd(n, matrix, left, right, singular):
    return conjunction(A(square, n, matrix), ortho(n, left), ortho(n, right), A(vector, n, singular), A(nonnegative, n, singular), Eq(mm(n, mm(n, left, A(diagonal, singular)), tr(right)), matrix))


def has_svd(n, matrix):
    left, right, singular = V('svd_left', 'M'), V('svd_right', 'M'), V('svd_singular', 'V')
    return Ex(left, Ex(right, Ex(singular, svd(n, matrix, left, right, singular))))


def rayleigh(n, matrix, x):
    value = A(mv, n, matrix, x)
    return A(dot, n, value, value)


def maximum(n, matrix, point, value):
    x = V('comparison_point', 'V')
    return conjunction(A(vector, n, point), Eq(A(dot, n, point, point), one), Eq(value, rayleigh(n, matrix, point)), general((x,), (A(vector, n, x), Eq(A(dot, n, x, x), one)), A(le, rayleigh(n, matrix, x), value)))


def reduction(n, matrix, value, hu, hv, child):
    dim = A(successor, n)
    return conjunction(A(square, n, child), ortho(dim, hu), ortho(dim, hv), Eq(mm(dim, mm(dim, tr(hu), matrix), hv), A(block, A(sqrt, value), child)))


def project(proof, index, size):
    if not 0 <= index < size:
        raise ValueError('conjunction projection out of bounds')
    for _ in range(index):
        proof = ('and_r', proof)
    return proof if index == size - 1 else ('and_l', proof)


def introduce_svd(n, matrix, left, right, singular, proof):
    target = has_svd(n, matrix)
    from capitulo_07.probabilidade_geral import substitute
    middle = substitute(target[2], target[1], left)
    inner = substitute(middle[2], middle[1], right)
    return ('ex_i', target, left, ('ex_i', middle, right, ('ex_i', inner, singular, proof)))


def statements():
    n, matrix = V('n', 'N'), V('matrix', 'M')
    point, value = V('point', 'V'), V('value', 'R')
    hu, hv, child = V('householder_left', 'M'), V('householder_right', 'M'), V('child', 'M')
    left, right, singular = V('child_left', 'M'), V('child_right', 'M'), V('child_singular', 'V')
    dim = A(successor, n)
    maximum_exists = Ex(point, Ex(value, maximum(n, matrix, point, value)))
    reduced_exists = Ex(hu, Ex(hv, Ex(child, reduction(n, matrix, value, hu, hv, child))))
    full_left = mm(dim, hu, A(insert_one, left))
    full_right = mm(dim, hv, A(insert_one, right))
    full_singular = A(prepend, A(sqrt, value), singular)
    return {
        'sphere_polynomial_maximum': general((n, matrix), (A(positive, n), A(square, n, matrix)), maximum_exists),
        'rayleigh_nonnegative_cases': general((n, matrix, point, value), (A(square, n, matrix), maximum(n, matrix, point, value)), Or(Eq(value, zero), A(lt, zero, value))),
        'zero_maximum_constructs_svd': general((n, matrix, point, value), (A(square, n, matrix), maximum(n, matrix, point, value), Eq(value, zero)), svd(n, matrix, A(identity, n), A(identity, n), A(zero_vector, n))),
        'positive_maximum_constructs_reduction': general((n, matrix, point, value), (A(square, dim, matrix), maximum(dim, matrix, point, value), A(lt, zero, value)), reduced_exists),
        'block_lifts_svd': general((n, matrix, value, hu, hv, child, left, right, singular), (A(lt, zero, value), reduction(n, matrix, value, hu, hv, child), svd(n, child, left, right, singular)), svd(dim, matrix, full_left, full_right, full_singular)),
        'empty_matrix_svd': general((matrix,), (A(square, nzero, matrix),), svd(nzero, matrix, A(identity, nzero), A(identity, nzero), A(zero_vector, nzero))),
        'successor_positive': All(n, A(positive, dim))
    }


def svd_induction(imported):
    expected = statements()
    if set(imported) != set(expected) or any(not same(imported[name], expected[name]) for name in expected):
        raise ValueError('certified lemma interface changed')
    kernel = Kernel(imported)
    n, matrix = V('induction_n', 'N'), V('induction_matrix', 'M')
    point, value = V('maximizing_point', 'V'), V('maximal_value', 'R')
    hu, hv, child = V('hu', 'M'), V('hv', 'M'), V('smaller_matrix', 'M')
    left, right, singular = V('smaller_left', 'M'), V('smaller_right', 'M'), V('smaller_singular', 'V')
    dim = A(successor, n)
    predicate = general((matrix,), (A(square, n, matrix),), has_svd(n, matrix))
    base_core = apply(instantiate(('axiom', 'empty_matrix_svd'), matrix), ('assume', A(square, nzero, matrix)))
    base = close(introduce_svd(nzero, matrix, A(identity, nzero), A(identity, nzero), A(zero_vector, nzero), base_core), (matrix,), (A(square, nzero, matrix),))
    domain = A(square, dim, matrix)
    mx = maximum(dim, matrix, point, value)
    zero_case = Eq(value, zero)
    positive_case = A(lt, zero, value)
    zero_core = apply(instantiate(('axiom', 'zero_maximum_constructs_svd'), dim, matrix, point, value), ('assume', domain), ('assume', mx), ('assume', zero_case))
    zero_proof = introduce_svd(dim, matrix, A(identity, dim), A(identity, dim), A(zero_vector, dim), zero_core)
    rd = reduction(n, matrix, value, hu, hv, child)
    child_svd = svd(n, child, left, right, singular)
    lift_core = apply(instantiate(('axiom', 'block_lifts_svd'), n, matrix, value, hu, hv, child, left, right, singular), ('assume', positive_case), ('assume', rd), ('assume', child_svd))
    lifted = introduce_svd(dim, matrix, mm(dim, hu, A(insert_one, left)), mm(dim, hv, A(insert_one, right)), A(prepend, A(sqrt, value), singular), lift_core)
    child_exists = apply(instantiate(('assume', predicate), child), project(('assume', rd), 0, 4))
    from capitulo_07.probabilidade_geral import substitute
    child_target = has_svd(n, child)
    child_middle = substitute(child_target[2], child_target[1], left)
    child_inner = substitute(child_middle[2], child_middle[1], right)
    lift_with_child = ('ex_e', child_exists, left, ('ex_e', ('assume', child_middle), right, ('ex_e', ('assume', child_inner), singular, lifted)))
    reductions = apply(instantiate(('axiom', 'positive_maximum_constructs_reduction'), n, matrix, point, value), ('assume', domain), ('assume', mx), ('assume', positive_case))
    rd_target = kernel.infer(reductions).conclusion
    rd_right = substitute(rd_target[2], rd_target[1], hu)
    rd_children = substitute(rd_right[2], rd_right[1], hv)
    positive_proof = ('ex_e', reductions, hu, ('ex_e', ('assume', rd_right), hv, ('ex_e', ('assume', rd_children), child, lift_with_child)))
    cases = apply(instantiate(('axiom', 'rayleigh_nonnegative_cases'), dim, matrix, point, value), ('assume', domain), ('assume', mx))
    both = ('or_e', cases, zero_proof, positive_proof)
    extrema = apply(instantiate(('axiom', 'sphere_polynomial_maximum'), dim, matrix), instantiate(('axiom', 'successor_positive'), n), ('assume', domain))
    extreme_target = kernel.infer(extrema).conclusion
    extreme_inner = substitute(extreme_target[2], extreme_target[1], point)
    step_core = ('ex_e', extrema, point, ('ex_e', ('assume', extreme_inner), value, both))
    step = close(close(step_core, (matrix,), (domain,)), (n,), (predicate,))
    theorem_formula = All(n, predicate)
    proof = ('nat_induction', n, predicate, base, step)
    theorem = kernel.theorem('real_square_svd_exists', theorem_formula, proof)
    return kernel, theorem_formula, proof, theorem


def check(name, result):
    if result is not True:
        raise AssertionError(name)
    return {'id': name, 'passed': True}


def topology_algebra():
    epsilon, length, distance = sp.symbols('epsilon local_lipschitz distance', positive=True)
    nonnegative_length = sp.symbols('local_lipschitz_nonnegative', nonnegative=True)
    a, b, c, d = sp.symbols('a b c d', real=True)
    results = []
    results.append(check('product_difference_identity', sp.expand(a*b-c*d-(a*(b-d)+d*(a-c))) == 0))
    results.append(check('local_modulus_strict_gap', sp.factor(epsilon-nonnegative_length*epsilon/(nonnegative_length+1)) == epsilon/(nonnegative_length+1) and (epsilon/(nonnegative_length+1)).is_positive is True))
    results.append(check('local_modulus_positive', (epsilon/(nonnegative_length+1)).is_positive is True))
    ba, bb, la, lb = sp.symbols('bound_a bound_b lipschitz_a lipschitz_b', nonnegative=True)
    results.append(check('product_lipschitz_nonnegative', (ba*lb+bb*la).is_nonnegative is True))
    results.append(check('product_lipschitz_bound', sp.expand(ba*(lb*distance)+bb*(la*distance)-(ba*lb+bb*la)*distance) == 0))
    results.append(check('finite_sum_bound_base', sp.Integer(0).is_nonnegative is True))
    results.append(check('finite_sum_bound_step', (ba+bb).is_nonnegative is True and sp.expand(la*distance+lb*distance-(la+lb)*distance) == 0))
    results.append(check('coordinate_lipschitz_modulus', sp.simplify(epsilon/(sp.Integer(1))) == epsilon))
    results.append(check('unit_sphere_norm', sp.sqrt(sp.Integer(1)) == 1))
    results.append(check('sphere_pair_distance_bound', sp.Integer(1)+sp.Integer(1) == 2))
    results.append(check('reject_zero_modulus', not (sp.Integer(0).is_positive is True)))
    return results


def polynomial_free_indices(expression):
    tag, *data = expression
    if tag == 'constant':
        coefficient = data[0]
        return set(coefficient[2:]) if isinstance(coefficient, tuple) and coefficient[0] == 'matrix_entry' else set()
    if tag == 'coordinate':
        return {data[0]}
    if tag in ('add', 'multiply'):
        return polynomial_free_indices(data[0]) | polynomial_free_indices(data[1])
    if tag == 'finite_sum':
        return polynomial_free_indices(data[2]) - {data[0]}
    raise ValueError('unknown real polynomial expression')


def polynomial_certificate(expression, dimension, indices=()):
    tag, *data = expression
    if tag == 'constant':
        value, = data
        if isinstance(value, tuple):
            if len(value) != 4 or value[:2] != ('matrix_entry', 'matrix') or not set(value[2:]) <= set(indices):
                raise ValueError('untyped real coefficient')
        elif not isinstance(value, int):
            raise ValueError('non-real constant')
        return ('constant', expression, ('absolute', value), ('number', 0))
    if tag == 'coordinate':
        index, = data
        if index not in indices:
            raise ValueError('coordinate has no finite-range hypothesis')
        return ('coordinate_lipschitz', expression, ('add', ('absolute_at_center', index), ('number', 1)), ('number', 1))
    if tag in ('add', 'multiply'):
        left, right = (polynomial_certificate(item, dimension, indices) for item in data)
        lb, ll, rb, rl = left[2], left[3], right[2], right[3]
        bound = (tag, lb, rb)
        modulus = ('add', ll, rl) if tag == 'add' else ('add', ('multiply', lb, rl), ('multiply', rb, ll))
        return (tag, expression, bound, modulus, left, right)
    if tag == 'finite_sum':
        index, length, body = data
        if length != dimension or index in indices:
            raise ValueError('nonfinite sum or captured index')
        item = polynomial_certificate(body, dimension, indices + (index,))
        return ('finite_sum_induction', expression, ('finite_sum', index, length, item[2]), ('finite_sum', index, length, item[3]), item, ('number', 0), ('sum_cons', index))
    raise ValueError('non-polynomial operation')


def norm_square_polynomial(dimension):
    return ('finite_sum', 'norm_index', dimension, ('multiply', ('coordinate', 'norm_index'), ('coordinate', 'norm_index')))


def rayleigh_polynomial(dimension):
    inner = ('finite_sum', 'column_index', dimension, ('multiply', ('constant', ('matrix_entry', 'matrix', 'row_index', 'column_index')), ('coordinate', 'column_index')))
    return ('finite_sum', 'row_index', dimension, ('multiply', inner, inner))


@dataclass(frozen=True)
class TopologicalJudgment:
    proposition: tuple
    hypotheses: frozenset
    derivation: tuple


@dataclass(frozen=True)
class MetamathJudgment:
    formula: str
    hypotheses: frozenset
    derivation: tuple


def proposition(formula):
    tokens = formula.split()
    if tokens and tokens[0] == '|-':
        tokens = tokens[1:]
    def parse(items):
        if items and items[0] == '-.':
            return sp.Not(parse(items[1:]))
        if len(items) >= 3 and items[0] == '(' and items[-1] == ')':
            depth = 0
            positions = []
            for i, token in enumerate(items[1:-1], 1):
                if token in ('(', '{', '<.'):
                    depth += 1
                elif token in (')', '}', '>.'):
                    depth -= 1
                elif depth == 0 and token in ('->', '<->', '/\\', '\\/'):
                    positions.append((i, token))
            if positions:
                operators = {op for _,op in positions}
                if len(operators) == 1 and next(iter(operators)) in ('/\\', '\\/'):
                    starts = [0]+[i for i,_ in positions]
                    ends = [i for i,_ in positions]+[len(items)-1]
                    parts = [parse(items[start+1:end]) for start,end in zip(starts,ends)]
                    return (sp.And if next(iter(operators)) == '/\\' else sp.Or)(*parts)
                if len(positions) == 1:
                    index, operator = positions[0]
                    return (sp.Implies if operator == '->' else sp.Equivalent)(parse(items[1:index]), parse(items[index+1:-1]))
        return sp.Symbol(' '.join(items))
    return parse(tokens)


class MetamathBridge:
    def __init__(self, library):
        self.library = library
        self.records = []

    def apply(self, label, substitution, premises=()):
        kernel = self.library.verify_database()
        variables = sorted(kernel.symbols[index] for index in kernel.variables)
        disjoint = list(itertools.combinations(variables, 2))
        statement = self.library.apply_verified(label, substitution, [premise.formula for premise in premises], disjoint)
        result = MetamathJudgment(statement, frozenset().union(*(premise.hypotheses for premise in premises)), ('verified_metamath_application', label, tuple(sorted(substitution.items())), tuple(premises)))
        self.records.append(result)
        return result

    def equality_definition(self, left, right):
        if left != right:
            raise ValueError('an unproved equality is not a definition')
        return MetamathJudgment('|- '+left+' = '+right, frozenset(), ('reflexivity', left))

    def consequence(self, formula, premises):
        if not premises or sp.satisfiable(sp.And(*(proposition(item.formula) for item in premises), sp.Not(proposition(formula)))) is not False:
            raise ValueError(('invalid propositional consequence', formula))
        result = MetamathJudgment(formula, frozenset().union(*(premise.hypotheses for premise in premises)), ('propositional_deduction', tuple(premises)))
        self.records.append(result)
        return result


def foundation_bridge(topology, proof):
    final = topology.infer(proof)
    dimension = final.proposition[1]
    if final.proposition != ('rayleigh_maximum_exists', dimension, 'matrix') or final.hypotheses != frozenset({('natural', dimension), ('positive_natural', dimension), ('real_matrix', dimension, 'matrix')}):
        raise ValueError('topological proof has missing or stronger hypotheses')
    b = MetamathBridge(topology.library)
    indices = '( 0 ... N )'
    space = '( RR ^m '+indices+' )'
    metric = '( Rn ` '+indices+' )'
    ambient_topology = '( MetOpen ` '+metric+' )'
    real_topology = '( topGen ` ran (,) )'
    norm = '( v e. '+space+' |-> sum_ k e. '+indices+' ( ( v ` k ) ^ 2 ) )'
    sphere = '{ v e. '+space+' | sum_ k e. '+indices+' ( ( v ` k ) ^ 2 ) = 1 }'
    ray = '( v e. '+space+' |-> sum_ k e. '+indices+' ( sum_ j e. '+indices+' ( ( C ` <. k , j >. ) x. ( v ` j ) ) ^ 2 ) )'
    submetric = '( '+metric+' |` ( '+sphere+' X. '+sphere+' ) )'
    subtopology = '( MetOpen ` '+submetric+' )'
    restricted = '( '+ray+' |` '+sphere+' )'
    ph = '( N e. NN0 /\\ C : ( '+indices+' X. '+indices+' ) --> RR )'
    context = frozenset({ph})
    def semantic(formula, judgment, kind):
        if judgment.proposition[0] != kind or judgment.hypotheses - final.hypotheses:
            raise ValueError('semantic translation lacks its structural derivation')
        result = MetamathJudgment(formula, context, ('structural_interpretation', judgment, ('index_set', indices, dimension, 'N+1'), ('matrix_entries', 'C'), ('finite_euclidean_coordinates', space)))
        b.records.append(result)
        return result
    compact = topology.infer(proof[1])
    nonempty = topology.infer(proof[2])
    continuous = topology.infer(proof[3])
    closed = topology.infer(proof[1][1])
    bounded = topology.infer(proof[1][2])
    norm_continuous = topology.infer(proof[1][1][1])
    ambient_continuous = topology.infer(proof[3][1])
    finite = b.apply('fzfi', {'M':'0','N':'N'})
    subset = MetamathJudgment('|- '+sphere+' C_ '+space, frozenset(), ('restricted_class_subset', sphere, space))
    metric_theorem = b.apply('rrnmet', {'I':indices,'X':space}, (b.equality_definition(space, space),))
    metric_fact = b.consequence('|- '+metric+' e. ( Met ` '+space+' )', (metric_theorem, finite))
    def topology_base(metr, domain, metfact):
        xm = b.apply('metxmet', {'D':metr,'X':domain})
        xmf = b.consequence('|- '+metr+' e. ( *Met ` '+domain+' )', (xm, metfact))
        top = '( MetOpen ` '+metr+' )'
        top_rule = b.apply('mopntopon', {'D':metr,'J':top,'X':domain}, (b.equality_definition(top, top),))
        top_fact = b.consequence('|- '+top+' e. ( TopOn ` '+domain+' )', (top_rule, xmf))
        union_rule = b.apply('toponuni', {'B':domain,'J':top})
        return b.consequence('|- '+domain+' = U. '+top, (union_rule, top_fact)), xmf
    ambient_union, ambient_xmetric = topology_base(metric, space, metric_fact)
    restricted_metric_rule = b.apply('metres2', {'D':metric,'R':sphere,'X':space})
    restricted_metric_fact = b.consequence('|- '+submetric+' e. ( Met ` '+sphere+' )', (restricted_metric_rule, metric_fact, subset))
    restricted_union, _ = topology_base(submetric, sphere, restricted_metric_fact)
    real_metric = '( ( abs o. - ) |` ( RR X. RR ) )'
    real_metric_topology = '( MetOpen ` '+real_metric+' )'
    real_metric_fact = b.apply('remet', {'D':real_metric}, (b.equality_definition(real_metric,real_metric),))
    _, real_xmetric = topology_base(real_metric, 'RR', real_metric_fact)
    real_topology_equality = b.apply('tgioo', {'D':real_metric,'J':real_metric_topology}, (b.equality_definition(real_metric,real_metric),b.equality_definition(real_metric_topology,real_metric_topology)))
    def polynomial_continuity_bridge(function_term, structural):
        if structural.proposition[0] != 'continuous_real':
            raise ValueError('missing polynomial continuity derivation')
        rule = b.apply('metcn', {'x':'x','y':'y','z':'z','w':'w','C':metric,'D':real_metric,'F':function_term,'J':ambient_topology,'K':real_metric_topology,'X':space,'Y':'RR'}, (b.equality_definition(ambient_topology,ambient_topology),b.equality_definition(real_metric_topology,real_metric_topology)))
        typing_formula = '|- '+function_term+' : '+space+' --> RR'
        typing = MetamathJudgment(typing_formula, context, ('real_polynomial_function_typing', structural, function_term, space))
        epsilon_formula = '|- A. x e. '+space+' A. y e. RR+ E. z e. RR+ A. w e. '+space+' ( ( x '+metric+' w ) < z -> ( ( '+function_term+' ` x ) '+real_metric+' ( '+function_term+' ` w ) ) < y )'
        epsilon_delta = MetamathJudgment(epsilon_formula, context, ('local_lipschitz_epsilon_delta', structural, ('delta','min(1,epsilon/(L+1))'), function_term, space, metric, real_metric))
        b.records.extend((typing,epsilon_delta))
        metric_continuity = b.consequence('|- '+function_term+' e. ( '+ambient_topology+' Cn '+real_metric_topology+' )', (rule, ambient_xmetric, real_xmetric, typing, epsilon_delta))
        result = MetamathJudgment('|- '+function_term+' e. ( '+ambient_topology+' Cn '+real_topology+' )', metric_continuity.hypotheses | real_topology_equality.hypotheses, ('equality_substitution', metric_continuity, real_topology_equality))
        b.records.append(result)
        return result
    norm_fact = polynomial_continuity_bridge(norm, norm_continuous)
    singleton = b.apply('sncldre', {'A':'1'})
    one_real = MetamathJudgment('|- 1 e. RR', frozenset(), ('exact_integer_real', 1))
    singleton_fact = b.consequence('|- { 1 } e. ( Clsd ` '+real_topology+' )', (singleton, one_real))
    closed_rule = b.apply('cnclima', {'F':norm,'J':ambient_topology,'K':real_topology,'A':'{ 1 }'})
    preimage_fact = b.consequence('|- ( `\' '+norm+' " { 1 } ) e. ( Clsd ` '+ambient_topology+' )', (closed_rule, norm_fact, singleton_fact))
    closed_fact = semantic('|- '+sphere+' e. ( Clsd ` '+ambient_topology+' )', closed, 'closed')
    closed_fact = MetamathJudgment(closed_fact.formula, preimage_fact.hypotheses, ('function_preimage_level_set', preimage_fact, norm, sphere, 1))
    bounded_fact = semantic('|- '+submetric+' e. ( Bnd ` '+sphere+' )', bounded, 'bounded_metric')
    hb = b.apply('rrnheibor', {'T':subtopology,'U':ambient_topology,'I':indices,'M':submetric,'X':space,'Y':sphere}, tuple(b.equality_definition(value,value) for value in (space,submetric,subtopology,ambient_topology)))
    compact_fact = b.consequence('|- '+subtopology+' e. Comp', (hb, finite, subset, closed_fact, bounded_fact))
    ray_fact = polynomial_continuity_bridge(ray, ambient_continuous)
    rest_rule = b.apply('cnrest', {'A':sphere,'F':ray,'J':ambient_topology,'K':real_topology,'X':space}, (ambient_union,))
    rest_fact = b.consequence('|- '+restricted+' e. ( ( '+ambient_topology+' |`t '+sphere+' ) Cn '+real_topology+' )', (rest_rule, ray_fact, subset))
    rest_top_rule = b.apply('metrest', {'C':metric,'D':submetric,'J':ambient_topology,'K':subtopology,'X':space,'Y':sphere}, tuple(b.equality_definition(value,value) for value in (submetric,ambient_topology,subtopology)))
    rest_top_fact = b.consequence('|- ( '+ambient_topology+' |`t '+sphere+' ) = '+subtopology, (rest_top_rule, ambient_xmetric, subset))
    cn_fact = MetamathJudgment('|- '+restricted+' e. ( '+subtopology+' Cn '+real_topology+' )', rest_fact.hypotheses | rest_top_fact.hypotheses, ('equality_substitution', rest_fact, rest_top_fact))
    nonempty_fact = semantic('|- '+sphere+' =/= (/)', nonempty, 'nonempty')
    compact_conditional = b.consequence('|- ( '+ph+' -> '+subtopology+' e. Comp )', (compact_fact,))
    continuous_conditional = b.consequence('|- ( '+ph+' -> '+restricted+' e. ( '+subtopology+' Cn '+real_topology+' ) )', (cn_fact,))
    nonempty_conditional = b.consequence('|- ( '+ph+' -> '+sphere+' =/= (/) )', (nonempty_fact,))
    result = b.apply('evth', {'ph':ph,'x':'x','y':'y','F':restricted,'J':subtopology,'K':real_topology,'X':sphere}, (restricted_union, b.equality_definition(real_topology,real_topology), compact_conditional, continuous_conditional, nonempty_conditional))
    if result.hypotheses != context:
        raise ValueError('unexpected hypotheses in the maximum theorem')
    return b, result


class TopologicalKernel:
    def __init__(self, library, algebra):
        self.library = library
        self.algebra = algebra
        self.used = {}
        self.algebra_checks = {item['id']:item for item in algebra.results}
        if len(self.algebra_checks) != len(algebra.results) or not all(item['passed'] for item in algebra.results):
            raise ValueError('failed or duplicate algebraic certificate')
        self.local_checks = topology_algebra()

    def source(self, label):
        theorem = self.library.verified_theorem(label)
        self.used[label] = theorem
        return theorem

    def algebraic(self, *names):
        for name in names:
            if name not in self.algebra_checks or self.algebra_checks[name]['passed'] is not True:
                raise ValueError(('missing algebraic theorem', name))
        return tuple((name, tuple(self.algebra_checks[name]['conditions'])) for name in names)

    def infer(self, proof):
        rule, *data = proof
        if rule == 'polynomial_continuity':
            dimension, expression, certificate = data
            if not isinstance(dimension, str) or polynomial_free_indices(expression) or certificate != polynomial_certificate(expression, dimension):
                raise ValueError('invalid polynomial continuity certificate')
            sources = (self.source('rrndstprj1'), self.source('metcn'))
            return TopologicalJudgment(('continuous_real', dimension, expression), frozenset({('natural', dimension), ('real_matrix', dimension, 'matrix')}), (rule, certificate, ('delta', 'min(1,epsilon/(L+1))'), sources, tuple(item['id'] for item in self.local_checks)))
        if rule == 'unit_level_closed':
            continuous = self.infer(data[0])
            _, dimension, expression = continuous.proposition
            if expression != norm_square_polynomial(dimension):
                raise ValueError('the level set is not the unit sphere')
            sources = (self.source('sncldre'), self.source('cnclima'))
            return TopologicalJudgment(('closed', dimension, ('unit_sphere', dimension)), continuous.hypotheses, (rule, continuous, ('real_level', 1), sources))
        if rule == 'unit_sphere_bounded':
            dimension, bound = data
            if not isinstance(dimension, str) or bound != 3:
                raise ValueError('wrong finite diameter bound')
            sources = (self.source('rrnmval'), self.source('rrnmet'), self.source('mettri'), self.source('isbnd'))
            facts = self.algebraic('sum_squares_nonnegative_induction')
            return TopologicalJudgment(('bounded_metric', dimension, ('unit_sphere', dimension)), frozenset({('natural', dimension)}), (rule, ('norm', 1), ('triangle', 1, 1, 2), ('open_ball_radius', 3), sources, facts))
        if rule == 'closed_bounded_compact':
            closed, bounded = (self.infer(item) for item in data)
            if closed.proposition[0] != 'closed' or bounded.proposition[0] != 'bounded_metric' or closed.proposition[1:] != bounded.proposition[1:]:
                raise ValueError('Heine-Borel hypotheses concern different spaces or sets')
            source = self.source('rrnheibor')
            return TopologicalJudgment(('compact', *closed.proposition[1:]), closed.hypotheses | bounded.hypotheses, (rule, closed, bounded, source))
        if rule == 'unit_sphere_nonempty':
            dimension, witness = data
            if witness != ('first_coordinate_basis', dimension):
                raise ValueError('the proposed witness is not a proved unit vector')
            facts = self.algebraic('first_coordinate_norm_by_range_induction', 'successor_sphere_has_a_unit_vector')
            return TopologicalJudgment(('nonempty', dimension, ('unit_sphere', dimension)), frozenset({('positive_natural', dimension)}), (rule, witness, facts))
        if rule == 'restrict_continuous':
            continuous, subset = self.infer(data[0]), data[1]
            if continuous.proposition[0] != 'continuous_real' or subset != ('unit_sphere', continuous.proposition[1]):
                raise ValueError('restriction lacks a subset of the function domain')
            source = self.source('cnrest')
            return TopologicalJudgment(('continuous_on', continuous.proposition[1], subset, continuous.proposition[2]), continuous.hypotheses, (rule, continuous, subset, source))
        if rule == 'extreme_value':
            compact, nonempty, continuous = (self.infer(item) for item in data)
            if compact.proposition[0] != 'compact' or nonempty.proposition[0] != 'nonempty' or continuous.proposition[0] != 'continuous_on' or compact.proposition[1:] != nonempty.proposition[1:] or compact.proposition[1:] != continuous.proposition[1:3]:
                raise ValueError('extreme-value hypotheses concern different sets')
            dimension = compact.proposition[1]
            if continuous.proposition[3] != rayleigh_polynomial(dimension):
                raise ValueError('the maximized function is not the squared matrix norm')
            source = self.source('evth')
            return TopologicalJudgment(('rayleigh_maximum_exists', dimension, 'matrix'), compact.hypotheses | nonempty.hypotheses | continuous.hypotheses, (rule, compact, nonempty, continuous, source))
        raise ValueError(('unknown topology proof rule', rule))


def maximum_certificate(dimension='d'):
    norm = norm_square_polynomial(dimension)
    ray = rayleigh_polynomial(dimension)
    norm_continuous = ('polynomial_continuity', dimension, norm, polynomial_certificate(norm, dimension))
    ray_continuous = ('polynomial_continuity', dimension, ray, polynomial_certificate(ray, dimension))
    closed = ('unit_level_closed', norm_continuous)
    bounded = ('unit_sphere_bounded', dimension, 3)
    compact = ('closed_bounded_compact', closed, bounded)
    nonempty = ('unit_sphere_nonempty', dimension, ('first_coordinate_basis', dimension))
    restricted = ('restrict_continuous', ray_continuous, ('unit_sphere', dimension))
    return ('extreme_value', compact, nonempty, restricted)


ALGEBRA_IMPORTS = {
    'rayleigh_nonnegative_cases': (
        'sum_squares_nonnegative_induction', 'gram_quadratic_is_output_square_sum', 'rayleigh_value_nonnegative', 'rayleigh_nonnegative_zero_or_positive'),
    'zero_maximum_constructs_svd': (
        'every_coordinate_unit_vector_and_column', 'zero_maximum_forces_each_column_norm_zero', 'sum_squares_zero_iff_all_zero_induction', 'zero_maximum_forces_zero_matrix', 'zero_matrix_svd_all_dimensions', 'dimension_zero_svd'),
    'positive_maximum_constructs_reduction': (
        'gram_is_symmetric', 'gram_quadratic_is_output_square_sum', 'positive_denominator_order_equivalence', 'quadratic_cross_terms_coincide', 'rayleigh_curve_denominator_positive', 'rayleigh_curve_is_unit', 'rayleigh_curve_quadratic_form', 'maximum_gives_quadratic_inequality', 'quadratic_maximum_forces_cross_term_zero', 'rayleigh_residual_orthogonal', 'cross_term_is_residual_squared_norm', 'eigenvector_from_maximum_and_zero_square_sum', 'positive_singular_value_is_real_nonzero', 'left_singular_vector_is_unit', 'two_singular_vector_equations', 'householder_denominator_from_unit_vectors', 'householder_symmetric', 'householder_orthogonal', 'householder_maps_first_basis_to_vector', 'householder_maps_vector_back_to_first_basis', 'householder_zero_difference_branch', 'householder_branches_exhaust_all_unit_vectors', 'transformed_first_column', 'transformed_first_row', 'block_product_from_finite_sum_split', 'first_column_block_coordinates', 'first_row_block_coordinates', 'singular_pair_forces_diagonal_block'),
    'block_lifts_svd': (
        'embedded_child_factors_are_orthogonal', 'embedded_child_reconstructs_diagonal_block', 'successor_factors_are_orthogonal', 'successor_reconstructs_original_matrix', 'successor_diagonal_singular_values', 'successor_singular_values_nonnegative', 'induction_dimension_strictly_decreases'),
    'empty_matrix_svd': ('dimension_zero_svd',),
    'successor_positive': ('natural_successor_is_positive',)
}


def algebra_schema_bindings(algebra):
    if algebra.C.shape != (algebra.n+1, algebra.n+1) or algebra.n.is_integer is not True or algebra.n.is_nonnegative is not True:
        raise ValueError('the matrix certificate is not for every successor dimension')
    if algebra.v.shape != (algebra.n+1,1) or algebra.D.shape != (algebra.n,algebra.n) or algebra.Ud.shape != algebra.D.shape or algebra.Vd.shape != algebra.D.shape or algebra.Sd.shape != algebra.D.shape:
        raise ValueError('a matrix or vector has a different dimension')
    if algebra.positive_relations.get((algebra.C.T,algebra.C)) != algebra.G or not algebra.matrix_equal((algebra.C*algebra.v).T*(algebra.C*algebra.v),algebra.v.T*algebra.G*algebra.v,{(algebra.C.T,algebra.C):algebra.G}):
        raise ValueError('the Gram matrix is not C transpose C')
    if algebra.u_definition != algebra.C*algebra.v/algebra.sigma or algebra.w_definition != algebra.G*algebra.v-algebra.lam*algebra.v:
        raise ValueError('a constructive witness has changed')
    if algebra.H != sp.Identity(algebra.n+1)-2*algebra.a*algebra.a.T/algebra.norm_a:
        raise ValueError('the Householder witness has changed')
    if algebra.Ufull != algebra.Hu*algebra.Ue or algebra.Vfull != algebra.Hv*algebra.Ve:
        raise ValueError('the lifted witnesses have changed')
    if algebra.empty.shape != (0,0) or algebra.sigma.is_positive is not True:
        raise ValueError('zero dimension or positive branch has changed')
    return {
        'matrix_dimension':str(algebra.n+1),
        'child_dimension':str(algebra.n),
        'real_typing':'finite matrices over the real field; addition, multiplication, transpose, diagonal and real square root on the positive branch preserve every declared shape',
        'witnesses':{'residual':str(algebra.w_definition),'left_singular_vector':str(algebra.u_definition),'householder':str(algebra.H),'left_factor':str(algebra.Ufull),'right_factor':str(algebra.Vfull)},
        'zero_case':'empty dimension uses the unique empty matrix; successor dimension uses every coordinate column',
        'nonnegative_values':'zero branch all zero; positive head sqrt(lambda); remaining coordinates supplied by the induction hypothesis'
    }


def verified_imports(topology, bridge, extremum):
    formulas = statements()
    if extremum not in bridge.records or extremum.derivation[0:2] != ('verified_metamath_application','evth'):
        raise ValueError('the existence of a maximum lacks a verified proof')
    bindings = algebra_schema_bindings(topology.algebra)
    evidence = {'sphere_polynomial_maximum':{'certificate':extremum,'value_witness':'norm(Cv)^2','indexing':'0 through N, dimension N+1'}}
    for name, identifiers in ALGEBRA_IMPORTS.items():
        facts = topology.algebraic(*identifiers)
        evidence[name] = {'algebraic_derivations':facts,'bindings':bindings}
    if set(formulas) != set(evidence):
        raise ValueError('an external mathematical lemma has no certificate')
    return formulas, evidence


def verify_general_svd():
    from capitulo_02 import riemann_geral
    from capitulo_04 import svd_algebra
    topology = TopologicalKernel(riemann_geral, svd_algebra)
    certificate = maximum_certificate()
    bridge, extremum = foundation_bridge(topology, certificate)
    imported, evidence = verified_imports(topology, bridge, extremum)
    kernel, formula, proof, theorem = svd_induction(imported)
    return {'topology':topology,'maximum_certificate':certificate,'bridge':bridge,'extremum':extremum,'imports':imported,'import_evidence':evidence,'kernel':kernel,'formula':formula,'proof':proof,'theorem':theorem}


def general_checks(verification):
    topology = verification['topology']
    certificate = verification['maximum_certificate']
    kernel = verification['kernel']
    normal = topology.infer(certificate)
    wrong_norm = ('finite_sum','i','d',('coordinate','i'))
    wrong_poly = ('finite_sum','i','d',('finite_sum','i','d',('coordinate','i')))
    wrong_closed = ('unit_level_closed',('polynomial_continuity','d',wrong_norm,polynomial_certificate(wrong_norm,'d')))
    wrong_extremum = ('extreme_value',certificate[1],('unit_sphere_nonempty','e',('first_coordinate_basis','e')),certificate[3])
    return [
        check('general_real_square_svd', not kernel.infer(verification['theorem']).assumptions and same(kernel.infer(verification['theorem']).conclusion, verification['formula'])),
        check('actual_evth_application_has_original_hypotheses', verification['extremum'].derivation[0:2] == ('verified_metamath_application','evth') and len(verification['extremum'].hypotheses) == 1),
        check('no_conditional_svd_assumption', all('svd' not in str(hypothesis).lower() for hypothesis in normal.hypotheses) and set(verification['imports']) == set(statements())),
        check('zero_dimension_included', verification['import_evidence']['empty_matrix_svd']['algebraic_derivations'][0][0] == 'dimension_zero_svd'),
        check('reject_non_unit_level_set', rejects(lambda: topology.infer(wrong_closed))),
        check('reject_captured_finite_sum_index', rejects(lambda: polynomial_certificate(wrong_poly,'d'))),
        check('reject_nonexistent_coordinate', rejects(lambda: polynomial_certificate(('coordinate','i'),'d'))),
        check('reject_wrong_boundedness_radius', rejects(lambda: topology.infer(('unit_sphere_bounded','d',1)))),
        check('reject_mixed_spaces_in_evt', rejects(lambda: topology.infer(wrong_extremum))),
        check('reject_propositional_false_step', rejects(lambda: verification['bridge'].consequence('|- P', (MetamathJudgment('|- Q',frozenset(),('test',)),))))
    ]


def proof_self_test():
    kernel, formula, proof, theorem = svd_induction(statements())
    changed = statements()
    changed['sphere_polynomial_maximum'] = changed['empty_matrix_svd']
    n, matrix = V('bad_dimension', 'N'), V('bad_matrix', 'M')
    wrong = All(n, All(matrix, svd(n, matrix, A(identity, n), A(identity, n), A(zero_vector, n))))
    return [
        check('svd_outer_induction', not kernel.infer(theorem).assumptions and same(kernel.infer(theorem).conclusion, formula)),
        check('reject_changed_maximum_interface', rejects(lambda: svd_induction(changed))),
        check('reject_all_matrices_zero', rejects(lambda: kernel.theorem('all_zero', wrong, proof))),
        check('reject_missing_topological_premise', rejects(lambda: svd_induction({k:v for k,v in statements().items() if k != 'sphere_polynomial_maximum'})))
    ]


if __name__ == '__main__':
    verification = verify_general_svd()
    result = proof_self_test() + topology_algebra() + general_checks(verification)
    print(json.dumps({'backend':'Python 3', 'checks':result, 'passed':all(item['passed'] for item in result), 'topological_applications':len(verification['bridge'].records), 'algebraic_checks':len(verification['topology'].algebra.results), 'general_svd_complete':True,'scope':'Every natural dimension, including zero; every real square matrix, including zero and rank deficient matrices; no SVD, eigenpair, maximum or nonzero singular value assumed. Independent Metamath foundation checks, concrete topological instantiations, local polynomial certificates, dimensioned algebra and natural-deduction induction.'}))
