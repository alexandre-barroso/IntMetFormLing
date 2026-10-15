import json
import sys
from pathlib import Path
import sympy as sp

SCRIPTS_ROOT = Path(__file__).resolve().parents[1]
if str(SCRIPTS_ROOT) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_ROOT))
from capitulo_07.probabilidade_geral import *

NCAST = C('natural_real_embedding', FT('N', 'R'))
NADD = C('natural_add', FT('N', FT('N', 'N')))
NMUL = C('natural_mul', FT('N', FT('N', 'N')))
NFLOOR = C('nonnegative_floor', FT('R', 'N'))
RMIN = C('real_min', FT('R', FT('R', 'R')))
DYADIC = C('dyadic_natural', FT('N', 'N'))
GRID = C('upper_level_grid', FT(FUNCTION, FT('R', FT('N', SIMPLE))))
TWO = Add(RONE, RONE)


def cast(n):
    return A(NCAST, n)


def minimum(a, b):
    return A(RMIN, a, b)


def floor_value(x):
    return cast(A(NFLOOR, x))


def qvalue(n):
    return cast(A(DYADIC, n))


def cap(n):
    return A(NMUL, A(DYADIC, n), A(DYADIC, n))


def grid(f, q, m):
    return A(GRID, f, q, m)


def upper_levels_in(f, family):
    level = V('canonical_upper_level', 'R')
    return All(level, A(family, upper_level(f, level)))


def approximation(f):
    n = V('canonical_stage', 'N')
    return Lam(n, grid(f, qvalue(n), cap(n)))


def clipped(q, m, x):
    return Div(minimum(cast(m), floor_value(Mul(q, x))), q)


def canonical_scalar(n, x):
    return clipped(qvalue(n), cap(n), x)


def foundations():
    a, b, c, d, x, q = (V(name, 'R') for name in ('fa', 'fb', 'fc', 'fd', 'fx', 'fq'))
    n, m, j = (V(name, 'N') for name in ('fn', 'fm', 'fj'))
    f = V('foundation_function', FUNCTION)
    sn = A(SUCCESSOR, n)
    fq = floor_value(x)
    return {
        'embedding_zero': Eq(cast(NZERO), RZERO),
        'embedding_successor': All(n, Eq(cast(sn), Add(cast(n), RONE))),
        'embedding_add': alls((n, m), Eq(cast(A(NADD, n, m)), Add(cast(n), cast(m)))),
        'embedding_multiply': alls((n, m), Eq(cast(A(NMUL, n, m)), Mul(cast(n), cast(m)))),
        'embedding_nonnegative': All(n, Le(RZERO, cast(n))),
        'natural_below_zero': All(n, Imp(A(NLE, n, NZERO), Eq(n, NZERO))),
        'natural_below_successor_cases': alls((n, m), Imp(A(NLE, n, A(SUCCESSOR, m)), Or(A(NLE, n, m), Eq(n, A(SUCCESSOR, m))))),
        'real_archimedean_embedding': All(b, Ex(n, Lt(b, cast(n)))),
        'floor_lower': All(x, Imp(Le(RZERO, x), Le(fq, x))),
        'floor_upper_strict': All(x, Imp(Le(RZERO, x), Lt(x, Add(fq, RONE)))),
        'floor_integer_lower': alls((n, x), imps((Le(RZERO, x), Le(cast(n), x)), Le(cast(n), fq))),
        'floor_successor_upper': alls((n, x), imps((Le(RZERO, x), Lt(x, cast(A(SUCCESSOR, n)))), Le(fq, cast(n)))),
        'minimum_left': alls((a, b), Imp(Le(a, b), Eq(minimum(a, b), a))),
        'minimum_right': alls((a, b), Imp(Le(b, a), Eq(minimum(a, b), b))),
        'minimum_bound_left': alls((a, b), Le(minimum(a, b), a)),
        'minimum_bound_right': alls((a, b), Le(minimum(a, b), b)),
        'minimum_greatest_lower': alls((a, b, c), imps((Le(c, a), Le(c, b)), Le(c, minimum(a, b)))),
        'strict_implies_order': alls((a, b), Imp(Lt(a, b), Le(a, b))),
        'order_strict_transitive': alls((a, b, c), imps((Le(a, b), Lt(b, c)), Lt(a, c))),
        'strict_order_transitive': alls((a, b, c), imps((Lt(a, b), Le(b, c)), Lt(a, c))),
        'strict_transitive': alls((a, b, c), imps((Lt(a, b), Lt(b, c)), Lt(a, c))),
        'strict_from_not_order': alls((a, b), Imp(Imp(Le(a, b), BOTTOM), Lt(b, a))),
        'division_positive': All(q, Imp(Lt(RZERO, q), Lt(RZERO, Div(RONE, q)))),
        'division_monotone': alls((q, a, b), imps((Lt(RZERO, q), Le(a, b)), Le(Div(a, q), Div(b, q)))),
        'division_strict': alls((q, a, b), imps((Lt(RZERO, q), Lt(a, b)), Lt(Div(a, q), Div(b, q)))),
        'division_threshold_forward': alls((q, a, x), imps((Lt(RZERO, q), Le(Div(a, q), x)), Le(a, Mul(q, x)))),
        'division_threshold_reverse_strict': alls((q, a, x), imps((Lt(RZERO, q), Lt(x, Div(a, q))), Lt(Mul(q, x), a))),
        'division_cancel_product': alls((q, a), Imp(Lt(RZERO, q), Eq(Div(Mul(q, a), q), a))),
        'division_zero': All(q, Imp(Lt(RZERO, q), Eq(Div(RZERO, q), RZERO))),
        'division_add_one': alls((q, a), Imp(Lt(RZERO, q), Eq(Add(Div(RONE, q), Div(a, q)), Div(Add(a, RONE), q)))),
        'division_double_cancel': alls((q, a), Imp(Lt(RZERO, q), Eq(Div(Mul(TWO, a), Mul(TWO, q)), Div(a, q)))),
        'positive_product': alls((a, b), imps((Lt(RZERO, a), Lt(RZERO, b)), Lt(RZERO, Mul(a, b)))),
        'positive_times_order': alls((a, b, c), imps((Lt(RZERO, a), Le(b, c)), Le(Mul(a, b), Mul(a, c)))),
        'positive_times_strict': alls((a, b, c), imps((Lt(RZERO, a), Lt(b, c)), Lt(Mul(a, b), Mul(a, c)))),
        'addition_strict_right': alls((a, b, c), Imp(Lt(a, b), Lt(Add(a, c), Add(b, c)))),
        'addition_nonnegative_increment': alls((a, b), Imp(Le(RZERO, b), Le(a, Add(a, b)))),
        'gap_positive': alls((a, b), Imp(Lt(b, a), Lt(RZERO, Sub(a, b)))),
        'reciprocal_cancel': All(q, Imp(Lt(RZERO, q), Eq(Mul(q, Div(RONE, q)), RONE))),
        'strict_add_cancel': alls((a, b, c), Imp(Lt(Add(a, c), Add(b, c)), Lt(a, b))),
        'one_positive': Lt(RZERO, RONE),
        'dyadic_zero': Eq(A(DYADIC, NZERO), A(SUCCESSOR, NZERO)),
        'dyadic_successor': All(n, Eq(A(DYADIC, sn), A(NADD, A(DYADIC, n), A(DYADIC, n)))),
        'grid_zero': alls((f, q), Eq(grid(f, q, NZERO), SIMPLE_NIL)),
        'grid_successor': alls((f, q, n), Eq(grid(f, q, sn), A(SIMPLE_CONS, pair(Div(RONE, q), upper_level(f, Div(cast(sn), q))), grid(f, q, n))))
    }


def order_le(kernel, left, middle, right, first, second):
    return apply(ax('real_order_transitive', left, middle, right), first, second)


def identity_chain(kernel, left, middle, right, first, second):
    return eq_trans(left, middle, right, first, second)


def two_positive(kernel):
    one = ax('one_positive')
    doubled = apply(ax('addition_strict_right', RZERO, RONE, RONE), one)
    doubled = rewrite(kernel, doubled, ring(Add(RZERO, RONE), RONE))
    return apply(ax('strict_transitive', RZERO, RONE, TWO), one, doubled)


def two_nonnegative(kernel):
    return apply(ax('positive_implies_nonnegative', TWO), two_positive(kernel))


def derive_order_helpers(kernel):
    a, b, c, q = (V(name, 'R') for name in ('helper_a', 'helper_b', 'helper_c', 'helper_q'))
    conditions = (Lt(b, a), Lt(Div(RONE, Sub(a, b)), q))
    gap = Sub(a, b)
    positive = apply(ax('gap_positive', a, b), hyp(conditions[0]))
    scaled = apply(ax('positive_times_strict', gap, Div(RONE, gap), q), positive, hyp(conditions[1]))
    scaled = rewrite(kernel, scaled, apply(ax('reciprocal_cancel', gap), positive))
    shifted = apply(ax('addition_strict_right', RONE, Mul(gap, q), Mul(q, b)), scaled)
    shifted = rewrite(kernel, shifted, ring(Add(RONE, Mul(q, b)), Add(Mul(q, b), RONE)))
    shifted = rewrite(kernel, shifted, ring(Add(Mul(gap, q), Mul(q, b)), Mul(q, a)))
    kernel.theorem('inverse_gap_bound', alls((a, b, q), imps(conditions, Lt(Add(Mul(q, b), RONE), Mul(q, a)))), close(shifted, (a, b, q), conditions))
    conditions = (Lt(a, Add(b, RONE)), Lt(Add(c, RONE), a))
    transitive = apply(ax('strict_transitive', Add(c, RONE), a, Add(b, RONE)), hyp(conditions[1]), hyp(conditions[0]))
    cancel = apply(ax('strict_add_cancel', c, b, RONE), transitive)
    kernel.theorem('floor_upper_contradiction', alls((a, b, c), imps(conditions, Lt(c, b))), close(cancel, (a, b, c), conditions))
    conditions = (Lt(RZERO, q), Lt(Mul(q, b), a))
    division = apply(ax('division_strict', q, Mul(q, b), a), hyp(conditions[0]), hyp(conditions[1]))
    division = rewrite(kernel, division, apply(ax('division_cancel_product', q, b), hyp(conditions[0])))
    kernel.theorem('division_upper_contradiction', alls((q, a, b), imps(conditions, Lt(b, Div(a, q)))), close(division, (q, a, b), conditions))
    return kernel


def derive_parameters(kernel):
    n = V('dyadic_stage', 'N')
    q, qn = qvalue(n), qvalue(A(SUCCESSOR, n))
    base = ax('embedding_successor', NZERO)
    base = rewrite(kernel, base, ('axiom', 'embedding_zero'))
    base = rewrite(kernel, base, ring(Add(RZERO, RONE), RONE))
    base = rewrite(kernel, base, ('axiom', 'dyadic_zero'), True)
    kernel.theorem('dyadic_real_zero', Eq(qvalue(NZERO), RONE), base)
    step = ax('embedding_add', A(DYADIC, n), A(DYADIC, n))
    step = rewrite(kernel, step, ax('dyadic_successor', n), True)
    step = rewrite(kernel, step, ring(Add(q, q), Mul(TWO, q)))
    kernel.theorem('dyadic_real_successor', All(n, Eq(qn, Mul(TWO, q))), close(step, (n,)))
    kernel.theorem('dyadic_cap_real', All(n, Eq(cast(cap(n)), Mul(q, q))), close(ax('embedding_multiply', A(DYADIC, n), A(DYADIC, n)), (n,)))
    bound = Le(Add(cast(n), RONE), q)
    placeholder = V('zero_cast_placeholder', 'R')
    zero_plus = ring(Add(RZERO, RONE), RONE)
    zero_plus = rewrite(kernel, zero_plus, ('axiom', 'embedding_zero'), True)
    base_bound = ('eq_e', symmetric(Add(cast(NZERO), RONE), RONE, zero_plus), placeholder, Le(placeholder, RONE), ax('real_order_reflexive', RONE))
    base_bound = ('eq_e', symmetric(qvalue(NZERO), RONE, ref('dyadic_real_zero')), placeholder, Le(Add(cast(NZERO), RONE), placeholder), base_bound)
    step_bound = apply(ax('addition_monotone', Add(cast(n), RONE), q, Add(cast(n), RONE), q), hyp(bound), hyp(bound))
    step_bound = rewrite(kernel, step_bound, ring(Add(Add(cast(n), RONE), Add(cast(n), RONE)), Add(Add(cast(n), TWO), cast(n))))
    step_bound = rewrite(kernel, step_bound, ring(Add(q, q), Mul(TWO, q)))
    nonnegative_n = ax('embedding_nonnegative', n)
    base_to_double = apply(ax('addition_nonnegative_increment', Add(cast(n), TWO), cast(n)), nonnegative_n)
    step_bound = order_le(kernel, Add(cast(n), TWO), Add(Add(cast(n), TWO), cast(n)), Mul(TWO, q), base_to_double, step_bound)
    step_bound = rewrite(kernel, step_bound, ring(Add(Add(cast(n), RONE), RONE), Add(cast(n), TWO)), True)
    step_bound = rewrite(kernel, step_bound, ax('embedding_successor', n), True)
    step_bound = rewrite(kernel, step_bound, ref('dyadic_real_successor', n), True)
    induction = ('nat_induction', n, bound, base_bound, close(step_bound, (n,), (bound,)))
    kernel.theorem('dyadic_dominates_index', All(n, bound), induction)
    one_le = apply(ax('addition_nonnegative_increment', RONE, cast(n)), nonnegative_n)
    one_le = rewrite(kernel, one_le, ring(Add(RONE, cast(n)), Add(cast(n), RONE)))
    one_le = order_le(kernel, RONE, Add(cast(n), RONE), q, one_le, ref('dyadic_dominates_index', n))
    kernel.theorem('dyadic_at_least_one', All(n, Le(RONE, q)), close(one_le, (n,)))
    positive = apply(ax('strict_order_transitive', RZERO, RONE, q), ax('one_positive'), ref('dyadic_at_least_one', n))
    kernel.theorem('dyadic_positive', All(n, Lt(RZERO, q)), close(positive, (n,)))
    b = V('cofinal_bound', 'R')
    witness = V('cofinal_stage', 'N')
    condition = Lt(b, cast(witness))
    increase = apply(ax('addition_nonnegative_increment', cast(witness), RONE), apply(ax('positive_implies_nonnegative', RONE), ax('one_positive')))
    bound_q = order_le(kernel, cast(witness), Add(cast(witness), RONE), qvalue(witness), increase, ref('dyadic_dominates_index', witness))
    strict = apply(ax('strict_order_transitive', b, cast(witness), qvalue(witness)), hyp(condition), bound_q)
    exists_target = Ex(n, Lt(b, qvalue(n)))
    result = ('ex_i', exists_target, witness, strict)
    result = ('ex_e', ax('real_archimedean_embedding', b), witness, result)
    kernel.theorem('dyadic_unbounded', All(b, exists_target), close(result, (b,)))
    return kernel


def derive_grid(kernel):
    f, q, n = V('grid_function', FUNCTION), V('grid_denominator', 'R'), V('grid_length', 'N')
    point, family = V('grid_point', OMEGA), V('grid_family', EVENT_FAMILY)
    successor = A(SUCCESSOR, n)
    coefficient = Div(RONE, q)
    event = upper_level(f, Div(cast(successor), q))
    head = pair(coefficient, event)
    tail = grid(f, q, n)
    qp = Lt(RZERO, q)
    for mode in ('positive', 'adapted'):
        if mode == 'positive':
            premise = measurable_real(f)
            predicate = A(SIMPLE_VALID_NONNEGATIVE, tail)
            base = ('axiom', 'valid_nonnegative_simple_nil')
            measurable = ('and_l', instantiate(hyp(premise), Div(cast(successor), q)))
            measurable = rewrite(kernel, measurable, ax('simple_pair_event', coefficient, event), True)
            nonnegative = apply(ax('positive_implies_nonnegative', coefficient), apply(ax('division_positive', q), hyp(qp)))
            nonnegative = rewrite(kernel, nonnegative, ax('simple_pair_coefficient', coefficient, event), True)
            step = apply(('and_r', ax('valid_nonnegative_simple_cons', head, tail)), ('and_i', ('and_i', measurable, nonnegative), hyp(predicate)))
            variables = (f, q)
            conditions = (qp, premise)
        else:
            premise = upper_levels_in(f, family)
            predicate = A(SIMPLE_ADAPTED, family, tail)
            base = ax('simple_adapted_nil', family)
            included = instantiate(hyp(premise), Div(cast(successor), q))
            included = rewrite(kernel, included, ax('simple_pair_event', coefficient, event), True)
            step = apply(('and_r', ax('simple_adapted_cons', family, head, tail)), ('and_i', included, hyp(predicate)))
            variables = (f, q, family)
            conditions = (premise,)
        base = rewrite(kernel, base, ax('grid_zero', f, q), True)
        step = rewrite(kernel, step, ax('grid_successor', f, q, n), True)
        result = ('nat_induction', n, predicate, base, close(step, (n,), (predicate,)))
        statement = alls(variables, imps(conditions, All(n, predicate)))
        kernel.theorem('finite_upper_grid_' + mode, statement, close(result, variables, conditions))
    x = A(f, point)
    xp = Le(RZERO, x)
    floor = floor_value(Mul(q, x))
    qnonnegative = apply(ax('positive_implies_nonnegative', q), hyp(qp))
    product_positive = apply(ref('product_nonnegative', q, x), qnonnegative, hyp(xp))
    floor_nonnegative = ax('embedding_nonnegative', A(NFLOOR, Mul(q, x)))
    scalar_base = apply(ax('minimum_left', RZERO, floor), floor_nonnegative)
    scalar_base = rewrite(kernel, scalar_base, ('axiom', 'embedding_zero'), True)
    scalar_base = eq_trans(minimum(cast(NZERO), floor), cast(NZERO), RZERO, scalar_base, ('axiom', 'embedding_zero'))
    scalar_base = ('eq_e', scalar_base, V('grid_minimum_placeholder', 'R'), Eq(Div(minimum(cast(NZERO), floor), q), Div(V('grid_minimum_placeholder', 'R'), q)), ('eq_i', Div(minimum(cast(NZERO), floor), q)))
    scalar_base = rewrite(kernel, scalar_base, apply(ax('division_zero', q), hyp(qp)))
    value_base = rewrite(kernel, ax('simple_value_nil', point), ax('grid_zero', f, q), True)
    value_base = eq_trans(val(grid(f, q, NZERO), point), RZERO, clipped(q, NZERO, x), value_base, symmetric(clipped(q, NZERO, x), RZERO, scalar_base))
    predicate = Eq(val(tail, point), clipped(q, n, x))
    step_value = ax('simple_value_cons', head, tail, point)
    step_value = rewrite(kernel, step_value, ax('simple_pair_coefficient', coefficient, event))
    step_value = rewrite(kernel, step_value, ax('simple_pair_event', coefficient, event))
    step_value = rewrite(kernel, step_value, ax('grid_successor', f, q, n), True)
    step_value = rewrite(kernel, step_value, hyp(predicate))
    inside = Le(Div(cast(successor), q), x)
    outside = Imp(inside, BOTTOM)
    threshold = apply(ax('division_threshold_forward', q, cast(successor), x), hyp(qp), hyp(inside))
    floor_in = apply(ax('floor_integer_lower', successor, Mul(q, x)), product_positive, threshold)
    m_le_next = apply(ax('addition_nonnegative_increment', cast(n), RONE), apply(ax('positive_implies_nonnegative', RONE), ax('one_positive')))
    m_le_next = rewrite(kernel, m_le_next, ax('embedding_successor', n), True)
    m_le_floor = order_le(kernel, cast(n), cast(successor), floor, m_le_next, floor_in)
    min_current = apply(ax('minimum_left', cast(n), floor), m_le_floor)
    min_next = apply(ax('minimum_left', cast(successor), floor), floor_in)
    positive_step = rewrite(kernel, step_value, apply(ax('indicator_inside', event, point), hyp(inside)))
    positive_step = rewrite(kernel, positive_step, min_current)
    positive_step = rewrite(kernel, positive_step, ring(Add(Mul(coefficient, RONE), Div(cast(n), q)), Add(coefficient, Div(cast(n), q))))
    positive_step = rewrite(kernel, positive_step, apply(ax('division_add_one', q, cast(n)), hyp(qp)))
    positive_step = rewrite(kernel, positive_step, ax('embedding_successor', n), True)
    positive_step = rewrite(kernel, positive_step, min_next, True)
    threshold_out = apply(ax('strict_from_not_order', Div(cast(successor), q), x), hyp(outside))
    product_out = apply(ax('division_threshold_reverse_strict', q, cast(successor), x), hyp(qp), threshold_out)
    floor_out = apply(ax('floor_successor_upper', n, Mul(q, x)), product_positive, product_out)
    floor_next = order_le(kernel, floor, cast(n), cast(successor), floor_out, m_le_next)
    min_current_out = apply(ax('minimum_right', cast(n), floor), floor_out)
    min_next_out = apply(ax('minimum_right', cast(successor), floor), floor_next)
    negative_step = rewrite(kernel, step_value, apply(ax('indicator_outside', event, point), hyp(outside)))
    negative_step = rewrite(kernel, negative_step, min_current_out)
    negative_step = rewrite(kernel, negative_step, ring(Add(Mul(coefficient, RZERO), Div(floor, q)), Div(floor, q)))
    placeholder = V('next_minimum_placeholder', 'R')
    negative_step = ('eq_e', symmetric(minimum(cast(successor), floor), floor, min_next_out), placeholder, Eq(val(grid(f, q, successor), point), Div(placeholder, q)), negative_step)
    step = by_cases(inside, positive_step, negative_step)
    result = ('nat_induction', n, predicate, value_base, close(step, (n,), (predicate,)))
    statement = alls((f, q, point), imps((qp, xp), All(n, predicate)))
    kernel.theorem('finite_upper_grid_value', statement, close(result, (f, q, point), (qp, xp)))
    return kernel


def square_clip(q, x):
    return Div(minimum(Mul(q, q), floor_value(Mul(q, x))), q)


def derive_scalar(kernel):
    q, x, b = V('scalar_denominator', 'R'), V('scalar_value', 'R'), V('scalar_bound', 'R')
    m, n = V('scalar_length', 'N'), V('scalar_stage', 'N')
    qp, xp = Lt(RZERO, q), Le(RZERO, x)
    qnn = apply(ax('positive_implies_nonnegative', q), hyp(qp))
    product_nn = apply(ref('product_nonnegative', q, x), qnn, hyp(xp))
    floor = floor_value(Mul(q, x))
    lower = apply(ax('minimum_greatest_lower', cast(m), floor, RZERO), ax('embedding_nonnegative', m), ax('embedding_nonnegative', A(NFLOOR, Mul(q, x))))
    lower = apply(ax('division_monotone', q, RZERO, minimum(cast(m), floor)), hyp(qp), lower)
    lower = rewrite(kernel, lower, apply(ax('division_zero', q), hyp(qp)))
    upper = order_le(kernel, minimum(cast(m), floor), floor, Mul(q, x), ax('minimum_bound_right', cast(m), floor), apply(ax('floor_lower', Mul(q, x)), product_nn))
    upper = apply(ax('division_monotone', q, minimum(cast(m), floor), Mul(q, x)), hyp(qp), upper)
    upper = rewrite(kernel, upper, apply(ax('division_cancel_product', q, x), hyp(qp)))
    statement = alls((q, m, x), imps((qp, xp), And(Le(RZERO, clipped(q, m, x)), Le(clipped(q, m, x), x))))
    kernel.theorem('finite_grid_scalar_bounds', statement, close(('and_i', lower, upper), (q, m, x), (qp, xp)))
    double_q = Mul(TWO, q)
    double_q_positive = apply(ax('positive_product', TWO, q), two_positive(kernel), hyp(qp))
    double_product_nonnegative = apply(ref('product_nonnegative', double_q, x), apply(ax('positive_implies_nonnegative', double_q), double_q_positive), hyp(xp))
    floor_twice = floor_value(Mul(double_q, x))
    integer_floor = A(NFLOOR, Mul(q, x))
    twice_integer = A(NADD, integer_floor, integer_floor)
    twice_bound = apply(ax('positive_times_order', TWO, floor, Mul(q, x)), two_positive(kernel), apply(ax('floor_lower', Mul(q, x)), product_nn))
    twice_bound = rewrite(kernel, twice_bound, ring(Mul(TWO, Mul(q, x)), Mul(double_q, x)))
    twice_cast = ax('embedding_add', integer_floor, integer_floor)
    twice_cast = rewrite(kernel, twice_cast, ring(Add(floor, floor), Mul(TWO, floor)))
    twice_bound = rewrite(kernel, twice_bound, twice_cast, True)
    doubled_floor_bound = apply(ax('floor_integer_lower', twice_integer, Mul(double_q, x)), double_product_nonnegative, twice_bound)
    doubled_floor_bound = rewrite(kernel, doubled_floor_bound, twice_cast)
    z = minimum(Mul(q, q), floor)
    q_squared_nonnegative = apply(ref('product_nonnegative', q, q), qnn, qnn)
    twice_square_nonnegative = apply(ref('product_nonnegative', TWO, Mul(q, q)), two_nonnegative(kernel), q_squared_nonnegative)
    square_bound = apply(ax('positive_times_order', TWO, z, Mul(q, q)), two_positive(kernel), ax('minimum_bound_left', Mul(q, q), floor))
    extra_square = apply(ax('addition_nonnegative_increment', Mul(TWO, Mul(q, q)), Mul(TWO, Mul(q, q))), twice_square_nonnegative)
    extra_square = rewrite(kernel, extra_square, ring(Add(Mul(TWO, Mul(q, q)), Mul(TWO, Mul(q, q))), Mul(double_q, double_q)))
    square_bound = order_le(kernel, Mul(TWO, z), Mul(TWO, Mul(q, q)), Mul(double_q, double_q), square_bound, extra_square)
    floor_bound = apply(ax('positive_times_order', TWO, z, floor), two_positive(kernel), ax('minimum_bound_right', Mul(q, q), floor))
    floor_bound = order_le(kernel, Mul(TWO, z), Mul(TWO, floor), floor_twice, floor_bound, doubled_floor_bound)
    minimum_bound = apply(ax('minimum_greatest_lower', Mul(double_q, double_q), floor_twice, Mul(TWO, z)), square_bound, floor_bound)
    final = apply(ax('division_monotone', double_q, Mul(TWO, z), minimum(Mul(double_q, double_q), floor_twice)), double_q_positive, minimum_bound)
    final = rewrite(kernel, final, apply(ax('division_double_cancel', q, z), hyp(qp)))
    statement = alls((q, x), imps((qp, xp), Le(square_clip(q, x), square_clip(double_q, x))))
    kernel.theorem('grid_doubling_monotone', statement, close(final, (q, x), (qp, xp)))
    current, next_value = canonical_scalar(n, x), canonical_scalar(A(SUCCESSOR, n), x)
    adjacent = apply(ref('grid_doubling_monotone', qvalue(n), x), ref('dyadic_positive', n), hyp(xp))
    adjacent = rewrite(kernel, adjacent, ref('dyadic_real_successor', n), True)
    adjacent = rewrite(kernel, adjacent, ref('dyadic_cap_real', n), True)
    adjacent = rewrite(kernel, adjacent, ref('dyadic_cap_real', A(SUCCESSOR, n)), True)
    kernel.theorem('canonical_scalar_adjacent', alls((x,), Imp(xp, All(n, Le(current, next_value)))), close(close(adjacent, (n,)), (x,), (xp,)))
    return kernel


def derive_natural_monotonicity(kernel):
    seq = V('arbitrary_sequence', FT('N', 'R'))
    i, j = V('monotone_first', 'N'), V('monotone_last', 'N')
    adjacent = All(i, Le(A(seq, i), A(seq, A(SUCCESSOR, i))))
    predicate = All(i, Imp(A(NLE, i, j), Le(A(seq, i), A(seq, j))))
    base_condition = A(NLE, i, NZERO)
    base_eq = apply(ax('natural_below_zero', i), hyp(base_condition))
    placeholder = V('natural_index_placeholder', 'N')
    base = ('eq_e', symmetric(i, NZERO, base_eq), placeholder, Le(A(seq, placeholder), A(seq, NZERO)), ax('real_order_reflexive', A(seq, NZERO)))
    base = close(base, (i,), (base_condition,))
    step_condition = A(NLE, i, A(SUCCESSOR, j))
    cases = apply(ax('natural_below_successor_cases', i, j), hyp(step_condition))
    previous = A(NLE, i, j)
    first = apply(instantiate(hyp(predicate), i), hyp(previous))
    first = order_le(kernel, A(seq, i), A(seq, j), A(seq, A(SUCCESSOR, j)), first, instantiate(hyp(adjacent), j))
    equal_case = Eq(i, A(SUCCESSOR, j))
    second = ('eq_e', symmetric(i, A(SUCCESSOR, j), hyp(equal_case)), placeholder, Le(A(seq, placeholder), A(seq, A(SUCCESSOR, j))), ax('real_order_reflexive', A(seq, A(SUCCESSOR, j))))
    step = ('or_e', cases, first, second)
    step = close(step, (i,), (step_condition,))
    induction = ('nat_induction', j, predicate, base, close(step, (j,), (predicate,)))
    result = apply(instantiate(induction, j, i), hyp(A(NLE, i, j)))
    result = close(result, (i, j), (A(NLE, i, j),))
    kernel.theorem('adjacent_order_implies_increasing', All(seq, Imp(adjacent, increasing(seq))), close(result, (seq,), (adjacent,)))
    return kernel


def derive_scalar_lub(kernel):
    x, b = V('limit_value', 'R'), V('candidate_upper_bound', 'R')
    n, witness = V('limit_stage', 'N'), V('cofinal_witness', 'N')
    xp = Le(RZERO, x)
    sequence = Lam(n, canonical_scalar(n, x))
    bounds = All(n, Le(canonical_scalar(n, x), b))
    reverse = Lt(b, x)
    inverse_gap = Div(RONE, Sub(x, b))
    threshold = Add(x, inverse_gap)
    gap_positive = apply(ax('gap_positive', x, b), hyp(reverse))
    inverse_positive = apply(ax('division_positive', Sub(x, b)), gap_positive)
    left_threshold = apply(ax('addition_nonnegative_increment', x, inverse_gap), apply(ax('positive_implies_nonnegative', inverse_gap), inverse_positive))
    right_threshold = apply(ax('addition_nonnegative_increment', inverse_gap, x), hyp(xp))
    right_threshold = rewrite(kernel, right_threshold, ring(Add(inverse_gap, x), threshold))
    stage_condition = Lt(threshold, qvalue(witness))
    q, k = qvalue(witness), floor_value(Mul(qvalue(witness), x))
    q_positive = ref('dyadic_positive', witness)
    q_nonnegative = apply(ax('positive_implies_nonnegative', q), q_positive)
    qx_nonnegative = apply(ref('product_nonnegative', q, x), q_nonnegative, hyp(xp))
    x_less_q = apply(ax('order_strict_transitive', x, threshold, q), left_threshold, hyp(stage_condition))
    inv_less_q = apply(ax('order_strict_transitive', inverse_gap, threshold, q), right_threshold, hyp(stage_condition))
    product_less_square = apply(ax('positive_times_strict', q, x, q), q_positive, x_less_q)
    floor_less_square = apply(ax('order_strict_transitive', k, Mul(q, x), Mul(q, q)), apply(ax('floor_lower', Mul(q, x)), qx_nonnegative), product_less_square)
    min_reduces = apply(ax('minimum_right', Mul(q, q), k), apply(ax('strict_implies_order', k, Mul(q, q)), floor_less_square))
    below_product = apply(ref('inverse_gap_bound', x, b, q), hyp(reverse), inv_less_q)
    floor_upper = apply(ax('floor_upper_strict', Mul(q, x)), qx_nonnegative)
    product_below_floor = apply(ref('floor_upper_contradiction', Mul(q, x), k, Mul(q, b)), floor_upper, below_product)
    b_below_value = apply(ref('division_upper_contradiction', q, k, b), q_positive, product_below_floor)
    placeholder = V('uncapped_floor_placeholder', 'R')
    b_below_value = ('eq_e', symmetric(minimum(Mul(q, q), k), k, min_reduces), placeholder, Lt(b, Div(placeholder, q)), b_below_value)
    b_below_value = rewrite(kernel, b_below_value, ref('dyadic_cap_real', witness), True)
    contradiction = apply(ax('real_strict_nonstrict_inconsistent', b, canonical_scalar(witness, x)), b_below_value, instantiate(hyp(bounds), witness))
    contradiction = ('ex_e', ref('dyadic_unbounded', threshold), witness, contradiction)
    not_reverse = close(contradiction, (), (reverse,))
    least = apply(ax('real_order_not_reverse_strict', x, b), not_reverse)
    least = close(least, (b,), (bounds,))
    upper = ('and_r', apply(ref('finite_grid_scalar_bounds', qvalue(n), cap(n), x), ref('dyadic_positive', n), hyp(xp)))
    upper = close(upper, (n,))
    result = ('and_i', upper, least)
    kernel.theorem('canonical_scalar_lub', All(x, Imp(xp, lub(sequence, x))), close(result, (x,), (xp,)))
    adjacent = apply(ref('canonical_scalar_adjacent', x), hyp(xp))
    increasing_result = apply(ref('adjacent_order_implies_increasing', sequence), adjacent)
    kernel.theorem('canonical_scalar_increasing', All(x, Imp(xp, increasing(sequence))), close(increasing_result, (x,), (xp,)))
    return kernel


def derive_sequence(kernel):
    f, family = V('canonical_function', FUNCTION), V('canonical_family', EVENT_FAMILY)
    n, point = V('canonical_index', 'N'), V('canonical_point', OMEGA)
    h = approximation(f)
    nn, meas, adapted = function_nonnegative(f), measurable_real(f), upper_levels_in(f, family)
    positive = instantiate(apply(ref('finite_upper_grid_positive', f, qvalue(n)), ref('dyadic_positive', n), hyp(meas)), cap(n))
    positive = close(positive, (n,))
    kernel.theorem('canonical_sequence_positive', All(f, Imp(meas, simple_sequence_positive(h))), close(positive, (f,), (meas,)))
    adapted_proof = instantiate(apply(ref('finite_upper_grid_adapted', f, qvalue(n), family), hyp(adapted)), cap(n))
    adapted_proof = close(adapted_proof, (n,))
    kernel.theorem('canonical_sequence_adapted', alls((f, family), Imp(adapted, simple_sequence_adapted(h, family))), close(adapted_proof, (f, family), (adapted,)))
    strong = measurable_in(f, family)
    upper = close(('and_l', instantiate(hyp(strong), V('canonical_upper_level', 'R'))), (V('canonical_upper_level', 'R'),))
    adapted_from_strong = apply(ref('canonical_sequence_adapted', f, family), upper)
    kernel.theorem('canonical_sequence_adapted_measurable_in', alls((f, family), Imp(strong, simple_sequence_adapted(h, family))), close(adapted_from_strong, (f, family), (strong,)))
    x = A(f, point)
    value_identity = instantiate(apply(ref('finite_upper_grid_value', f, qvalue(n), point), ref('dyadic_positive', n), instantiate(hyp(nn), point)), cap(n))
    scalar_sequence = Lam(n, canonical_scalar(n, x))
    value_sequence = Lam(n, val(A(h, n), point))
    sequence_identity = apply(ax('real_sequence_extensionality', value_sequence, scalar_sequence), close(value_identity, (n,)))
    value_inc = apply(ref('canonical_scalar_increasing', x), instantiate(hyp(nn), point))
    value_inc = rewrite(kernel, value_inc, sequence_identity, True)
    value_lub = apply(ref('canonical_scalar_lub', x), instantiate(hyp(nn), point))
    value_lub = rewrite(kernel, value_lub, sequence_identity, True)
    kernel.theorem('canonical_sequence_increasing', All(f, Imp(nn, simple_sequence_increasing(h))), close(close(value_inc, (point,)), (f,), (nn,)))
    kernel.theorem('canonical_sequence_pointwise_lub', All(f, Imp(nn, simple_pointwise_lub(h, f))), close(close(value_lub, (point,)), (f,), (nn,)))
    positivity = apply(ref('canonical_sequence_positive', f), hyp(meas))
    monotonicity = apply(ref('canonical_sequence_increasing', f), hyp(nn))
    supremum = apply(ref('canonical_sequence_pointwise_lub', f), hyp(nn))
    combined = ('and_i', ('and_i', positivity, monotonicity), supremum)
    statement = All(f, imps((nn, meas), positive_approximation(h, f)))
    kernel.theorem('canonical_nonnegative_approximation', statement, close(combined, (f,), (nn, meas)))
    existence = ('ex_i', positive_approximable(f), h, combined)
    kernel.theorem('nonnegative_measurable_approximable', All(f, imps((nn, meas), positive_approximable(f))), close(existence, (f,), (nn, meas)))
    target_variable = V('adapted_simple_approximation', SIMPLE_SEQUENCE)
    target = Ex(target_variable, And(positive_approximation(target_variable, f), simple_sequence_adapted(target_variable, family)))
    adaptation = apply(ref('canonical_sequence_adapted', f, family), hyp(adapted))
    existence = ('ex_i', target, h, ('and_i', combined, adaptation))
    statement = alls((f, family), imps((nn, meas, adapted), target))
    kernel.theorem('nonnegative_measurable_adapted_approximable', statement, close(existence, (f, family), (nn, meas, adapted)))
    return kernel


def derive_canonical_approximations(kernel):
    proposed = foundations()
    additions = {}
    for name, formula in proposed.items():
        if name in kernel.axioms:
            if not same(kernel.axioms[name], formula):
                raise ValueError(('incompatible elementary foundation', name))
        elif name in kernel.verified:
            raise ValueError(('foundation collides with theorem', name))
        else:
            additions[name] = formula
    add_axioms(kernel, additions)
    for builder in (derive_order_helpers, derive_parameters, derive_grid, derive_scalar, derive_natural_monotonicity, derive_scalar_lub, derive_sequence):
        kernel = builder(kernel)
    return kernel


def run():
    kernel = derived_order_certificates()
    for builder in (derive_simple_limit_bound, derive_measure_continuity, derive_intersection_continuity, derive_finite_simple_continuity, derive_simple_finite_algebra, derive_simple_positivity, derive_simple_operations, derive_simple_restriction, derive_simple_threshold_measurable, derive_nonnegative_simple, derive_monotone_convergence, derive_simple_product_factorization):
        kernel = builder(kernel)
    return derive_canonical_approximations(kernel)



results = []


def check(identifier, condition):
    results.append({'id': identifier, 'passed': bool(condition)})


def negative_cases(kernel):
    f = V('canonical_function', FUNCTION)
    family = V('canonical_family', EVENT_FAMILY)
    q, point = V('grid_denominator', 'R'), V('grid_point', OMEGA)
    n = V('grid_length', 'N')
    fgrid = V('grid_function', FUNCTION)
    proposed = foundations()
    fn = V('fn', 'N')
    ff, fq = V('foundation_function', FUNCTION), V('fq', 'R')
    wrong_dyadic = replace_subterm(proposed['dyadic_successor'], A(NADD, A(DYADIC, fn), A(DYADIC, fn)), A(DYADIC, fn))
    wrong_grid = replace_subterm(proposed['grid_successor'], Div(RONE, fq), Div(TWO, fq))
    wrong_cap = replace_subterm(proposed['embedding_multiply'], RMUL, RADD)
    wrong_floor = replace_subterm(proposed['floor_upper_strict'], RLT, RLE)
    changed_limit = All(f, imps((function_nonnegative(f), measurable_real(f)), positive_approximation(approximation(f), add_function(f, constant_function(RONE)))))
    no_nn = All(f, Imp(measurable_real(f), positive_approximable(f)))
    no_meas = All(f, Imp(function_nonnegative(f), positive_approximable(f)))
    no_family = alls((f, family), simple_sequence_adapted(approximation(f), family))
    no_q = alls((fgrid, q, point), Imp(Le(RZERO, A(fgrid, point)), All(n, Eq(val(grid(fgrid, q, n), point), clipped(q, n, A(fgrid, point))))))
    wrong_direction = All(f, Imp(function_nonnegative(f), simple_sequence_increasing(Lam(V('bad_stage', 'N'), grid(f, Div(RONE, qvalue(V('bad_stage', 'N'))), cap(V('bad_stage', 'N')))))))
    return [
        {'id': 'reject_dyadic_without_doubling', 'kind': 'axiom', 'name': 'dyadic_successor', 'formula': wrong_dyadic},
        {'id': 'reject_grid_wrong_coefficient', 'kind': 'axiom', 'name': 'grid_successor', 'formula': wrong_grid},
        {'id': 'reject_wrong_cap_embedding', 'kind': 'axiom', 'name': 'embedding_multiply', 'formula': wrong_cap},
        {'id': 'reject_floor_upper_without_strictness', 'kind': 'axiom', 'name': 'floor_upper_strict', 'formula': wrong_floor},
        {'id': 'reject_missing_archimedean_foundation', 'kind': 'delete', 'name': 'real_archimedean_embedding'},
        {'id': 'reject_missing_floor_integer_property', 'kind': 'delete', 'name': 'floor_integer_lower'},
        {'id': 'reject_omitted_nonnegative_function', 'kind': 'target', 'name': 'nonnegative_measurable_approximable', 'formula': no_nn},
        {'id': 'reject_omitted_measurability', 'kind': 'target', 'name': 'nonnegative_measurable_approximable', 'formula': no_meas},
        {'id': 'reject_unrestricted_event_family', 'kind': 'target', 'name': 'canonical_sequence_adapted', 'formula': no_family},
        {'id': 'reject_zero_denominator_scope', 'kind': 'target', 'name': 'finite_upper_grid_value', 'formula': no_q},
        {'id': 'reject_shifted_limit', 'kind': 'target', 'name': 'canonical_nonnegative_approximation', 'formula': changed_limit},
        {'id': 'reject_inverted_mesh', 'kind': 'target', 'name': 'canonical_sequence_increasing', 'formula': wrong_direction}
    ]


def replay_mutation(kernel, case):
    if case['kind'] == 'target':
        original = next(record for record in kernel.records if record[0] == case['name'])
        fresh = Kernel(kernel.axioms)
        for name, formula, proof in kernel.records:
            if name == case['name']:
                fresh.theorem(name, case['formula'], proof)
                return fresh
            fresh.theorem(name, formula, proof)
        raise ValueError('mutation theorem absent')
    axioms = dict(kernel.axioms)
    if case['kind'] == 'delete':
        del axioms[case['name']]
    elif case['kind'] == 'axiom':
        if same(axioms[case['name']], case['formula']):
            raise ValueError('mutation did not change its target')
        axioms[case['name']] = case['formula']
    else:
        raise ValueError('unknown mutation kind')
    fresh = Kernel(axioms)
    for name, formula, proof in kernel.records:
        fresh.theorem(name, formula, proof)
    return fresh


def verify():
    results.clear()
    kernel = run()
    f, family = V('independent_function', FUNCTION), V('independent_family', EVENT_FAMILY)
    sequence = approximation(f)
    expected = All(f, imps((function_nonnegative(f), measurable_real(f)), positive_approximable(f)))
    bound_sequence = V('independent_sequence', SIMPLE_SEQUENCE)
    expected_adapted = alls((f, family), imps((function_nonnegative(f), measurable_real(f), upper_levels_in(f, family)), Ex(bound_sequence, And(positive_approximation(bound_sequence, f), simple_sequence_adapted(bound_sequence, family)))))
    check('canonical_nonnegative_approximations_exist', same(kernel.verified['nonnegative_measurable_approximable'].conclusion, expected))
    check('canonical_adapted_approximations_exist', same(kernel.verified['nonnegative_measurable_adapted_approximable'].conclusion, expected_adapted))
    check('canonical_list_is_explicit', same(kernel.verified['canonical_nonnegative_approximation'].conclusion, All(f, imps((function_nonnegative(f), measurable_real(f)), positive_approximation(sequence, f)))))
    check('canonical_lists_positive', not kernel.verified['canonical_sequence_positive'].assumptions)
    check('canonical_lists_increasing', not kernel.verified['canonical_sequence_increasing'].assumptions)
    check('canonical_lists_pointwise_lub', not kernel.verified['canonical_sequence_pointwise_lub'].assumptions)
    check('finite_sum_equals_truncated_floor', not kernel.verified['finite_upper_grid_value'].assumptions)
    check('dyadic_growth_by_induction', not kernel.verified['dyadic_dominates_index'].assumptions)
    check('cofinality_from_archimedean_embedding', not kernel.verified['dyadic_unbounded'].assumptions)
    check('all_derived_claims_closed', all(not result.assumptions for result in kernel.verified.values()))
    check('approximation_is_not_a_foundation', not any(name in kernel.axioms for name in ('canonical_sequence_pointwise_lub', 'nonnegative_measurable_approximable', 'finite_upper_grid_value', 'canonical_scalar_lub')))
    positive_q = sp.Symbol('positive_q', positive=True)
    arbitrary_x = sp.Symbol('arbitrary_x', real=True)
    check('reciprocal_positive_domain', (1 / positive_q).is_positive is True)
    check('division_addition_identity', sp.cancel(1 / positive_q + arbitrary_x / positive_q - (arbitrary_x + 1) / positive_q) == 0)
    check('division_doubling_identity', sp.cancel(2 * arbitrary_x / (2 * positive_q) - arbitrary_x / positive_q) == 0)
    for case in negative_cases(kernel):
        check(case['id'], rejects(lambda case=case: replay_mutation(kernel, case)))
    if not all(item['passed'] for item in results):
        raise AssertionError(results)
    first = next(i for i, record in enumerate(kernel.records) if record[0] == 'inverse_gap_bound')
    return {'backend': 'Python 3', 'checks': list(results), 'derived': [name for name, _, _ in kernel.records[first:]], 'derived_count': len(kernel.records) - first, 'kernel': kernel}


if __name__ == '__main__':
    report = verify()
    print(json.dumps({key: value for key, value in report.items() if key != 'kernel'}, ensure_ascii=False))
