from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from capitulo_07.probabilidade_geral import V, FT, A, All, Ex, Imp, And, Eq, BOTTOM, Kernel, instantiate, apply, close, alls, rejects


def certificate():
    f = V('forward', FT('Input', 'Output'))
    g = V('recovery', FT('Output', 'Input'))
    x, y, z = (V(name, 'Input') for name in ('first', 'second', 'point'))
    output = V('output', 'Output')
    origin = V('origin', 'Input')
    collision = And(Imp(Eq(x, y), BOTTOM), Eq(A(f, x), A(f, y)))
    noninjective = Ex(x, Ex(y, collision))
    left_inverse = All(z, Eq(A(g, A(f, z)), z))
    fx = instantiate(('assume', left_inverse), x)
    gy_equals_x = ('eq_e', ('and_r', ('assume', collision)), output, Eq(A(g, output), x), fx)
    y_equals_x = ('eq_e', instantiate(('assume', left_inverse), y), origin, Eq(origin, x), gy_equals_x)
    x_equals_y = ('eq_e', y_equals_x, origin, Eq(origin, y), ('eq_i', y))
    contradiction = apply(('and_l', ('assume', collision)), x_equals_y)
    eliminate_y = ('ex_e', ('assume', Ex(y, collision)), y, contradiction)
    eliminate_x = ('ex_e', ('assume', noninjective), x, eliminate_y)
    proof = close(eliminate_x, (f, g), (noninjective, left_inverse))
    formula = alls((f, g), Imp(noninjective, Imp(left_inverse, BOTTOM)))
    kernel = Kernel({})
    kernel.theorem('noninjective_has_no_left_inverse', formula, proof)
    return kernel, formula, proof


def check(name, value):
    if not value:
        raise AssertionError(name)


def verify():
    kernel, formula, proof = certificate()
    check('noninjective_has_no_left_inverse', 'noninjective_has_no_left_inverse' in kernel.verified and not kernel.verified['noninjective_has_no_left_inverse'].assumptions)
    f, g = V('forward', FT('Input', 'Output')), V('recovery', FT('Output', 'Input'))
    x, y = V('first', 'Input'), V('second', 'Input')
    results = [
        {'id': 'noninjective_has_no_left_inverse', 'passed': not kernel.verified['noninjective_has_no_left_inverse'].assumptions},
        {'id': 'reject_missing_inverse', 'passed': rejects(lambda: Kernel({}).theorem('invalid', formula, ('eq_i', x)))},
        {'id': 'reject_wrong_direction_equality', 'passed': rejects(lambda: Kernel({}).infer(('eq_e', ('assume', Eq(A(f, x), A(f, y))), V('t', 'Output'), Eq(A(g, V('t', 'Output')), x), ('eq_i', x))))},
    ]
    if not all(row['passed'] for row in results):
        raise AssertionError(results)
    return {'backend': 'Python 3 typed proof kernel', 'passed': True, 'results': results, 'axioms': [], 'scope': 'Arbitrary input and output types, arbitrary functions, existential collision, left inverse on the entire domain.'}


if __name__ == '__main__':
    print(json.dumps(verify()))
