import json
from itertools import product

ALPHABET = ('t', 'a', 'd')
TRANSITIONS = {
    (0, 't'): ((0, 't'),), (0, 'a'): ((0, 'a'),),
    (0, 'd'): ((1, 'd'), (2, 't')),
    (1, 't'): ((0, 't'),), (1, 'a'): ((0, 'a'),),
    (1, 'd'): ((1, 'd'), (2, 't')),
    (2, 't'): (), (2, 'a'): (), (2, 'd'): ()
}
FINAL = {0, 2}


def outputs(state, word, transitions=TRANSITIONS, final=FINAL):
    if not word:
        return ((),) if state in final else ()
    return tuple((emitted,) + suffix
                 for target, emitted in transitions[state, word[0]]
                 for suffix in outputs(target, word[1:], transitions, final))


def target(word):
    return word[:-1] + (('t',) if word[-1] == 'd' else word[-1:]) if word else ()


def induction_certificate(transitions=TRANSITIONS, final=FINAL):
    if set(transitions) != set(product(range(3), ALPHABET)):
        return False
    if any(transitions[0, c] != transitions[1, c] for c in ALPHABET):
        return False
    if any(transitions[2, c] for c in ALPHABET):
        return False
    if outputs(0, (), transitions, final) != ((),):
        return False
    if any(outputs(0, (c,), transitions, final) != (target((c,)),)
           for c in ALPHABET):
        return False
    tail = ('devoice_of_arbitrary_nonempty_tail',)
    for head in ALPHABET:
        expanded = tuple((emitted,) + suffix
                         for state, emitted in transitions[0, head]
                         for suffix in ((tail,) if state in (0, 1) else ()))
        if expanded != ((head,) + tail,):
            return False
    return True


def main():
    checks = []
    def check(name, condition):
        if not condition:
            raise AssertionError(name)
        checks.append(name)
    check('all_states_all_symbols_structural_induction', induction_certificate())
    check('published_tad', outputs(0, tuple('tad')) == (tuple('tat'),))
    check('published_tada', outputs(0, tuple('tada')) == (tuple('tada'),))
    changed = dict(TRANSITIONS)
    changed[1, 'a'] = ((1, 'a'),)
    check('changed_pending_transition_rejected', not induction_certificate(changed))
    changed = dict(TRANSITIONS)
    changed[2, 'a'] = ((0, 'a'),)
    check('continuing_after_final_devoicing_rejected', not induction_certificate(changed))
    check('wrong_accepting_state_rejected', not induction_certificate(final={0, 1, 2}))
    changed = dict(TRANSITIONS)
    changed[0, 'd'] = changed[1, 'd'] = ((1, 'd'), (2, 'd'))
    check('wrong_final_output_rejected', not induction_certificate(changed))
    print(json.dumps({'passed': True, 'checks': len(checks), 'results': checks,
                      'scope': 'Structural induction for arbitrary finite words over t,a,d. The nonempty-tail induction variable remains symbolic; all finite transition cases are exhaustive. The Lean proof supplies kernel-checked totality, uniqueness, unchanged nonfinal symbols and exact final-symbol rule.'}))


if __name__ == '__main__':
    main()
