"""Untrusted exact search; Lean checks its stopped seven-column certificate."""
import importlib.util
import json
from pathlib import Path

source = Path('scripts/experiments/observable_space.py')
spec = importlib.util.spec_from_file_location('observable_space', source)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
states = [('initial',)] + [('bound', binding) for binding in range(3)] + [
    ('revealed', binding, publish) for binding in range(3) for publish in range(2)]
actions = [(binding, publish) for binding in range(3) for publish in range(2)]

def next_state(state, action):
    if state[0] == 'initial':
        return ('bound', action[0])
    if state[0] == 'bound':
        return ('revealed', state[1], action[1])
    return state

def readout(state):
    if state[0] != 'revealed':
        return 0
    binding, publish = state[1:]
    return binding + 1 if publish else 1

operators = {}
for observed in states:
    for action in actions:
        matrix = [[0] * len(states) for _ in states]
        if observed[0] != 'revealed':
            matrix[states.index(observed)][states.index(next_state(observed, action))] = 1
        operators[str((observed, action))] = matrix
data = {'operators': operators,
        'seeds': [[int(readout(state) == outcome) for state in states] for outcome in range(4)]}
result = module.construct(data)
output = Path('ephemeral/survey-experiments/program-payment-observables-result.json')
output.write_text(json.dumps(result, default=str, indent=2))
print(json.dumps({'states': len(states), 'labels': len(operators),
                  'nonzero_labels': sum(any(any(row) for row in m) for m in operators.values()),
                  'dimension': result['dimension'], 'basis_words': result['basis_words']}))
