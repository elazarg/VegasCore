#!/usr/bin/env python3
"""Exact finite probe of the permitted-menu deviation law on the roster calendar.

Claim under test (N3). In the permitted native menu, against the timed calendar
profile of a source profile, the outcome law of every unilateral deviation of
one player is an exact mixture of the outcome laws of that player's source
deviations.

Source game S. Chance draws correlated private types (tA, tB). Alice commits a
hidden bit vA (law depends on tA); Bob commits a hidden bit vB knowing tB and
that Alice committed; Alice opens or withholds (law depends on tA, vA); Bob
opens or withholds knowing tB, vB and Alice's public result. The outcome is the
complete typed terminal state (tA, tB, vA, vB, rA, rB). Alice plays a fixed
mixed source profile; Bob deviates.

Native game N (one calendar instance). Every event has a three-visit roster
[owner, other, owner]. Alice decides at a roster visit drawn from the roster
timing at weight one half (first visit 1/4, last visit 3/4), independently of
everything else; at the selected visit she sends her source decision, and she
is silent otherwise (withholding is silence). Bob, a non-owner at Alice's
events, is silent there (permitted menu) but observes, at his middle visit,
the leak of an in-transit packet: that Alice already sent, and the content of
an in-transit opening. At the end of each phase the inclusion, its visit
index and any opened value are public. At his own events Bob may act at
either visit; a binding is required by his last visit, and silence through his
last reveal visit withholds. Bob's native information therefore contains
Alice's timing noise and his own timing, which the source lacks.

Method. Both games are trees with Bob as the only decision maker (perfect
recall). For a rational weight vector w on outcomes, the maximal expected w
over Bob's native policies and over his source policies are computed exactly by
backward induction over information sets; N3 implies the native maximum never
exceeds the source maximum. Every native maximizer found is then checked for
exact membership in the source polytope by an exact rational linear program
over Bob's source realization plans (sequence form), as is the law of each of a
sample of random pure native deviations. Two negative controls must
fail: a content leak of Alice's committed bit to Bob, and an Alice timing law
that depends on her committed bit. They validate that the harness detects
non-source information.

Run: python scripts/experiments/calendar_menu_mixture_probe.py
"""

from fractions import Fraction as F
import itertools
import random

PRIOR = {(0, 0): F(1, 6), (0, 1): F(1, 3), (1, 0): F(1, 4), (1, 1): F(1, 4)}
COMMIT_ONE = {0: F(1, 3), 1: F(3, 4)}  # P(vA = 1 | tA)
OPEN = {(0, 0): F(1, 2), (0, 1): F(1, 5), (1, 0): F(2, 3), (1, 1): F(7, 8)}  # P(open | tA, vA)
TIMING = {0: F(1, 4), 1: F(3, 4)}  # roster timing at weight 1/2 with two owner visits
TYPED_TIMING = {0: {0: F(1, 10), 1: F(9, 10)}, 1: {0: F(9, 10), 1: F(1, 10)}}


def leaf(outcome):
    return ("leaf", outcome)


def chance(branches):
    branches = [(p, node) for p, node in branches if p != 0]
    assert sum(p for p, _ in branches) == 1
    return ("chance", branches)


def bob(info, actions):
    return ("B", info, actions)


def bern(p, one, zero):
    return [(p, one), (1 - p, zero)]


# Source game.

def source_tree():
    def after_types(tA, tB):
        def after_commit(vA):
            def after_bob_commit(vB):
                def after_open(rA):
                    seen = vA if rA else None
                    return bob(("S4", tB, vB, seen),
                               [(rB, leaf((tA, tB, vA, vB, rA, rB))) for rB in (0, 1)])
                return chance(bern(OPEN[(tA, vA)], after_open(1), after_open(0)))
            return bob(("S2", tB), [(vB, after_bob_commit(vB)) for vB in (0, 1)])
        return chance(bern(COMMIT_ONE[tA], after_commit(1), after_commit(0)))
    return chance([(p, after_types(tA, tB)) for (tA, tB), p in PRIOR.items()])


# Native game.

def native_tree(variant):
    def after_types(tA, tB):
        def commit_branches():
            for vA in (0, 1):
                pv = COMMIT_ONE[tA] if vA else 1 - COMMIT_ONE[tA]
                timing = TYPED_TIMING[vA] if variant == "typed-timing" else TIMING
                for s1 in (0, 1):
                    yield pv * timing[s1], vA, s1

        def e1(vA, s1):
            leak1 = ("sent", vA) if (s1 == 0 and variant == "content-leak") else (
                ("sent",) if s1 == 0 else ("pending",))
            known = (tB, leak1, ("A-commit", s1))
            return e2(vA, known)

        def e2(vA, known):
            def committed(vB, slot):
                return e3(vA, vB, known + (("B-commit", vB, slot),))
            first = [(("commit", 0), committed(0, 0)), (("commit", 1), committed(1, 0)),
                     ("wait", bob(("E2v1", known),
                                  [(("commit", vB), committed(vB, 1)) for vB in (0, 1)]))]
            return bob(("E2v0", known), first)

        def e3(vA, vB, known):
            branches = []
            for rA in (0, 1):
                pr = OPEN[(tA, vA)] if rA else 1 - OPEN[(tA, vA)]
                for s3 in (0, 1):
                    if rA:
                        leak3 = ("opened", vA) if s3 == 0 else ("pending",)
                        public = ("A-open", s3, vA)
                    else:
                        leak3 = ("pending",)
                        public = ("A-expired",)
                    branches.append((pr * TIMING[s3],
                                     e4(vA, vB, rA, known + (leak3, public))))
            return chance(branches)

        def e4(vA, vB, rA, known):
            def done(rB):
                return leaf((tA, tB, vA, vB, rA, rB))
            return bob(("E4v0", known),
                       [("open", done(1)),
                        ("wait", bob(("E4v1", known), [("open", done(1)), ("withhold", done(0))]))])

        return chance([(p, e1(vA, s1)) for p, vA, s1 in commit_branches()])

    return chance([(p, after_types(tA, tB)) for (tA, tB), p in PRIOR.items()])


# Exact single-agent backward induction under perfect recall.

def collect(tree):
    sets = {}

    def walk(node, reach, depth):
        kind = node[0]
        if kind == "leaf":
            return
        if kind == "chance":
            for p, child in node[1]:
                walk(child, reach * p, depth)
            return
        _, info, actions = node
        entry = sets.setdefault(info, {"depth": depth, "nodes": []})
        assert entry["depth"] == depth, "perfect recall violated"
        entry["nodes"].append((node, reach))
        for _, child in actions:
            walk(child, reach, depth + 1)

    walk(tree, F(1), 0)
    return sets


def best_response(tree, weight):
    sets = collect(tree)
    best = {}

    def value(node):
        kind = node[0]
        if kind == "leaf":
            return weight.get(node[1], F(0))
        if kind == "chance":
            return sum(p * value(child) for p, child in node[1])
        _, info, actions = node
        return value(dict(actions)[best[info]])

    for info in sorted(sets, key=lambda key: -sets[key]["depth"]):
        nodes = sets[info]["nodes"]
        actions = [a for a, _ in nodes[0][0][2]]
        scores = {a: sum(reach * value(dict(node[2])[a]) for node, reach in nodes)
                  for a in actions}
        best[info] = max(actions, key=lambda a: (scores[a], -actions.index(a)))
    return best


def law(tree, policy):
    result = {}

    def walk(node, mass):
        kind = node[0]
        if kind == "leaf":
            result[node[1]] = result.get(node[1], F(0)) + mass
        elif kind == "chance":
            for p, child in node[1]:
                walk(child, mass * p)
        else:
            _, info, actions = node
            walk(dict(actions)[policy[info]], mass)

    walk(tree, F(1))
    return result


def expected(distribution, weight):
    return sum(p * weight.get(o, F(0)) for o, p in distribution.items())


# Exact membership in the source polytope: sequence-form linear program.

def sequence_form(tree):
    """Rows of the realization-plan constraints and the outcome map."""
    sequences = [()]
    parents = {}
    outcome_terms = {}

    def walk(node, reach, current):
        kind = node[0]
        if kind == "leaf":
            outcome_terms.setdefault(node[1], []).append((reach, current))
        elif kind == "chance":
            for p, child in node[1]:
                walk(child, reach * p, current)
        else:
            _, info, actions = node
            parents.setdefault(info, current)
            assert parents[info] == current, "perfect recall violated"
            for a, child in actions:
                seq = current + ((info, a),)
                if seq not in sequences:
                    sequences.append(seq)
                walk(child, reach, seq)

    walk(tree, F(1), ())
    index = {seq: i for i, seq in enumerate(sequences)}
    rows, rhs = [], []
    row = [F(0)] * len(sequences)
    row[index[()]] = F(1)
    rows.append(row)
    rhs.append(F(1))
    for info, parent in parents.items():
        row = [F(0)] * len(sequences)
        row[index[parent]] = F(-1)
        for seq in sequences:
            if seq and seq[-1][0] == info and seq[:-1] == parent:
                row[index[seq]] += F(1)
        rows.append(row)
        rhs.append(F(0))
    return sequences, index, rows, rhs, outcome_terms


def feasible(rows, rhs):
    """Exact phase-one simplex (Bland's rule): is {x >= 0 : rows x = rhs} nonempty?"""
    m, n = len(rows), len(rows[0])
    table = []
    for r, b in zip(rows, rhs):
        if b < 0:
            r, b = [-v for v in r], -b
        table.append(list(r) + [F(1) if i == len(table) else F(0) for i in range(m)] + [b])
    basis = [n + i for i in range(m)]
    width = n + m
    cost = [F(0)] * n + [F(1)] * m

    def reduced(j):
        return cost[j] - sum(cost[basis[i]] * table[i][j] for i in range(m))

    while True:
        entering = next((j for j in range(width) if reduced(j) < 0), None)
        if entering is None:
            break
        ratios = [(table[i][-1] / table[i][entering], basis[i], i)
                  for i in range(m) if table[i][entering] > 0]
        if not ratios:
            raise RuntimeError("unbounded phase one")
        _, _, pivot = min(ratios)
        factor = table[pivot][entering]
        table[pivot] = [v / factor for v in table[pivot]]
        for i in range(m):
            if i != pivot and table[i][entering] != 0:
                scale = table[i][entering]
                table[i] = [a - scale * b for a, b in zip(table[i], table[pivot])]
        basis[pivot] = entering
    objective = sum(cost[basis[i]] * table[i][-1] for i in range(m))
    return objective == 0


def in_source_polytope(source, target):
    sequences, index, rows, rhs, terms = sequence_form(source)
    rows, rhs = [list(r) for r in rows], list(rhs)
    outcomes = set(terms) | set(target)
    for o in sorted(outcomes):
        row = [F(0)] * len(sequences)
        for reach, seq in terms.get(o, []):
            row[index[seq]] += reach
        rows.append(row)
        rhs.append(target.get(o, F(0)))
    return feasible(rows, rhs)


OUTCOMES = list(itertools.product((0, 1), repeat=6))


def directions(seed, count):
    rng = random.Random(seed)
    yield {o: F(1) if o[2] == o[3] else F(0) for o in OUTCOMES}  # Bob matches Alice's bit
    yield {o: F(1) if (o[2] == o[3]) == bool(o[5]) else F(0) for o in OUTCOMES}
    for o in OUTCOMES:
        yield {o: F(1)}
        yield {o: F(-1)}
    for _ in range(count):
        yield {o: F(rng.randint(-20, 20), rng.randint(1, 7)) for o in OUTCOMES}


def probe(variant, count=300, seed=2026):
    source = source_tree()
    native = native_tree(variant)
    worst = None
    checked = 0
    for weight in directions(seed, count):
        native_policy = best_response(native, weight)
        native_law = law(native, native_policy)
        native_value = expected(native_law, weight)
        source_value = expected(law(source, best_response(source, weight)), weight)
        gap = native_value - source_value
        if worst is None or gap > worst[0]:
            worst = (gap, weight, native_law)
        if gap > 0:
            return {"variant": variant, "holds": False, "gap": gap,
                    "member": in_source_polytope(source, native_law), "checked": checked}
        if not in_source_polytope(source, native_law):
            return {"variant": variant, "holds": False, "gap": gap, "member": False,
                    "checked": checked}
        checked += 1
    # Random pure native deviations are further vertices of the native polytope.
    rng = random.Random(seed + 1)
    sets = collect(native)
    for _ in range(count):
        policy = {info: rng.choice([a for a, _ in entry["nodes"][0][0][2]])
                  for info, entry in sets.items()}
        if not in_source_polytope(source, law(native, policy)):
            return {"variant": variant, "holds": False, "gap": worst[0], "member": False,
                    "checked": checked}
        checked += 1
    return {"variant": variant, "holds": True, "gap": worst[0], "member": True,
            "checked": checked}


def main():
    results = [probe("base"), probe("content-leak"), probe("typed-timing")]
    for result in results:
        print(result)
    base, leak, typed = results
    assert base["holds"], "N3 refuted in the base calendar model"
    assert not leak["holds"], "negative control (content leak) not detected"
    assert not typed["holds"], "negative control (typed timing) not detected"
    print("base model: every tested native maximizer and random pure native deviation is an "
          "exact source mixture; both negative controls are detected")


if __name__ == "__main__":
    main()
