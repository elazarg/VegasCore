#!/usr/bin/env python3
"""Finite probe C6: deferral, public misses and the penalized-miss route.

Source. Chance draws Alice's private value v, uniform on {0, 1}. Alice commits
a bit a, Bob chooses b without seeing v or a, and then a is revealed. Two
payoff kinds on the committed outcome: `pennies` (Bob gets 1 when b = a,
Alice gets 1 when b != a; the unique equilibrium law is uniform) and
`coordination` (both get 1 when b = a). The source equilibrium studied has
Alice commit a = v and Bob mix uniformly, so the source law of (v, a, b) is
uniform on {(v, v, b)}.

Miss payoffs. If Alice's binding fails, Bob chooses `0` (abort, worth 1/3 to
him) or `1` (proceed without her, worth v to him), so his best reply after a
miss depends on his belief about v: proceed exactly when P(v = 1) > 1/3.
Alice gets 1 if Bob proceeds and 0 otherwise, minus the deposit D. Under the
prior Bob proceeds, so a miss is worth 1 - D to Alice against 1/2 on path.

Extended source. The source plus a `miss` move at each binding, leading to
the miss payoffs (deposit included) after Bob's public observation.

Target. Alice's turn 1: send0, send1 or defer. After a deferral the builder
grants turn 2 with probability p_v (control (a) lets it depend on v); at
turn 2 Alice may send0, send1 or stay silent. No send is a public miss. Bob
observes whether a handle was accepted and at which turn (`t1`, `t2`) or that
the binding missed (`miss`); whether turn 2 was granted is not public.

The route compiles an extended-source profile to the target: sending at turn
1 is the source action, deciding at turn 2 is the same source action, and
deferral is the mixture of a miss (probability 1 - p) and deciding later.
Bob's play at `t1` and `t2` is his source play at `guess` (he ignores the
timing signal), and his play at `miss` is his extended-source play.

Beliefs and sequential rationality use the checker of adaptive_schedules.py:
exact limits of one explicit tremble sequence and every whole replacement
policy at every information set. Unless stated, trembles are uniform at every
information set, so deferral has weight epsilon / 3 for both values of v.
These are design probes, not proofs; see docs/se-schedule-generalization.md.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
import json

from adaptive_schedules import (ALICE, BOB, HALF, Chance, End, Move, Node, Profile,
                                consistent_beliefs, infosets, law, prescribed_value,
                                pure, uniform, value)


TYPES = (0, 1)
KINDS = ("pennies", "coordination")
MISS = "miss"
THIRD = Fraction(1, 3)
DEPOSITS = (Fraction(0), Fraction(1, 4), HALF, Fraction(1))
GRANTS = (Fraction(0), HALF, Fraction(1))
# Alice's gain from a miss Bob answers by proceeding: 1 - D against 1/2 on path.
DEPOSIT_THRESHOLD = HALF


def accepted(kind: str, v: int, a: int, b: int) -> End:
    agree = Fraction(int(a == b))
    alice = agree if kind == "coordination" else 1 - agree
    return End((alice, agree), (v, a, b))


def missed(v: int, b: int, deposit: Fraction) -> End:
    bob = THIRD if b == 0 else Fraction(v)
    return End((Fraction(b) - deposit, bob), (v, MISS, b))


def bob_after_send(infoset: str, kind: str, v: int, a: int) -> Move:
    return Move(BOB, infoset, tuple((str(b), accepted(kind, v, a, b)) for b in (0, 1)))


def bob_after_miss(infoset: str, v: int, deposit: Fraction) -> Move:
    return Move(BOB, infoset, tuple((str(b), missed(v, b, deposit)) for b in (0, 1)))


def source(kind: str, deposit: Fraction, extended: bool) -> Node:
    def commit(v: int) -> Move:
        options = [(str(a), bob_after_send("guess", kind, v, a)) for a in (0, 1)]
        if extended:
            options.append((MISS, bob_after_miss("after_miss", v, deposit)))
        return Move(ALICE, f"commit{v}", tuple(options))
    return Chance(tuple((HALF, commit(v)) for v in TYPES))


def target(kind: str, deposit: Fraction, grant: dict[int, Fraction]) -> Node:
    def turn2(v: int) -> Move:
        return Move(ALICE, f"turn2_{v}", (
            ("send0", bob_after_send("t2", kind, v, 0)),
            ("send1", bob_after_send("t2", kind, v, 1)),
            ("silent", bob_after_miss("miss", v, deposit))))

    def deferred(v: int) -> Chance:
        branches = ((grant[v], turn2(v)), (1 - grant[v], bob_after_miss("miss", v, deposit)))
        return Chance(tuple((w, node) for w, node in branches if w))

    def turn1(v: int) -> Move:
        return Move(ALICE, f"turn1_{v}", (
            ("send0", bob_after_send("t1", kind, v, 0)),
            ("send1", bob_after_send("t1", kind, v, 1)),
            ("defer", deferred(v))))
    return Chance(tuple((HALF, turn1(v)) for v in TYPES))


def uniform_trembles(root: Node) -> Profile:
    return {name: uniform(*actions) for name, (_, actions) in infosets(root).items()}


def violations(root: Node, profile: Profile, tremble: Profile, first_only: bool = False) -> list[str]:
    """Information sets where some whole replacement policy is strictly better."""
    sets = infosets(root)
    beliefs = consistent_beliefs(root, profile, tremble)
    failing = []
    for infoset, (who, _) in sets.items():
        own = [name for name, (player, _) in sets.items() if player == who]
        prescribed = sum(mu * prescribed_value(node, who, profile) for node, mu in beliefs[infoset])
        for choice in product(*(sets[name][1] for name in own)):
            policy = dict(zip(own, choice))
            if sum(mu * value(node, who, profile, policy) for node, mu in beliefs[infoset]) > prescribed:
                failing.append(infoset)
                if first_only:
                    return failing
                break
    return failing


def bob_belief(root: Node, profile: Profile, tremble: Profile, infoset: str,
               keep: slice) -> dict[str, str]:
    """Bob's limit belief at `infoset` over the projected hidden state (v, a)."""
    out: dict[tuple, Fraction] = {}
    for node, mu in consistent_beliefs(root, profile, tremble).get(infoset, []):
        key = node.children[0][1].outcome[keep]
        out[key] = out.get(key, Fraction(0)) + mu
    return {str(k): str(mu) for k, mu in sorted(out.items()) if mu}


def source_law(kind: str) -> dict:
    profile = {f"commit{v}": pure(str(v), "0", "1") for v in TYPES} | {"guess": uniform("0", "1")}
    root = source(kind, Fraction(0), extended=False)
    assert not violations(root, profile, uniform_trembles(root))
    return law(root, profile)


def extended_equilibrium(kind: str, deposit: Fraction, tremble: Profile | None = None) -> Profile:
    """The extended-source profile, with play after a miss supplied as Bob's best reply.

    Alice commits a = v and never misses; Bob mixes at `guess`. Bob's play at
    `after_miss` is computed from the limit belief, as the restriction
    extension would supply it.
    """
    root = source(kind, deposit, extended=True)
    tremble = uniform_trembles(root) if tremble is None else tremble
    profile = {f"commit{v}": pure(str(v), "0", "1", MISS) for v in TYPES}
    profile |= {"guess": uniform("0", "1"), "after_miss": uniform("0", "1")}
    belief = consistent_beliefs(root, profile, tremble)["after_miss"]
    payoff = {b: sum(mu * dict(node.children)[b].payoff[BOB] for node, mu in belief) for b in "01"}
    best = max(payoff.values())
    winners = [b for b in "01" if payoff[b] == best]
    profile["after_miss"] = pure(winners[0], "0", "1") if len(winners) == 1 else uniform("0", "1")
    return profile


def compile_profile(extended: Profile) -> Profile:
    """Target image: send now as in the source, decide later the same way, Bob ignores timing."""
    out: Profile = {}
    for v in TYPES:
        commit = extended[f"commit{v}"]
        out[f"turn1_{v}"] = {"send0": commit["0"], "send1": commit["1"], "defer": commit[MISS]}
        stay = 1 - commit[MISS]
        out[f"turn2_{v}"] = {"send0": commit["0"] / stay, "send1": commit["1"] / stay,
                             "silent": Fraction(0)}
    out["t1"] = out["t2"] = extended["guess"]
    out["miss"] = extended["after_miss"]
    return out


def mixture_identity(kind: str, deposit: Fraction, grant: dict[int, Fraction],
                     extended: Profile, compiled: Profile) -> bool:
    """Alice's target value of deferring then playing x equals the source mixture.

    For each value v and each turn-2 action x, against the compiled profile,
    value(defer, x) = (1 - p) * value(miss) + p * value(x) in the extended source.
    """
    turn1s = [node for _, node in target(kind, deposit, grant).branches]
    commits = [node for _, node in source(kind, deposit, extended=True).branches]
    for v, x in product(TYPES, ("send0", "send1", "silent")):
        turn1, commit = turn1s[v], commits[v]
        left = value(turn1, ALICE, compiled, {f"turn1_{v}": "defer", f"turn2_{v}": x})
        source_x = MISS if x == "silent" else x[-1]
        later = value(commit, ALICE, extended, {f"commit{v}": source_x})
        now_miss = value(commit, ALICE, extended, {f"commit{v}": MISS})
        if left != (1 - grant[v]) * now_miss + grant[v] * later:
            return False
    return True


def route(kind: str, deposit: Fraction, grant: dict[int, Fraction],
          extended_tremble: Profile | None = None) -> dict[str, object]:
    """Extended-source equilibrium, compiled; is the image a target equilibrium?"""
    sroot = source(kind, deposit, extended=True)
    stremble = uniform_trembles(sroot) if extended_tremble is None else extended_tremble
    ext = extended_equilibrium(kind, deposit, stremble)
    troot = target(kind, deposit, grant)
    ttremble = uniform_trembles(troot)
    compiled = compile_profile(ext)
    sets = infosets(troot)
    beliefs_match = (
        bob_belief(troot, compiled, ttremble, "miss", slice(0, 1))
        == bob_belief(sroot, ext, stremble, "after_miss", slice(0, 1))
        and all(bob_belief(troot, compiled, ttremble, name, slice(0, 2))
                == bob_belief(sroot, ext, stremble, "guess", slice(0, 2))
                for name in ("t1", "t2") if name in sets))
    return {
        "extended_source_violations": violations(sroot, ext, stremble),
        "after_miss_play": {b: str(w) for b, w in ext["after_miss"].items()},
        "target_violations": violations(troot, compiled, ttremble),
        "target_law_is_source_law": law(troot, compiled) == source_law(kind),
        "beliefs_match_extended_source": beliefs_match,
        "mixture_identity": mixture_identity(kind, deposit, grant, ext, compiled),
        "target_beliefs": {name: bob_belief(troot, compiled, ttremble, name, slice(0, 2))
                           for name in ("t1", "t2", "miss") if name in sets},
    }


def bob_mix(x: Fraction) -> dict[str, Fraction]:
    return {"0": 1 - x, "1": x}


TURN2_OPTIONS = {
    "send0": pure("send0", "send0", "send1", "silent"),
    "send1": pure("send1", "send0", "send1", "silent"),
    "silent": pure("silent", "send0", "send1", "silent"),
    "mix": {"send0": HALF, "send1": HALF, "silent": Fraction(0)},
}


def source_law_equilibria(kind: str, deposit: Fraction, grant: dict[int, Fraction]) -> list[str]:
    """Target equilibria with the source law and Alice sending a = v at turn 1.

    The family: Alice's turn-2 play per value in TURN2_OPTIONS; Bob uniform at
    `t1` (forced by the source law) and plays `1` with probability in
    {0, 1/4, 1/2, 3/4, 1} at `t2` and at `miss`; uniform trembles (deferral
    weight independent of v). Bob is not required to ignore timing here, and
    late play need not repeat the source action.
    """
    root = target(kind, deposit, grant)
    tremble = uniform_trembles(root)
    goal = source_law(kind)
    grid = tuple(Fraction(k, 4) for k in range(5))
    found = []
    for t0, t1, x2, xm in product(TURN2_OPTIONS, TURN2_OPTIONS, grid, grid):
        profile = {f"turn1_{v}": pure(f"send{v}", "send0", "send1", "defer") for v in TYPES}
        profile |= {"turn2_0": TURN2_OPTIONS[t0], "turn2_1": TURN2_OPTIONS[t1],
                    "t1": uniform("0", "1"), "t2": bob_mix(x2), "miss": bob_mix(xm)}
        if law(root, profile) == goal and not violations(root, profile, tremble, first_only=True):
            found.append(f"turn2=({t0},{t1}) P(t2 plays 1)={x2} P(miss plays 1)={xm} "
                         f"miss belief={bob_belief(root, profile, tremble, 'miss', slice(0, 1))}")
    return found


def late_silence(grant: Fraction, deposit: Fraction) -> Profile:
    """A source-law equilibrium below the deposit threshold, outside the route.

    Value 0, if granted a late turn, stays silent with probability
    s = (1 - p) / p and otherwise sends a uniform bit; value 1 sends a uniform
    bit late. A miss then has order-epsilon weight (1 - p) + p s = 1 for
    value 0 and 1 - p for value 1, so Bob's post-miss belief is P(v = 1) = 1/3
    and he is indifferent; he proceeds with probability 1/2 + D, which makes a
    miss worth exactly 1/2 to Alice. Needs p >= 1/2 (so s <= 1) and D <= 1/2.
    """
    s = (1 - grant) / grant
    late_mix = {"send0": (1 - s) / 2, "send1": (1 - s) / 2, "silent": s}
    profile = {f"turn1_{v}": pure(f"send{v}", "send0", "send1", "defer") for v in TYPES}
    profile |= {"turn2_0": late_mix, "turn2_1": TURN2_OPTIONS["mix"], "t1": uniform("0", "1"),
                "t2": uniform("0", "1"), "miss": bob_mix(HALF + deposit)}
    return profile


def flat(grant: Fraction) -> dict[int, Fraction]:
    return {v: grant for v in TYPES}


def report() -> dict[str, object]:
    cases: dict[str, object] = {}

    # Checks 1 and 2: existence with Bob ignoring timing, via the route.
    existence: dict[str, object] = {}
    for kind, p, deposit in product(KINDS, GRANTS, DEPOSITS):
        result = route(kind, deposit, flat(p))
        holds = not result["target_violations"]
        assert result["target_law_is_source_law"]
        assert result["beliefs_match_extended_source"]
        assert result["mixture_identity"]
        assert result["after_miss_play"] == {"0": "0", "1": "1"}
        # The route works exactly when the penalty pays the miss comparison,
        # in the extended source and in the target alike.
        assert holds == (not result["extended_source_violations"]) == (deposit >= DEPOSIT_THRESHOLD)
        existence[f"{kind} p={p} D={deposit}"] = {
            "source_law_equilibrium_ignoring_timing": holds,
            "target_violations": result["target_violations"]}
    cases["C6_route_existence"] = existence

    # Below the threshold, search a wider family in which late play and Bob's
    # play at t2 and after a miss are free. With p = 0 the miss belief is the
    # prior (deferral weight is independent of v), Bob proceeds, and a miss is
    # worth 1 - D > 1/2. With p = 1 a value that stays silent late makes the
    # miss reveal it at order epsilon. With p = 1/2 the search finds
    # equilibria outside the route; see late_silence.
    below = {}
    for kind, p, deposit in product(KINDS, GRANTS, (Fraction(0), Fraction(1, 4))):
        found = source_law_equilibria(kind, deposit, flat(p))
        assert bool(found) == (p == HALF)
        below[f"{kind} p={p} D={deposit}"] = found
    cases["C6_family_search_below_threshold"] = below
    late = {}
    for kind, p, deposit in product(KINDS, (HALF, Fraction(3, 4), Fraction(9, 10)),
                                    (Fraction(0), Fraction(1, 4), Fraction(2, 5))):
        root = target(kind, deposit, flat(p))
        tremble = uniform_trembles(root)
        profile = late_silence(p, deposit)
        assert not violations(root, profile, tremble)
        assert law(root, profile) == source_law(kind)
        assert bob_belief(root, profile, tremble, "miss", slice(0, 1)) == {"(0,)": "2/3",
                                                                           "(1,)": "1/3"}
        late[f"{kind} p={p} D={deposit}"] = True
    cases["C6_late_silence_equilibria_below_threshold"] = late

    # Control (a): the grant depends on Alice's private value.
    skewed = {0: Fraction(1, 4), 1: Fraction(3, 4)}
    control_a = {}
    for kind in KINDS:
        naive = route(kind, Fraction(1), skewed)
        assert "miss" in naive["target_violations"] and "t2" in naive["target_violations"]
        assert not naive["beliefs_match_extended_source"]
        # Repair attempt: give the extended source miss trembles in the ratio
        # 1 - p_v, so its post-miss belief matches the target. Bob's play after
        # a miss is then rational, but accepted-at-turn-2 still reveals v.
        sroot = source(kind, Fraction(1), extended=True)
        matched = uniform_trembles(sroot) | {
            f"commit{v}": {MISS: (1 - skewed[v]) / 2, "0": (1 + skewed[v]) / 4,
                           "1": (1 + skewed[v]) / 4} for v in TYPES}
        repaired = route(kind, Fraction(1), skewed, matched)
        assert repaired["target_violations"] == ["t2"]
        assert repaired["after_miss_play"] == {"0": "1", "1": "0"}
        # Existence itself survives, through profiles the route does not build:
        # late play mixes, so Bob is indifferent at t2, and the miss reveals
        # v = 0 often enough that Bob aborts, so a miss is worth -D.
        family = {str(d): source_law_equilibria(kind, d, skewed)
                  for d in (Fraction(0), HALF, Fraction(1))}
        assert all(family.values())
        control_a[kind] = {
            "naive": {k: naive[k] for k in ("target_violations", "target_beliefs",
                                            "mixture_identity")},
            "miss_trembles_matched": {k: repaired[k] for k in ("target_violations",
                                                               "after_miss_play")},
            "family_equilibria_by_deposit": family,
        }
    cases["C6_control_a_value_dependent_grant"] = control_a

    # Control (b): D = 0. Defer-then-silent is a profitable miss.
    for kind, p in product(KINDS, GRANTS):
        failing = route(kind, Fraction(0), flat(p))["target_violations"]
        assert "turn1_0" in failing and "turn1_1" in failing
    cases["C6_control_b_zero_deposit_rejected"] = True

    # Control (c): Bob aborts after a miss although his belief is the prior.
    control_c = {}
    for kind, p in product(KINDS, GRANTS):
        compiled = compile_profile(extended_equilibrium(kind, Fraction(1)))
        compiled["miss"] = pure("0", "0", "1")
        root = target(kind, Fraction(1), flat(p))
        failing = violations(root, compiled, uniform_trembles(root))
        assert failing == ["miss"]
        control_c[f"{kind} p={p}"] = failing
    cases["C6_control_c_irrational_post_miss"] = control_c

    # Check 4: timing as cheap talk. Value 0 sends at turn 1, value 1 defers
    # and sends at turn 2; Bob reads the timing. Separation needs a free late
    # turn (p = 1) and common interest; with p < 1 value 1 prefers sending 0
    # at turn 1 to risking a miss, and in pennies Alice never wants to be read.
    signal = {}
    for kind, p, deposit in product(KINDS, (HALF, Fraction(1)), (HALF, Fraction(1))):
        root = target(kind, deposit, flat(p))
        tremble = uniform_trembles(root)
        separating = {"turn1_0": pure("send0", "send0", "send1", "defer"),
                      "turn1_1": pure("defer", "send0", "send1", "defer"),
                      "turn2_0": TURN2_OPTIONS["send1"], "turn2_1": TURN2_OPTIONS["send1"],
                      "t1": pure("0", "0", "1"), "t2": pure("1", "0", "1"),
                      "miss": pure("1", "0", "1")}
        uses_signal = not violations(root, separating, tremble)
        babbling = not route(kind, deposit, flat(p))["target_violations"]
        assert babbling
        assert uses_signal == (kind == "coordination" and p == 1)
        signal[f"{kind} p={p} D={deposit}"] = {
            "signalling_equilibrium": uses_signal,
            "signalling_law_is_source_law": law(root, separating) == source_law(kind),
            "source_law_equilibrium": babbling}
    cases["C6_timing_signal"] = signal
    return cases


if __name__ == "__main__":
    print(json.dumps(report(), indent=2, default=str))
