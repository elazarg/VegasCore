#!/usr/bin/env python3
"""Exact finite probe for beliefs after protected waiting and late censorship.

Nature privately tells the sender Good or Bad, each with probability 1/2.
The source sender chooses TRUE (disclose the type) or FALSE (withhold). The
receiver guesses the type and earns 1 for a correct guess. Sender payoffs are:

* Good: accepted TRUE earns 2 plus the correct-guess reward; FALSE earns that
  reward alone. Thus the source equilibrium's TRUE payoff is 3.
* Bad: accepted TRUE earns the correct-guess reward; FALSE earns twice that
  reward. Thus the source equilibrium's TRUE payoff is 1.

Both types choose TRUE in the source equilibrium. Off-path FALSE is answered
Good, consistently with Good FALSE trembles epsilon and Bad FALSE trembles
epsilon squared. Bad therefore cannot improve by choosing FALSE.

The native game adds early wait and a subsequent late TRUE/FALSE/wait turn.
Every early packet is accepted. At the late turn, Good TRUE and either type's
FALSE are accepted; Bad TRUE is censored until expiry. Late wait also expires.
The builder reads the type from the publicly visible TRUE packet, not hidden
state. A public miss uses the actual default FALSE payoff minus the escrow D.
The receiver sees early/late timing, accepted TRUE contents, and the miss flag;
it does not see the censored pending TRUE packet in the miss information set.

The timing pattern is early clock 0, late clock 1, inclusion bound 2, deadline
3: the first turn is protected; the late turn remains timely but unprotected.
This tree is not a certified AsyncServiceSpec or a watcher-backend theorem.
It contains only the stated local actions and does not classify other packets.

All early, late, and receiver actions have strictly positive trembles along
epsilon = 1/(n+4). Late laws mix epsilon of the uniform three-action reference
with Good TRUE or Bad FALSE. Receiver laws mix epsilon of the uniform two-guess
reference with their Bayes best reply. Two early waiting families are tested:
equal waits epsilon, or Good epsilon and Bad epsilon cubed. Exact polynomial
reach weights determine every limiting belief. Every whole replacement policy
is checked at every information set, including public misses.

Equal waiting gives a consistent, rational free continuation but makes Bad's
initial wait profitable. Type-dependent waiting gives a consistent rational
limit preserving the source law in this finite game. This is evidence that an
event-only geometric family can be too restrictive, not a general preservation
result or a native sequential-equilibrium impossibility claim.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
import json

from adaptive_schedules import (
    ALICE, BOB, HALF, Chance, End, Move, Node, Poly, Profile, infosets, law,
    poly_add, poly_mul, prescribed_value, pure, value,
)


GOOD, BAD = 0, 1
TYPES = (GOOD, BAD)
NAMES = {GOOD: "Good", BAD: "Bad"}
TRUE, FALSE, WAIT = "TRUE", "FALSE", "wait"
GUESSES = ("Good", "Bad")
DECISIONS = (TRUE, FALSE, WAIT)
DEPOSIT = Fraction(10)
ZERO, ONE = Fraction(0), Fraction(1)
PolynomialProfile = dict[str, dict[str, Poly]]
Beliefs = dict[str, list[tuple[Move, Fraction]]]


def terminal(kind: int, disclosed: bool, missed: bool, guess: int) -> End:
    """Misses evaluate FALSE, even when the censored attempted action was TRUE."""
    assert not (disclosed and missed)
    correct = Fraction(kind == guess)
    if disclosed:
        sender = correct + (2 if kind == GOOD else 0)
    else:
        sender = correct * (1 if kind == GOOD else 2)
    return End((sender - DEPOSIT * missed, correct), (kind, disclosed, missed, guess))


def receiver(site: str, kind: int, disclosed: bool, missed: bool = False) -> Move:
    return Move(BOB, site, tuple(
        (NAMES[guess], terminal(kind, disclosed, missed, guess)) for guess in TYPES))


def source() -> Node:
    return Chance(tuple((HALF, Move(ALICE, f"early:{NAMES[kind]}", (
        (TRUE, receiver(f"early:TRUE:{NAMES[kind]}", kind, True)),
        (FALSE, receiver("early:FALSE", kind, False))))) for kind in TYPES))


def native() -> Node:
    def late(kind: int) -> Move:
        true = (receiver("late:TRUE:Good", kind, True) if kind == GOOD else
                receiver("public-miss", kind, False, True))
        return Move(ALICE, f"late:{NAMES[kind]}", (
            (TRUE, true), (FALSE, receiver("late:FALSE", kind, False)),
            (WAIT, receiver("public-miss", kind, False, True))))

    return Chance(tuple((HALF, Move(ALICE, f"early:{NAMES[kind]}", (
        (TRUE, receiver(f"early:TRUE:{NAMES[kind]}", kind, True)),
        (FALSE, receiver("early:FALSE", kind, False)),
        (WAIT, late(kind))))) for kind in TYPES))


def candidate(root: Node, dependent_wait: bool) -> Profile:
    result = {}
    for site, (who, actions) in infosets(root).items():
        if who == ALICE:
            chosen = FALSE if site == "late:Bad" else TRUE
        elif site in ("late:FALSE", "public-miss"):
            chosen = "Good" if dependent_wait else "Bad"
        else:
            chosen = "Bad" if site.endswith("TRUE:Bad") else "Good"
        result[site] = pure(chosen, *actions)
    return result


def polynomial_family(root: Node, dependent_wait: bool) -> PolynomialProfile:
    """The native pinned early laws and fully supported free continuation laws."""
    limit = candidate(root, dependent_wait)
    result = {}
    for site, (who, actions) in infosets(root).items():
        if site.startswith("early:") and who == ALICE:
            false = (ZERO, ONE) if site.endswith("Good") else (ZERO, ZERO, ONE)
            wait = ((ZERO, ZERO, ZERO, ONE) if dependent_wait and site.endswith("Bad")
                    else (ZERO, ONE))
            negatives = poly_add(false, wait) if WAIT in actions else false
            result[site] = {TRUE: poly_add((ONE,), tuple(-c for c in negatives)),
                            FALSE: false}
            if WAIT in actions:
                result[site][WAIT] = wait
        else:
            # Late sender and receiver residual choices tremble uniformly.
            result[site] = {
                action: (limit[site][action], Fraction(1, len(actions)) - limit[site][action])
                for action in actions}
    return result


def evaluate(poly: Poly, epsilon: Fraction) -> Fraction:
    return sum((coefficient * epsilon ** power for power, coefficient in enumerate(poly)), ZERO)


def evaluate_family(family: PolynomialProfile, epsilon: Fraction) -> Profile:
    assert ZERO < epsilon <= Fraction(1, 4)
    result = {site: {action: evaluate(poly, epsilon) for action, poly in choices.items()}
              for site, choices in family.items()}
    assert all(sum(choices.values()) == ONE and all(p > ZERO for p in choices.values())
               for choices in result.values())
    return result


def polynomial_reach(root: Node, family: PolynomialProfile) -> dict[str, list[tuple[Move, Poly]]]:
    """Full reach weights, including nature, waiting, and subsequent mistakes."""
    reached = {}

    def visit(node: Node, weight: Poly) -> None:
        if isinstance(node, Chance):
            for probability, child in node.branches:
                visit(child, poly_mul(weight, (probability,)))
        elif isinstance(node, Move):
            reached.setdefault(node.infoset, []).append((node, weight))
            for action, child in node.children:
                visit(child, poly_mul(weight, family[node.infoset][action]))

    visit(root, (ONE,))
    return reached


def leading(poly: Poly) -> tuple[int, Fraction]:
    return next((power, coefficient) for power, coefficient in enumerate(poly) if coefficient)


def format_polynomial(poly: Poly) -> str:
    return " + ".join(f"({coefficient})*epsilon^{power}"
                      for power, coefficient in enumerate(poly) if coefficient) or "0"


def limiting_beliefs(root: Node, family: PolynomialProfile) -> Beliefs:
    result = {}
    for site, members in polynomial_reach(root, family).items():
        total = (ZERO,)
        for _, weight in members:
            total = poly_add(total, weight)
        order, coefficient = leading(total)
        assert coefficient > ZERO
        result[site] = [(node, (weight[order] if order < len(weight) else ZERO) / coefficient)
                        for node, weight in members]
        assert sum(probability for _, probability in result[site]) == ONE
    return result


def node_kind(node: Move) -> int:
    # Every receiver child is a terminal with the same actual type.
    child = node.children[0][1]
    assert isinstance(child, End)
    return child.outcome[0]


def type_weights(root: Node, family: PolynomialProfile, site: str) -> dict[int, Poly]:
    result = {kind: (ZERO,) for kind in TYPES}
    for node, weight in polynomial_reach(root, family)[site]:
        kind = node_kind(node)
        result[kind] = poly_add(result[kind], weight)
    return result


def bad_posterior(root: Node, family: PolynomialProfile, site: str,
                  epsilon: Fraction) -> Fraction:
    weights = type_weights(root, family, site)
    good, bad = (evaluate(weights[kind], epsilon) for kind in TYPES)
    return bad / (good + bad)


def bad_limit(beliefs: Beliefs, site: str) -> Fraction:
    return sum((p for node, p in beliefs[site] if node_kind(node) == BAD), ZERO)


def rationality(root: Node, profile: Profile, beliefs: Beliefs) -> dict[str, Fraction]:
    """Check every whole pure replacement continuation, not only one action."""
    sets = infosets(root)
    failures = {}
    for site, (who, _) in sets.items():
        members = beliefs[site]
        actual = sum(p * prescribed_value(node, who, profile) for node, p in members)
        own = [name for name, (player, _) in sets.items() if player == who]
        best = actual
        for choices in product(*(sets[name][1] for name in own)):
            policy = dict(zip(own, choices))
            best = max(best, sum(p * value(node, who, profile, policy) for node, p in members))
        if best > actual:
            failures[site] = best - actual
    return failures


def action_values(root: Node, profile: Profile, site: str) -> dict[str, Fraction]:
    """Local values under the displayed continuation (whole replacements also checked)."""
    node = next(node for node, _ in polynomial_reach(
        root, polynomial_family(root, True))[site])
    return {action: prescribed_value(child, node.player, profile)
            for action, child in node.children}


def residual_best_responses(root: Node, family: PolynomialProfile,
                            limit: Profile, epsilon: Fraction) -> bool:
    """Free residual laws are best replies under their actual perturbed Bayes beliefs."""
    profile = evaluate_family(family, epsilon)
    for site, (who, _) in infosets(root).items():
        if who == ALICE and site.startswith("early:"):
            continue
        members = polynomial_reach(root, family)[site]
        total = sum(evaluate(weight, epsilon) for _, weight in members)
        values = {
            action: sum(evaluate(weight, epsilon) * prescribed_value(
                dict(node.children)[action], who, profile) for node, weight in members) / total
            for action in profile[site]}
        selected = next(action for action, probability in limit[site].items() if probability)
        if values[selected] != max(values.values()):
            return False
    return True


def report() -> dict[str, object]:
    source_root, root = source(), native()
    source_profile = candidate(source_root, True)
    source_family = polynomial_family(source_root, True)
    source_beliefs = limiting_beliefs(source_root, source_family)
    assert not rationality(source_root, source_profile, source_beliefs)
    assert bad_limit(source_beliefs, "early:FALSE") == ZERO
    assert terminal(GOOD, False, True, GOOD).payoff[ALICE] == 1 - DEPOSIT
    assert terminal(BAD, False, True, BAD).payoff[ALICE] == 2 - DEPOSIT
    assert 0 + 2 < 3 and 1 < 3 and not 1 + 2 < 3

    result = {
        "scope": "Finite signaling tree; not a certified AsyncServiceSpec/backend theorem",
        "source_equilibrium": True,
        "source_FALSE_trembles": {"Good": "epsilon", "Bad": "epsilon^2"},
        "public_miss_outcome": "default FALSE minus D=10; no intended-TRUE bonus",
        "families": {},
    }
    for dependent in (False, True):
        name = "type_dependent_wait" if dependent else "equal_wait"
        profile = candidate(root, dependent)
        family = polynomial_family(root, dependent)
        beliefs = limiting_beliefs(root, family)
        failures = rationality(root, profile, beliefs)
        assert failures == ({} if dependent else {"early:Bad": ONE})
        assert law(root, profile) == law(source_root, source_profile)
        assert all(evaluate(poly, ZERO) == profile[site][action]
                   for site, choices in family.items() for action, poly in choices.items())
        samples = []
        for epsilon in (Fraction(1, 4), Fraction(1, 10), Fraction(1, 100), Fraction(1, 1000)):
            perturbed = evaluate_family(family, epsilon)
            assert sum(law(root, perturbed).values()) == ONE
            assert residual_best_responses(root, family, profile, epsilon)
            samples.append({
                "epsilon": str(epsilon),
                "P(Bad|early_FALSE)": str(bad_posterior(root, family, "early:FALSE", epsilon)),
                "P(Bad|late_FALSE)": str(bad_posterior(root, family, "late:FALSE", epsilon)),
                "P(Bad|public_miss)": str(bad_posterior(root, family, "public-miss", epsilon)),
            })
        result["families"][name] = {
            "early_wait": {"Good": "epsilon", "Bad": "epsilon^3" if dependent else "epsilon"},
            "late_reference": "epsilon/3 at each action plus (1-epsilon) residual",
            "actual_Bayes_reach_weights": {
                site: {NAMES[kind]: format_polynomial(weight)
                       for kind, weight in type_weights(root, family, site).items()}
                for site in ("early:FALSE", "late:FALSE", "public-miss")},
            "limiting_Bad_beliefs": {
                site: str(bad_limit(beliefs, site))
                for site in ("early:FALSE", "late:FALSE", "public-miss")},
            "limit_receiver_guesses": {
                site: next(action for action, p in profile[site].items() if p)
                for site in ("early:FALSE", "late:FALSE", "public-miss")},
            "limit_sender_action_values": {
                site: {action: str(p) for action, p in action_values(root, profile, site).items()}
                for site in ("early:Good", "early:Bad", "late:Good", "late:Bad")},
            "whole_policy_incentive_violations": {
                site: str(gain) for site, gain in failures.items()},
            "source_terminal_law_preserved": True,
            "finite_free_residual_best_reply_samples": True,
            "Bayes_samples": samples,
        }
    return result


if __name__ == "__main__":
    print(json.dumps(report(), indent=2))
