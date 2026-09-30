#!/usr/bin/env python3
"""Finite design probes for sequential equilibrium under adaptive schedules.

Two players commit concurrently in a coordination game: Alice commits a bit,
Bob commits a bit without seeing it, and both receive 1 when the bits agree.
The source has the fully mixed sequential equilibrium in which both mix
uniformly, whose law of (Alice, Bob) is uniform. Each target lets a public
order policy react to the pending pool and lets Bob observe the resulting
order. The question is whether some target sequential equilibrium has the
source law.

Beliefs are Kreps-Wilson consistent: they are the exact limits of Bayes
beliefs along one explicit tremble sequence, computed with polynomials in the
tremble size. Sequential rationality compares every whole replacement policy
at every information set. Nonexistence claims use a separate argument, stated
where it is made. These are design probes, not a Vegas adapter or a general
equilibrium checker; see docs/se-schedule-generalization.md.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
import json


ALICE, BOB = 0, 1
HALF = Fraction(1, 2)
Poly = tuple[Fraction, ...]


@dataclass(frozen=True)
class Chance:
    branches: tuple[tuple[Fraction, "Node"], ...]


@dataclass(frozen=True)
class Move:
    player: int
    infoset: str
    children: tuple[tuple[str, "Node"], ...]


@dataclass(frozen=True)
class End:
    payoff: tuple[Fraction, Fraction]
    outcome: tuple[int, int]


Node = Chance | Move | End
Profile = dict[str, dict[str, Fraction]]


def poly_mul(p: Poly, q: Poly) -> Poly:
    out = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return tuple(out)


def poly_add(p: Poly, q: Poly) -> Poly:
    n = max(len(p), len(q))
    return tuple((p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n))


def infosets(node: Node, out: dict[str, tuple[int, tuple[str, ...]]] | None = None):
    out = {} if out is None else out
    if isinstance(node, Chance):
        for _, child in node.branches:
            infosets(child, out)
    elif isinstance(node, Move):
        actions = tuple(a for a, _ in node.children)
        assert out.setdefault(node.infoset, (node.player, actions)) == (node.player, actions)
        for _, child in node.children:
            infosets(child, out)
    return out


def reach(node: Node, profile: Profile, tremble: Profile, weight: Poly = (Fraction(1),),
          out: dict[str, list[tuple[Node, Poly]]] | None = None):
    """Reach polynomial of every decision node under (1 - e) profile + e tremble."""
    out = {} if out is None else out
    if isinstance(node, Chance):
        for probability, child in node.branches:
            reach(child, profile, tremble, poly_mul(weight, (probability,)), out)
    elif isinstance(node, Move):
        out.setdefault(node.infoset, []).append((node, weight))
        for action, child in node.children:
            sigma = profile[node.infoset][action]
            step = (sigma, tremble[node.infoset][action] - sigma)
            reach(child, profile, tremble, poly_mul(weight, step), out)
    return out


def consistent_beliefs(root: Node, profile: Profile, tremble: Profile):
    """Limit beliefs: the lowest-order terms of the reach polynomials."""
    beliefs = {}
    for infoset, members in reach(root, profile, tremble).items():
        total: Poly = (Fraction(0),)
        for _, weight in members:
            total = poly_add(total, weight)
        order = next(k for k, c in enumerate(total) if c != 0)
        beliefs[infoset] = [(node, (weight[order] if order < len(weight) else Fraction(0))
                             / total[order]) for node, weight in members]
    return beliefs


def value(node: Node, who: int, profile: Profile, policy: dict[str, str]) -> Fraction:
    """Expected payoff of `who` when `who` follows `policy` and others follow `profile`."""
    if isinstance(node, End):
        return node.payoff[who]
    if isinstance(node, Chance):
        return sum(p * value(child, who, profile, policy) for p, child in node.branches)
    if node.player == who:
        child = dict(node.children)[policy[node.infoset]]
        return value(child, who, profile, policy)
    return sum(profile[node.infoset][a] * value(child, who, profile, policy)
               for a, child in node.children)


def prescribed_value(node: Node, who: int, profile: Profile) -> Fraction:
    if isinstance(node, End):
        return node.payoff[who]
    if isinstance(node, Chance):
        return sum(p * prescribed_value(child, who, profile) for p, child in node.branches)
    return sum(profile[node.infoset][a] * prescribed_value(child, who, profile)
               for a, child in node.children)


def is_sequential_equilibrium(root: Node, profile: Profile, tremble: Profile) -> bool:
    sets = infosets(root)
    beliefs = consistent_beliefs(root, profile, tremble)
    for infoset, (who, _) in sets.items():
        own = [name for name, (player, _) in sets.items() if player == who]
        prescribed = sum(mu * prescribed_value(node, who, profile) for node, mu in beliefs[infoset])
        for choice in product(*(sets[name][1] for name in own)):
            policy = dict(zip(own, choice))
            deviation = sum(mu * value(node, who, profile, policy) for node, mu in beliefs[infoset])
            if deviation > prescribed:
                return False
    return True


def law(node: Node, profile: Profile, weight: Fraction = Fraction(1),
        out: dict[tuple[int, int], Fraction] | None = None):
    out = {} if out is None else out
    if isinstance(node, End):
        out[node.outcome] = out.get(node.outcome, Fraction(0)) + weight
    elif isinstance(node, Chance):
        for p, child in node.branches:
            law(child, profile, weight * p, out)
    else:
        for a, child in node.children:
            if profile[node.infoset][a]:
                law(child, profile, weight * profile[node.infoset][a], out)
    return out


def end(bit: int, guess: int, charge: Fraction = Fraction(0)) -> End:
    agree = Fraction(int(bit == guess))
    return End((agree - charge, agree), (bit, guess))


def uniform(*actions: str) -> dict[str, Fraction]:
    return {a: Fraction(1, len(actions)) for a in actions}


def pure(action: str, *actions: str) -> dict[str, Fraction]:
    return {a: Fraction(int(a == action)) for a in actions}


def bob(infoset: str, bit: int, charge: Fraction = Fraction(0)) -> Move:
    return Move(BOB, infoset, (("0", end(bit, 0, charge)), ("1", end(bit, 1, charge))))


SOURCE_LAW = {(a, b): Fraction(1, 4) for a in (0, 1) for b in (0, 1)}


def source() -> Node:
    return Move(ALICE, "commit", tuple((str(a), bob("guess", a)) for a in (0, 1)))


def signalling(signal: str, charge: Fraction, reveals: bool) -> Node:
    """Alice commits, then either stays quiet or sends `signal` to the pool.

    The public order after a signal is `first` when Alice's bit is zero and
    `second` otherwise if the order policy can read the bit (`reveals`); with
    an unverified signal it is `first` in both cases. Bob sees only the order.
    """
    def after(bit: int) -> Move:
        order = ("first" if bit == 0 else "second") if reveals else "first"
        return Move(ALICE, f"signal{bit}", (
            ("quiet", bob("normal", bit)),
            (signal, bob(order, bit, charge)),
        ))
    return Move(ALICE, "commit", tuple((str(a), after(a)) for a in (0, 1)))


def translated_profile(extra: dict[str, dict[str, Fraction]]) -> Profile:
    base = {"commit": uniform("0", "1"), "signal0": pure("quiet", "quiet", "sig"),
            "signal1": pure("quiet", "quiet", "sig"), "normal": uniform("0", "1")}
    base.update(extra)
    return base


def trembles() -> Profile:
    """Signal trembles independent of the committed bit."""
    return {"commit": uniform("0", "1"), "signal0": uniform("quiet", "sig"),
            "signal1": uniform("quiet", "sig"), "normal": uniform("0", "1"),
            "first": uniform("0", "1"), "second": uniform("0", "1"), "guess": uniform("0", "1")}


def verified_gain(charge: Fraction) -> Fraction:
    """Alice's payoff from signalling when the order reveals her bit.

    Bob's information after a revealing order is a single committed bit, so
    every consistent belief is the point mass on it and matching is Bob's
    unique best response. Alice's payoff from signalling is therefore
    1 - charge in every sequentially rational assessment, while any assessment
    with the source law gives her 1/2 on path. Signalling is profitable, and
    no such assessment is an equilibrium, exactly when 1 - charge > 1/2.
    """
    return 1 - charge


def deadlines(timers_at_grant: bool, events: int = 3) -> list[dict[str, int | bool]]:
    """Concurrent bindings ready at clock zero, granted in blocks of index + 1 ticks.

    Mirrors `deadline event = event.val + 1` of the reveal service and its
    roster blocks. A timer counts from readiness unless `timers_at_grant`.
    """
    rows, clock = [], 0
    for event in range(events):
        entered = clock if timers_at_grant else 0
        rows.append({"event": event, "granted_at": clock, "deadline": event + 1,
                     "includable": clock - entered < event + 1})
        clock += event + 1
    return rows


def report() -> dict[str, object]:
    cases: dict[str, object] = {}

    root = source()
    profile = {"commit": uniform("0", "1"), "guess": uniform("0", "1")}
    assert is_sequential_equilibrium(root, profile, trembles())
    assert law(root, profile) == SOURCE_LAW
    cases["source_mixed_equilibrium"] = True
    # Negative controls: the checker rejects known non-equilibria.
    lopsided = {"commit": uniform("0", "1"), "guess": pure("0", "0", "1")}
    assert not is_sequential_equilibrium(root, lopsided, trembles())
    ignoring = translated_profile({"first": uniform("0", "1"), "second": uniform("0", "1")})
    assert not is_sequential_equilibrium(signalling("sig", Fraction(1), reveals=True),
                                         ignoring, trembles())
    cases["checker_rejects_non_equilibria"] = True

    # C1: readiness timers expire a concurrent binding; grant timers do not.
    ready, granted = deadlines(False), deadlines(True)
    assert [row["includable"] for row in ready] == [True, True, False]
    assert all(row["includable"] for row in granted)
    cases["C1_readiness_timers"] = ready
    cases["C1_grant_timers"] = granted

    # C2: an order reacting to an unverified claim is cheap talk; babbling works.
    cheap = signalling("sig", Fraction(0), reveals=False)
    babble = translated_profile({"first": uniform("0", "1")})
    assert is_sequential_equilibrium(cheap, babble, trembles())
    assert law(cheap, babble) == SOURCE_LAW
    cases["C2_cheap_talk_source_law_equilibrium"] = True

    # C3: a forbidden certificate, charged by the audit, read by the order.
    matching = {"first": pure("0", "0", "1"), "second": pure("1", "0", "1")}
    c3 = {}
    for charge in (Fraction(1, 4), HALF, Fraction(1)):
        game = signalling("sig", charge, reveals=True)
        candidate = translated_profile(matching)
        holds = is_sequential_equilibrium(game, candidate, trembles())
        assert holds == (verified_gain(charge) <= HALF)
        assert law(game, candidate) == SOURCE_LAW
        c3[str(charge)] = {"source_law_equilibrium": holds,
                           "signal_payoff": str(verified_gain(charge))}
    cases["C3_forbidden_certificate_by_expected_charge"] = c3

    # C4: a permitted, uncharged opening read by the order while Bob's binding
    # is still ungranted. The signal payoff 1 exceeds 1/2, so no assessment
    # with the source law is sequentially rational (see verified_gain). The
    # compiled barrier order excludes this state: a resolution is a public
    # barrier, so no binding is ready while its opening is pending.
    permitted = signalling("sig", Fraction(0), reveals=True)
    assert not is_sequential_equilibrium(permitted, translated_profile(matching), trembles())
    assert verified_gain(Fraction(0)) > HALF
    # An order that ignores certificate contents restores the babbling equilibrium.
    blind = signalling("sig", Fraction(0), reveals=False)
    assert is_sequential_equilibrium(blind, babble, trembles())
    cases["C4_permitted_opening_read_by_order"] = {
        "source_law_equilibrium_exists": False, "signal_payoff": "1",
        "order_blind_to_certificates": True}

    # C5: an unobserved wait before Bob's grant gives Bob's information set
    # histories of different depths; the translated profile remains an
    # equilibrium, so the depth gap is a proof-technique requirement only.
    def waited(bit: int) -> Node:
        return Chance(((HALF, bob("guess", bit)),
                       (HALF, Move(ALICE, f"idle{bit}", (("wait", bob("guess", bit)),)))))
    delayed = Move(ALICE, "commit", tuple((str(a), waited(a)) for a in (0, 1)))
    idle = {"idle0": {"wait": Fraction(1)}, "idle1": {"wait": Fraction(1)}}
    profile = {"commit": uniform("0", "1"), "guess": uniform("0", "1"), **idle}
    assert is_sequential_equilibrium(delayed, profile, {**trembles(), **idle})
    assert law(delayed, profile) == SOURCE_LAW
    cases["C5_mixed_depth_information_set_equilibrium"] = True
    return cases


if __name__ == "__main__":
    print(json.dumps(report(), indent=2))
