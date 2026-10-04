#!/usr/bin/env python3
"""Finite one-escrow probe: rational RAW play after a miss or own attempt.

The source is a hidden-bit coordination game. Alice sees a uniform private v,
commits a bit, and Bob guesses it without seeing the commitment's value. The
source equilibrium commits v and guesses uniformly.

The target keeps a protected send with exactly that source law. Its two extra
branches are deliberately small:

* A public binding miss collects the one escrow certainly. Alice subsequently
  can send her authentic private-input certificate; Bob sees it if she sends.
* An unprotected RAW attempt prepares a private candidate a, but addresses an
  already settled event. It has no observed receipt. Its immutable content and
  the eventual final record make it forbidden, regardless of the later retry.
  Alice remembers a. A fresh retry for the current binding is accepted with a
  chosen bit r, and can optionally attach a's authentic certificate. Attaching
  that certificate is forbidden even though the binding call is accepted.

The watcher samples all forbidden signed records or none with probability p.
Conditional on that observation, its reports are delivered with probability q.
These are explicit backend parameters, not properties of the gameplay service.
All offenses share the same hidden observation/report lottery; every offense
has coverage p*q, but an additional offense need not increase collection. Alice
observes neither this lottery nor a rejection receipt for her first attempt.

RAW completion chooses r=a and sends its certificate; Bob then rationally
guesses a. A fixed canonical continuation chooses r=v without evidence. The
probe compares both using exact Bayes-limit beliefs and every pure replacement
continuation policy, and checks the source law under the protected profile.

A separate control checks second fresh calls after a protected acceptance:
they are deterred while escrow is clear, and are profitable after an earlier
forbidden attempt activates the same one-time collection lottery.

The late-canonical control leaves the first packet genuinely undecided when
Alice chooses whether to send a second call. It is subsequently included with
probability s, otherwise the binding expires. Only the inclusion branch can
increase collection after a retry. Its complete protected-start game retains
Alice's chosen a and supplies rational raw play at every continuation site.

The first-late-content control lets a public-content-dependent builder expire
a bare first late packet while immediately including one with an authentic
certificate. Both packets remain within the actual acceptance deadline, but
the late turn has no protected inclusion window. A bare packet therefore pays
the certain public-miss charge D; an accepted certificate-bearing packet pays
only p*q*D. Raw play must open before this late opportunity, not after its first
attempt. The protected initial turn still accepts every source binding packet.

The due-but-unexpired control activates the owner exactly at the deadline,
before the explicit expiry command. A fresh certificate-bearing packet cannot
be accepted, but can still tell Bob the private input. Silence and transmission
both incur the same certain public-miss charge. Alice has no later opportunity
before Bob chooses, so waiting to open raw play at expiry does not repair this
decision. The binding-risk predicate therefore does not require WithinDeadline.

These finite games are design evidence, not a Vegas runtime adapter or a
general theorem. In particular, an unprotected canonical attempt need not be
forbidden: the private-attempt branch above is explicitly RAW. The current
canonical menu forbids same-event second submissions and extra commitment
evidence. No conclusion assumes those actions are retained.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
import json

from adaptive_schedules import (
    ALICE, BOB, HALF, Chance, End, Move, Node, Profile, consistent_beliefs,
    infosets, law, prescribed_value, pure, uniform, value,
)


ZERO = Fraction(0)
ONE = Fraction(1)
BITS = (0, 1)


@dataclass(frozen=True)
class ReportBackend:
    observation: Fraction
    delivery: Fraction

    def __post_init__(self) -> None:
        assert ZERO <= self.observation <= ONE
        assert ZERO <= self.delivery <= ONE

    @property
    def coverage(self) -> Fraction:
        return self.observation * self.delivery


@dataclass(frozen=True)
class OwnerOpportunity:
    owned_ready: bool
    binding: bool
    within_deadline: bool
    inclusion_fits: bool
    event_recorded: bool

    @property
    def first_unprotected(self) -> bool:
        return (self.owned_ready and self.binding and
                not self.inclusion_fits and not self.event_recorded)


def risk_seen(past: tuple[tuple[OwnerOpportunity, str], ...],
              current: OwnerOpportunity) -> bool:
    """Recall of a risky binding opportunity, independent of its response.

    Lawful source withholding at a resolution is not a binding risk, even
    though it leaves that event unrecorded in own submission recall.
    """
    return current.first_unprotected or any(view.first_unprotected for view, _ in past)


def terminal(v: int, result: int | str, hidden: int, guess: int,
             deposit: Fraction, collected: bool) -> End:
    base = Fraction(hidden == guess)
    return End((base - deposit * collected, base), (v, result, guess, collected))


def settle(v: int, result: int | str, hidden: int, guess: int,
           deposit: Fraction, backend: ReportBackend, forbidden: bool,
           public_miss: bool = False) -> Node:
    unpaid = terminal(v, result, hidden, guess, deposit, False)
    paid = terminal(v, result, hidden, guess, deposit, True)
    if public_miss:
        return paid
    if not forbidden:
        return unpaid
    # The same terminal lottery covers the earlier offense and every retry.
    delivery = Chance(tuple((p, end) for p, end in (
        (backend.delivery, paid), (1 - backend.delivery, unpaid)) if p))
    return Chance(tuple((p, node) for p, node in (
        (backend.observation, delivery), (1 - backend.observation, unpaid)) if p))


def bob(name: str, v: int, result: int | str, hidden: int,
        deposit: Fraction, backend: ReportBackend, forbidden: bool,
        public_miss: bool = False) -> Move:
    return Move(BOB, name, tuple((str(guess), settle(
        v, result, hidden, guess, deposit, backend, forbidden, public_miss))
        for guess in BITS))


def source() -> Node:
    backend = ReportBackend(ONE, ONE)
    return Chance(tuple((HALF, Move(ALICE, f"commit:{v}", tuple(
        (str(bit), bob("guess", v, bit, bit, ZERO, backend, False))
        for bit in BITS))) for v in BITS))


def source_profile() -> Profile:
    return {f"commit:{v}": pure(str(v), "0", "1") for v in BITS} | {
        "guess": uniform("0", "1")}


def target(deposit: Fraction, backend: ReportBackend) -> Node:
    def after_miss(v: int) -> Move:
        return Move(ALICE, f"miss:{v}", (
            ("quiet", bob("miss:quiet", v, "miss", v, deposit, backend, True, True)),
            ("certificate", bob(f"miss:cert{v}", v, "miss", v,
                                deposit, backend, True, True))))

    def after_attempt(v: int, attempted: int) -> Move:
        # The attempted choice is private perfect recall, not a public receipt.
        return Move(ALICE, f"attempt:{v}:{attempted}", tuple(
            (f"retry{bit}:{evidence}", bob(
                "retry:plain" if evidence == "plain" else f"retry:cert{attempted}",
                v, bit, bit, deposit, backend, True))
            for bit, evidence in product(BITS, ("plain", "certificate"))))

    def first(v: int) -> Move:
        protected = tuple((f"send{bit}", bob(
            "protected", v, bit, bit, deposit, backend, False)) for bit in BITS)
        attempts = tuple((f"attempt{bit}", after_attempt(v, bit)) for bit in BITS)
        return Move(ALICE, f"first:{v}", protected + (("miss", after_miss(v)),) + attempts)

    return Chance(tuple((HALF, first(v)) for v in BITS))


def target_profile(root: Node, raw: bool) -> Profile:
    profile = {name: uniform(*actions) for name, (_, actions) in infosets(root).items()}
    for v in BITS:
        name = f"first:{v}"
        profile[name] = pure(f"send{v}", *profile[name])
        name = f"miss:{v}"
        profile[name] = pure("certificate" if raw else "quiet", *profile[name])
        for attempted in BITS:
            name = f"attempt:{v}:{attempted}"
            response = f"retry{attempted}:certificate" if raw else f"retry{v}:plain"
            profile[name] = pure(response, *profile[name])
    for name in profile:
        if "cert" in name and name.startswith(("miss:", "retry:")):
            profile[name] = pure(name[-1], "0", "1")
    return profile


def trembles(root: Node) -> Profile:
    return {name: uniform(*actions) for name, (_, actions) in infosets(root).items()}


def assert_perfect_recall(root: Node) -> None:
    memories: dict[str, tuple[tuple[str, str], ...]] = {}

    def visit(node: Node, past: tuple[tuple[tuple[str, str], ...], ...]) -> None:
        if isinstance(node, Chance):
            for _, child in node.branches:
                visit(child, past)
        elif isinstance(node, Move):
            own = past[node.player]
            assert memories.setdefault(node.infoset, own) == own
            for action, child in node.children:
                updated = list(past)
                updated[node.player] = own + ((node.infoset, action),)
                visit(child, tuple(updated))

    visit(root, ((), ()))


def rationality(root: Node, profile: Profile) -> dict[str, dict[str, object]]:
    """Whole-policy comparison at every information set under exact limit beliefs.

    Choices at unreachable information sets cannot affect a conditional value.
    Enumerating the union of each belief member's descendant information sets
    therefore gives every relevant pure replacement policy, not just a local
    best response. Shared descendant information sets use one common choice.
    """
    sets = infosets(root)
    beliefs = consistent_beliefs(root, profile, trembles(root))
    failures: dict[str, dict[str, object]] = {}
    for name, (who, _) in sets.items():
        members = beliefs[name]
        active: dict[str, tuple[str, ...]] = {}
        for node, _ in members:
            for other, (actor, actions) in infosets(node).items():
                if actor == who:
                    active[other] = actions
        prescribed = sum(mu * prescribed_value(node, who, profile) for node, mu in members)
        best = prescribed
        witness: dict[str, str] | None = None
        for choices in product(*active.values()):
            policy = dict(zip(active, choices))
            candidate = sum(mu * value(node, who, profile, policy) for node, mu in members)
            if candidate > best:
                best, witness = candidate, policy
        if witness is not None:
            failures[name] = {"gain": best - prescribed, "replacement": witness}
    return failures


def protected_retry(deposit: Fraction, backend: ReportBackend,
                    previous_offense: bool) -> Node:
    """The original protected binding is already accepted with hidden bit a."""
    def continuation(bit: int) -> Move:
        return Move(ALICE, f"after_protected:{bit}", (
            ("quiet", bob("control:quiet", bit, bit, bit,
                          deposit, backend, previous_offense)),
            ("fresh_plain", bob("control:plain", bit, bit, bit,
                                deposit, backend, True)),
            ("fresh_certificate", bob(f"control:cert{bit}", bit, bit, bit,
                                      deposit, backend, True))))
    return Chance(tuple((HALF, continuation(bit)) for bit in BITS))


def protected_profile(root: Node, raw: bool) -> Profile:
    profile = trembles(root)
    for name in profile:
        if name.startswith("after_protected:"):
            profile[name] = pure("fresh_certificate" if raw else "quiet", *profile[name])
        elif name.startswith("control:cert"):
            profile[name] = pure(name[-1], "0", "1")
    return profile


def late_canonical_target(deposit: Fraction, backend: ReportBackend,
                          inclusion: Fraction) -> Node:
    """A late first canonical packet has no receipt at the second-call choice.

    `late0` and `late1` combine deferral and the owner's later binding choice;
    no new information arrives between these decisions in this finite game.
    Inclusion/expiry is sampled only after the raw continuation decision.
    """
    assert ZERO <= inclusion <= ONE

    def pending(v: int, attempted: int) -> Move:
        def response(evidence: str) -> Chance:
            certificate = attempted if evidence == "attempt" else v
            observed = "quiet" if evidence == "quiet" else f"{evidence}{certificate}"
            accepted = bob(f"late_bob:accepted:{observed}", v, attempted, attempted,
                           deposit, backend, evidence != "quiet")
            missed = bob(f"late_bob:miss:{observed}", v, "miss", v,
                         deposit, backend, True, True)
            return Chance(tuple((p, node) for p, node in (
                (inclusion, accepted), (1 - inclusion, missed)) if p))

        return Move(ALICE, f"late_attempt:{v}:{attempted}", tuple(
            (evidence, response(evidence)) for evidence in ("quiet", "attempt", "input")))

    def first(v: int) -> Move:
        return Move(ALICE, f"late_first:{v}", tuple(
            (f"send{bit}", bob("late_protected", v, bit, bit, deposit, backend, False))
            for bit in BITS) + tuple((f"late{bit}", pending(v, bit)) for bit in BITS))

    return Chance(tuple((HALF, first(v)) for v in BITS))


def late_profile(root: Node, deposit: Fraction, backend: ReportBackend,
                 inclusion: Fraction, raw: bool) -> Profile:
    profile = trembles(root)
    signal = raw and inclusion * backend.coverage * deposit <= HALF
    for v in BITS:
        name = f"late_first:{v}"
        profile[name] = pure(f"send{v}", *profile[name])
        for attempted in BITS:
            name = f"late_attempt:{v}:{attempted}"
            # Certificate identity also conveys whether the two private bits agree.
            response = ("attempt" if attempted == v else "input") if signal else "quiet"
            profile[name] = pure(response, *profile[name])
    for name in profile:
        if name.startswith("late_bob:") and not name.endswith("quiet"):
            guess = int(name[-1])
            if name.startswith("late_bob:accepted:input"):
                guess = 1 - guess
            profile[name] = pure(str(guess), "0", "1")
    return profile


def first_late_content_target(deposit: Fraction, backend: ReportBackend) -> Node:
    """A content-dependent late builder, with a protected initial opportunity.

    One concrete timing is deadline=3, delay=0, inclusionBound=1. The owner
    defers at clock 0 and is activated again at clock 2. A certificate-bearing
    packet is included at clock 2; a bare packet expires at clock 3. The latter
    event completes before the clock ever exceeds its send time plus the bound,
    so protected-inclusion receipt obligations do not require its inclusion.
    The builder distinguishes evidence presence, never a private candidate bit.
    """
    def missed(v: int, response: str) -> Move:
        return Move(ALICE, f"content_miss:{v}:{response}", (
            ("quiet", bob("content_miss_bob:quiet", v, "miss", v,
                          deposit, backend, True, True)),
            ("certificate", bob(f"content_miss_bob:cert{v}", v, "miss", v,
                                deposit, backend, True, True))))

    def late(v: int) -> Move:
        bare = tuple((f"bare{bit}", missed(v, f"bare{bit}")) for bit in BITS)
        certified = tuple((f"cert{bit}", bob(f"content_accepted:cert{v}",
            v, bit, bit, deposit, backend, True)) for bit in BITS)
        return Move(ALICE, f"content_late:{v}", bare + certified + (
            ("wait", missed(v, "wait")), ("foreign", missed(v, "foreign"))))

    def first(v: int) -> Move:
        protected = tuple((f"send{bit}", bob("content_protected", v, bit, bit,
            deposit, backend, False)) for bit in BITS)
        return Move(ALICE, f"content_first:{v}", protected + (("defer", late(v)),))

    return Chance(tuple((HALF, first(v)) for v in BITS))


def first_late_content_profile(root: Node, anticipatory: bool) -> Profile:
    profile = trembles(root)
    for v in BITS:
        name = f"content_first:{v}"
        profile[name] = pure(f"send{v}", *profile[name])
        name = f"content_late:{v}"
        profile[name] = pure(f"cert{v}" if anticipatory else f"bare{v}", *profile[name])
    for name in profile:
        if name.startswith("content_miss:"):
            profile[name] = pure("certificate", *profile[name])
        elif name.startswith(("content_miss_bob:cert", "content_accepted:cert")):
            profile[name] = pure(name[-1], "0", "1")
    return profile


def due_unexpired_target(deposit: Fraction, backend: ReportBackend) -> Node:
    """The last owner opportunity is due, but the binding remains ready.

    With deadline=3, delay=0 and bound=1, an initial activation at clock 0
    supplies the protected opportunity. After deferral the builder advances
    to clock 3 and activates Alice before issuing expire. Any due fresh packet
    is rejected (with a receipt), then the binding expires at the same clock.
    Bob can read its authentic certificate before his decision. No further
    Alice turn precedes that decision. Both branches collect only the one D.
    """
    def due(v: int) -> Move:
        return Move(ALICE, f"due_late:{v}", (
            ("quiet", bob("due_miss:quiet", v, "miss", v,
                          deposit, backend, True, True)),
            ("rejected_certificate", bob(f"due_miss:cert{v}", v, "miss", v,
                                         deposit, backend, True, True))))

    def first(v: int) -> Move:
        protected = tuple((f"send{bit}", bob("due_protected", v, bit, bit,
            deposit, backend, False)) for bit in BITS)
        return Move(ALICE, f"due_first:{v}", protected + (("defer", due(v)),))

    return Chance(tuple((HALF, first(v)) for v in BITS))


def due_profile(root: Node, anticipatory: bool) -> Profile:
    profile = trembles(root)
    for v in BITS:
        name = f"due_first:{v}"
        profile[name] = pure(f"send{v}", *profile[name])
        name = f"due_late:{v}"
        profile[name] = pure("rejected_certificate" if anticipatory else "quiet", *profile[name])
    for name in profile:
        if name.startswith("due_miss:cert"):
            profile[name] = pure(name[-1], "0", "1")
    return profile


def collection_mass(root: Node, profile: Profile) -> Fraction:
    return sum(weight for outcome, weight in law(root, profile).items() if outcome[-1])


def report() -> dict[str, object]:
    source_root = source()
    assert_perfect_recall(source_root)
    assert not rationality(source_root, source_profile())
    protected_law = law(source_root, source_profile())
    cases: dict[str, object] = {}
    for observation, delivery, deposit in (
        (HALF, HALF, Fraction(2)), (HALF, ONE, ONE),
        (ONE, ONE, HALF), (HALF, HALF, Fraction(3)),
        (HALF, HALF, ONE), (ONE, ONE, Fraction(1, 4))):
        backend = ReportBackend(observation, delivery)
        root = target(deposit, backend)
        assert_perfect_recall(root)
        raw = target_profile(root, True)
        fixed = target_profile(root, False)
        raw_failures = rationality(root, raw)
        sufficient = deposit >= HALF and backend.coverage * deposit >= HALF
        assert (not raw_failures) == sufficient
        assert law(root, raw) == protected_law
        fixed_failures = rationality(root, fixed)
        for v in BITS:
            assert fixed_failures[f"miss:{v}"]["gain"] == HALF
            first = root.branches[v][1]
            miss = dict(first.children)["miss"]
            assert collection_mass(miss, raw) == ONE
            for attempted in BITS:
                name = f"attempt:{v}:{attempted}"
                assert fixed_failures[name]["gain"] == HALF
                continuation = dict(first.children)[f"attempt{attempted}"]
                for _, response in continuation.children:
                    assert collection_mass(response, raw) == backend.coverage

        clear = protected_retry(deposit, backend, False)
        sunk = protected_retry(deposit, backend, True)
        assert_perfect_recall(clear)
        assert_perfect_recall(sunk)
        clear_fixed = protected_profile(clear, False)
        sunk_fixed = protected_profile(sunk, False)
        sunk_raw = protected_profile(sunk, True)
        clear_failures = rationality(clear, clear_fixed)
        assert (not clear_failures) == (backend.coverage * deposit >= HALF)
        sunk_failures = rationality(sunk, sunk_fixed)
        assert set(sunk_failures) == {f"after_protected:{bit}" for bit in BITS}
        assert all(failure["gain"] == HALF for failure in sunk_failures.values())
        assert not rationality(sunk, sunk_raw)
        for _, continuation in sunk.branches:
            for _, response in continuation.children:
                assert collection_mass(response, sunk_raw) == backend.coverage

        late_cases: dict[str, object] = {}
        for inclusion in (ZERO, Fraction(1, 4), HALF, ONE):
            late = late_canonical_target(deposit, backend, inclusion)
            assert_perfect_recall(late)
            late_raw = late_profile(late, deposit, backend, inclusion, True)
            late_fixed = late_profile(late, deposit, backend, inclusion, False)
            late_raw_failures = rationality(late, late_raw)
            late_fixed_failures = rationality(late, late_fixed)
            incremental = inclusion * backend.coverage * deposit
            gain = HALF - incremental
            threshold = ((1 - inclusion) + inclusion * backend.coverage) * deposit
            assert (not late_raw_failures) == (threshold >= HALF)
            assert law(late, late_raw) == protected_law
            for v, attempted in product(BITS, BITS):
                name = f"late_attempt:{v}:{attempted}"
                assert (name in late_fixed_failures) == (gain > ZERO)
                if gain > ZERO:
                    assert late_fixed_failures[name]["gain"] == gain
            late_cases[str(inclusion)] = {
                "canonical_second_call_gain": str(gain),
                "incremental_expected_charge": str(incremental),
                "raw_completion_is_sequentially_rational": not late_raw_failures,
                "raw_completion_violations": late_raw_failures,
                "protected_initial_law_is_source_law": True,
            }

        content = first_late_content_target(deposit, backend)
        assert_perfect_recall(content)
        anticipatory = first_late_content_profile(content, True)
        after_attempt = first_late_content_profile(content, False)
        content_raw_failures = rationality(content, anticipatory)
        content_fixed_failures = rationality(content, after_attempt)
        content_gain = (1 - backend.coverage) * deposit
        assert (not content_raw_failures) == (backend.coverage * deposit >= HALF)
        assert law(content, anticipatory) == protected_law
        for v in BITS:
            name = f"content_late:{v}"
            assert (name in content_fixed_failures) == (content_gain > ZERO)
            if content_gain > ZERO:
                assert content_fixed_failures[name]["gain"] == content_gain

        due = due_unexpired_target(deposit, backend)
        assert_perfect_recall(due)
        due_raw = due_profile(due, True)
        due_fixed = due_profile(due, False)
        due_raw_failures = rationality(due, due_raw)
        due_fixed_failures = rationality(due, due_fixed)
        assert (not due_raw_failures) == (deposit >= HALF)
        assert law(due, due_raw) == protected_law
        for v in BITS:
            assert due_fixed_failures[f"due_late:{v}"]["gain"] == HALF
            continuation = dict(due.branches[v][1].children)["defer"]
            for _, response in continuation.children:
                assert collection_mass(response, due_raw) == ONE

        cases[f"p={observation} q={delivery} D={deposit}"] = {
            "coverage": str(backend.coverage),
            "raw_completion_is_sequentially_rational": not raw_failures,
            "raw_completion_violations": raw_failures,
            "protected_initial_law_is_source_law": True,
            "fixed_continuation_violations": fixed_failures,
            "clear_escrow_deters_second_fresh_call": not clear_failures,
            "shared_collection_is_identical_before_and_after_retry": True,
            "sunk_escrow_fixed_continuation_gain": str(HALF),
            "sunk_escrow_raw_completion_is_sequentially_rational": True,
            "late_canonical_pending_packet": late_cases,
            "first_late_public_content": {
                "opening_raw_after_attempt_is_too_late": content_gain > ZERO,
                "excluded_first_packet_gain": str(content_gain),
                "anticipatory_raw_completion_is_sequentially_rational":
                    not content_raw_failures,
                "anticipatory_raw_completion_violations": content_raw_failures,
                "protected_initial_law_is_source_law": True,
            },
            "due_but_unexpired_first_binding": {
                "both_actions_collect_the_same_one_deposit": True,
                "excluded_certificate_gain": str(HALF),
                "anticipatory_raw_completion_is_sequentially_rational": not due_raw_failures,
                "anticipatory_raw_completion_violations": due_raw_failures,
                "protected_initial_law_is_source_law": True,
            },
        }
    return cases


if __name__ == "__main__":
    print(json.dumps(report(), indent=2, default=str))
