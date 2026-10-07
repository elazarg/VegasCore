#!/usr/bin/env python3
"""Exact finite probe: two late reveal turns with a leak between them.

Question. With the charged settled-record verdict and a builder blind to late
packets, a pending late opening leaked to a listener makes the sender's types
prefer different late sending turns. Does every native sequential equilibrium
then change the intended joint law (a counterexample to the Target), or does
some native sequential equilibrium preserve it?

Intended game I. Chance draws B's private type (v, s) in {0,1}^2, independent,
P(v = 1) = P(s = 1) = 9/20. B commits b with guard b = v (its only intended
commit), then opens it (the only intended reveal move); v becomes public. A
then picks a in {0,1} knowing v but not s. A gets [a = s]; B gets [a = s].
Every assessment in which A plays a = 0 after every v is a sequential
equilibrium (A's belief about s is the prior, 9/20 < 1/2, so a = 0 is A's
unique best reply). Intended joint law: v from its prior, the reveal succeeds,
a = 0.

Native game N (one admissible configuration). B's reveal event has one
protected turn P and two late turns L1, L2 before expiry. The builder:
- includes a packet sent at P before the protected window closes (always);
- includes a late opening, whenever it is sent, before expiry with probability
  q, by a coin independent of everything else (content-blind);
- activates A once between L1 and L2 whatever is pending, and issues every
  other command independently of late packets.
So `ProtectedInclusion` holds; `Opportunity` and `CompletesPlay` hold with the
fixed activation calendar; deadlines leave room for one reaction and one
inclusion (`AsyncTimely`); and the scheduler is blind to late packets (its only
late-packet-dependent command is the inclusion of that packet). Observation
rule: the activated player learns every pending message (it depends only on
authors and identifiers), so a late opening sent at L1 and still pending at A's
activation reveals v to A.
Payoffs: A gets [a = s] after a successful reveal and [a = v] after a failed
one. B gets [a = s], minus the forfeit D on a failed reveal, minus the expected
charge c of a dropped late opening (forbidden at settlement, collected with
the coverage probability; c is p * d). B's base utility has range R = 1; the
probe takes c = 2 > R (strict deterrence margin) and (q, D) in
(9/10, 4), (99/100, 4), (9/10, 3/2), (999/1000, 3/2): q near 1, D above R, both
below and above 3R.

A's information sets (A moves once, after the reveal event ends):
SP(v) success via P; S1(v) success via L1 (A saw the pending opening);
S2(v) success via L2 (A saw nothing pending); F1(v) failure after an L1 send
(A learned v from the leak); F0 failure with nothing learned (L2 send dropped,
or never sent).

Consistency. Beliefs are exact limits, as eps -> 0, of Bayes posteriors under
fully mixed B behaviour whose probabilities are polynomials in eps; trembles
may depend on the type and the turn arbitrarily. A's own trembles do not
affect A's beliefs (A moves once).

Results (every claim is an assertion).
1. Leak variant: a preserving native SE exists. A plays a = 0 at every success
   set and at F0, a = v at F1; every type sends at P; off path (1,1) sends at
   L1, (1,0) at L2, (0, *) as chosen below. The beliefs at S1(1) keep
   P(s = 1) <= 1/2 because type (1,1) waits at P with a tremble of higher order
   than type (1,0). So the instance is not a counterexample to the Target.
2. Negative control: with type-independent waiting trembles (the component
   construction's omega floors), the same profile is rejected: the belief at
   S1(1) is s = 1, so a = 0 is not a best reply; and if A answers a = 1 there,
   type (1,1) strictly gains by waiting at P.
3. Private-opening control (pending openings never leak, F1 merges into F0):
   a preserving native SE exists even with type-independent trembles.

Run: python scripts/experiments/late_turn_leak_probe.py
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product

TYPES = tuple(product((0, 1), (0, 1)))  # (v, s)
PRIOR_ONE = F(9, 20)
Q = F(9, 10)
D = F(4)
C = F(2)
RANGE = F(1)


def prior(t: tuple[int, int]) -> F:
    v, s = t
    pv = PRIOR_ONE if v == 1 else 1 - PRIOR_ONE
    ps = PRIOR_ONE if s == 1 else 1 - PRIOR_ONE
    return pv * ps


# ---------------------------------------------------------------- polynomials
# A mass is a polynomial in a small parameter eps: a dict exponent -> coefficient.


def poly(*terms: tuple[F | int, int]) -> dict[int, F]:
    out: dict[int, F] = {}
    for coef, exp in terms:
        out[exp] = out.get(exp, F(0)) + F(coef)
    return {e: c for e, c in out.items() if c != 0}


def padd(p: dict[int, F], q: dict[int, F]) -> dict[int, F]:
    return poly(*[(c, e) for e, c in p.items()], *[(c, e) for e, c in q.items()])


def pmul(p: dict[int, F], q: dict[int, F]) -> dict[int, F]:
    return poly(*[(cp * cq, ep + eq) for ep, cp in p.items() for eq, cq in q.items()])


def pconst(c: F) -> dict[int, F]:
    return poly((c, 0))


def leading(p: dict[int, F]) -> tuple[int, F]:
    assert p, "a fully mixed mass is never identically zero"
    e = min(p)
    assert p[e] > 0, "a mass is positive for small eps"
    return e, p[e]


def limit_belief(masses: dict) -> dict:
    """Exact limit of the normalized masses as eps -> 0."""
    leads = {k: leading(m) for k, m in masses.items()}
    e = min(x for x, _ in leads.values())
    weights = {k: (c if x == e else F(0)) for k, (x, c) in leads.items()}
    total = sum(weights.values())
    return {k: w / total for k, w in weights.items()}


def choice(chosen: bool, coef: F, exp: int) -> tuple[dict[int, F], dict[int, F]]:
    """(P(action), P(other)) for a fully mixed binary choice whose limit is the
    action if `chosen`, else the other; the unchosen one has mass coef eps^exp."""
    assert exp > 0 and coef > 0
    small = poly((coef, exp))
    big = poly((1, 0), (-coef, exp))
    return (big, small) if chosen else (small, big)


# ------------------------------------------------------------------- profiles


@dataclass(frozen=True)
class TypeBehaviour:
    """Limit play of one type after waiting at P, with tremble orders.
    wait = wait_coef eps^wait_exp; at L1 the limit is `l1` (send or not), the
    other choice trembles with off1; at L2 likewise."""
    wait_coef: F
    wait_exp: int
    l1: bool
    off1: tuple[F, int]
    l2: bool
    off2: tuple[F, int]


@dataclass(frozen=True)
class Answer:
    """A's probabilities of a = 1 at each information set."""
    s1: dict[int, F]
    s2: dict[int, F]
    f0: F
    leak: bool  # whether F1 is separate (A learned v) or merged into F0


def masses(behaviour: dict, leak: bool) -> dict[str, dict]:
    """Masses of every (type, A-information-set) pair."""
    out: dict[str, dict] = {"S1": {}, "S2": {}, "F0": {}, "F1": {}}
    for t in TYPES:
        b = behaviour[t]
        wait = poly((b.wait_coef, b.wait_exp))
        send1, hold1 = choice(b.l1, *b.off1)
        send2, hold2 = choice(b.l2, *b.off2)
        base = pmul(pconst(prior(t)), wait)
        at1 = pmul(base, send1)
        at2 = pmul(pmul(base, hold1), send2)
        never = pmul(pmul(base, hold1), hold2)
        out["S1"][t] = pmul(at1, pconst(Q))
        out["S2"][t] = pmul(at2, pconst(Q))
        dropped1 = pmul(at1, pconst(1 - Q))
        dropped2 = pmul(at2, pconst(1 - Q))
        failed = padd(dropped2, never)
        if leak:
            out["F1"][t] = dropped1
            out["F0"][t] = failed
        else:
            out["F0"][t] = padd(failed, dropped1)
    return out


def beliefs(behaviour: dict, leak: bool) -> dict:
    m = masses(behaviour, leak)
    out = {}
    for v in (0, 1):
        for key in ("S1", "S2"):
            out[(key, v)] = limit_belief({t: m[key][t] for t in TYPES if t[0] == v})
    out["F0"] = limit_belief(m["F0"])
    return out


def a_best(values: dict[int, F]) -> set[int]:
    best = max(values.values())
    return {a for a, x in values.items() if x == best}


def check_answer_rational(answer: Answer, belief: dict) -> None:
    """A's sequential rationality at S1(v), S2(v), F0 (at SP(v) a = 0 is the
    unique best reply to the prior; at F1(v) a = v is dominant)."""
    for v in (0, 1):
        for key, alpha in (("S1", answer.s1[v]), ("S2", answer.s2[v])):
            mu = belief[(key, v)]
            p1 = sum(w for t, w in mu.items() if t[1] == 1)
            brs = a_best({0: 1 - p1, 1: p1})
            assert (alpha == 0 or 1 in brs) and (alpha == 1 or 0 in brs), (key, v, mu, alpha)
    mu = belief["F0"]
    p1 = sum(w for t, w in mu.items() if t[0] == 1)
    brs = a_best({0: 1 - p1, 1: p1})
    assert (answer.f0 == 0 or 1 in brs) and (answer.f0 == 1 or 0 in brs), ("F0", mu, answer.f0)


def b_values(t: tuple[int, int], answer: Answer) -> dict[str, F]:
    """B's expected payoff of each whole plan from P on."""
    v, s = t

    def match(prob_one: F) -> F:
        return prob_one if s == 1 else 1 - prob_one

    fail_answer1 = F(v) if answer.leak else answer.f0
    send_p = match(F(0))
    send_l1 = Q * match(answer.s1[v]) + (1 - Q) * (match(fail_answer1) - D - C)
    send_l2 = Q * match(answer.s2[v]) + (1 - Q) * (match(answer.f0) - D - C)
    never = match(answer.f0) - D
    return {"P": send_p, "L1": send_l1, "L2": send_l2, "never": never}


def check_b_rational(behaviour: dict, answer: Answer) -> None:
    """B's sequential rationality at P, L1 and L2 for every type."""
    for t in TYPES:
        b = behaviour[t]
        val = b_values(t, answer)
        at2 = max(val["L2"], val["never"])
        assert val["L2"] >= val["never"] if b.l2 else val["never"] >= val["L2"], (t, val)
        cont2 = val["L2"] if b.l2 else val["never"]
        assert val["L1"] >= cont2 if b.l1 else cont2 >= val["L1"], (t, val)
        assert cont2 == at2
        cont1 = val["L1"] if b.l1 else cont2
        assert val["P"] >= cont1, (t, val)


def joint_law(answer_sp: dict[int, F]) -> dict:
    """On-path native law when every type sends at P: (v, success, a)."""
    law: dict = {}
    for t in TYPES:
        v, _ = t
        for a in (0, 1):
            p = prior(t) * (answer_sp[v] if a == 1 else 1 - answer_sp[v])
            if p:
                law[(v, "success", a)] = law.get((v, "success", a), F(0)) + p
    return law


def intended_law() -> dict:
    law: dict = {}
    for t in TYPES:
        law[(t[0], "success", 0)] = law.get((t[0], "success", 0), F(0)) + prior(t)
    return law


def check_intended_se() -> None:
    p1 = sum(prior(t) for t in TYPES if t[1] == 1)
    assert p1 == PRIOR_ONE < F(1, 2)
    for v in (0, 1):
        mu = {t: prior(t) / sum(prior(u) for u in TYPES if u[0] == v) for t in TYPES if t[0] == v}
        q1 = sum(w for t, w in mu.items() if t[1] == 1)
        assert a_best({0: 1 - q1, 1: q1}) == {0}


def check_preserving(behaviour: dict, answer: Answer) -> dict:
    belief = beliefs(behaviour, answer.leak)
    check_answer_rational(answer, belief)
    check_b_rational(behaviour, answer)
    assert joint_law({0: F(0), 1: F(0)}) == intended_law()
    return belief


def rejected(behaviour: dict, answer: Answer) -> bool:
    try:
        check_preserving(behaviour, answer)
    except AssertionError:
        return True
    return False


# ---------------------------------------------------------------------- main


def run() -> None:
    assert D > RANGE and C > RANGE and 0 < Q < 1
    assert Q * D > (1 - Q) * C  # sending at L2 beats never sending
    check_intended_se()

    zero = {0: F(0), 1: F(0)}
    answer = Answer(s1=zero, s2=zero, f0=F(0), leak=True)

    # The sender's strict off-path preferences under this answer.
    vals = {t: b_values(t, answer) for t in TYPES}
    assert vals[(1, 1)]["L1"] > vals[(1, 1)]["L2"] > vals[(1, 1)]["never"]
    assert vals[(1, 0)]["L2"] > vals[(1, 0)]["L1"] and vals[(1, 0)]["L2"] > vals[(1, 0)]["never"]
    assert vals[(0, 0)]["L1"] == vals[(0, 0)]["L2"] and vals[(0, 1)]["L1"] == vals[(0, 1)]["L2"]
    for t in TYPES:
        assert vals[t]["P"] > max(vals[t]["L1"], vals[t]["L2"], vals[t]["never"])

    # 1. Leak variant: a preserving native SE with type-tilted trembles.
    one = (F(1), 1)
    tilted = {
        (1, 1): TypeBehaviour(F(1), 3, True, one, True, one),    # waits rarely, sends at L1
        (1, 0): TypeBehaviour(F(1), 1, False, one, True, one),   # sends at L2
        (0, 0): TypeBehaviour(F(1), 1, False, one, True, one),   # indifferent; sends at L2
        (0, 1): TypeBehaviour(F(1), 2, True, one, True, one),    # indifferent; sends at L1
    }
    belief = check_preserving(tilted, answer)
    assert belief[("S1", 1)] == {(1, 0): F(1), (1, 1): F(0)}
    assert belief["F0"][(1, 0)] + belief["F0"][(1, 1)] <= F(1, 2)
    print("leak variant: preserving native SE exists (type-tilted waiting trembles); "
          f"belief at S1(1) = {belief[('S1', 1)]}, at F0 v=1 weight "
          f"{belief['F0'][(1, 0)] + belief['F0'][(1, 1)]}")

    # 2. Negative controls: type-independent waiting trembles.
    uniform = {t: TypeBehaviour(F(1), 1, b.l1, one, b.l2, one) for t, b in tilted.items()}
    uniform_belief = beliefs(uniform, True)
    assert uniform_belief[("S1", 1)] == {(1, 0): F(0), (1, 1): F(1)}
    assert rejected(uniform, answer)
    # If A answers a = 1 at S1(1), type (1,1) strictly gains by waiting at P.
    answer_one = Answer(s1={0: F(0), 1: F(1)}, s2=zero, f0=F(0), leak=True)
    deviation = b_values((1, 1), answer_one)
    assert deviation["L1"] > deviation["P"]
    assert rejected(uniform, answer_one)
    # A tilted profile with the wrong tilt is rejected too.
    wrong = dict(tilted)
    wrong[(1, 1)] = TypeBehaviour(F(1), 1, True, one, True, one)
    wrong[(1, 0)] = TypeBehaviour(F(1), 3, False, one, True, one)
    assert rejected(wrong, answer)
    # Irrational off-path play is rejected: (1,1) sending at L2.
    bad = dict(tilted)
    bad[(1, 1)] = TypeBehaviour(F(1), 3, False, one, True, one)
    assert rejected(bad, answer)
    print("negative controls: uniform waiting trembles give S1(1) belief s=1 and are "
          f"rejected; answering a=1 there lets (1,1) gain {deviation['L1'] - deviation['P']} "
          "by waiting; wrong tilt and irrational late play rejected")

    # 3. Private-opening control: no leak, F1 merges into F0. Every type is
    # indifferent between L1 and L2 under the zero answer, so all send at L1
    # and type-independent trembles already preserve the law.
    private = Answer(s1=zero, s2=zero, f0=F(0), leak=False)
    pvals = {t: b_values(t, private) for t in TYPES}
    for t in TYPES:
        assert pvals[t]["L1"] == pvals[t]["L2"]
    flat = {t: TypeBehaviour(F(1), 1, True, one, True, one) for t in TYPES}
    pbelief = check_preserving(flat, private)
    assert pbelief[("S1", 1)] == {(1, 0): 1 - PRIOR_ONE, (1, 1): PRIOR_ONE}
    print("private-opening control: preserving native SE with type-independent trembles")



def main() -> None:
    global Q, D
    for q, d in ((F(9, 10), F(4)), (F(99, 100), F(4)), (F(9, 10), F(3, 2)),
                 (F(999, 1000), F(3, 2))):
        Q, D = q, d
        print(f"-- q = {q}, D = {d}, c = {C}, range = {RANGE}")
        run()
    print("verdict: not a counterexample to the Target (a preserving native SE exists); "
          "it refutes only constructions whose waiting trembles are type-independent")


if __name__ == "__main__":
    main()
