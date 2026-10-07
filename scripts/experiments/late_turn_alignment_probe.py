#!/usr/bin/env python3
"""Exact finite search for a counterexample to the Target with two late turns.

Question. Without any observation hypothesis (pending openings may leak), with
a builder blind to late packets and strict margins (forfeit D >= 3R, expected
charge c = p d > R of a dropped late opening), is there a game in which EVERY
native sequential equilibrium changes the intended joint law?

Mechanism under test (plan section 13). A leaked late opening tells a listener
the opened value, so after a dropped late opening the listener answers with
knowledge it lacks after a silent failure. This makes two types of the sender
prefer opposite late sending turns, and then, for every tilt of the deferral
trembles, the belief after an inclusion at one of the turns is a point mass on
that turn's natural sender (Lemma 13.1). If the listener's best reply at that
point mass rewards the sender, deliberate lateness pays when q is near 1.

Common native model (one admissible configuration per design). B's type is
(v, s) in {0,1}^2, independent, P(v = 1) = P(s = 1) = 9/20. B commits v (guard
b = v) and reveals it. The reveal has a protected turn P (always included in
time) and two late turns L1, L2; a late opening is included before expiry with
probability q by a content-blind coin; A is activated between L1 and L2
whatever is pending and then learns every pending message (author-only rule);
every other builder command ignores late packets (`BlindToLatePackets`). A then
answers once, at one of: SP(v) success via P (on path); S1(v), S2(v) success
via L1, L2; F1(v) failure after an L1 send (A learned v); F0 failure with
nothing learned. Payoffs are tables per design: A and B after success and after
failure; B additionally pays D on a failed reveal and c on a dropped late
opening. The intended game is the same without timing: B opens, A answers at
SP(v); its law is the target.

Consistency: beliefs are exact limits of Bayes posteriors under fully mixed B
behaviour given as polynomials in eps, with type- and turn-dependent tremble
orders and coefficients. A moves once, so A's own trembles do not matter.

Designs (each with an explicit preserving native SE, checked exactly):
- D1: A's success actions {0, m, 1}, m the intended answer (best only at
  interior beliefs), failure answer [a = v]; B gets [a = s].
- D2: A's non-intended success answers x0, x1 reward every sender type equally.
- D3: x0 rewards s = 0 and punishes s = 1; x1 the reverse.
In each, with the intended answer m played at every success set, the two v = 1
types prefer opposite late turns, and every tilt in a grid gives a point-mass
belief at S1(1) or S2(1) where m is not a best reply (negative control,
Lemma 13.1). The preserving SE escapes by a small mixture at S1(1): A mixes m
with a reward of probability of order (1 - q), which makes the minority type
indifferent between L1 and L2, so both types send naturally at L1 and the
belief at S1(1) is free (set by the tilt) to the point where A is indifferent.
The reward stays within the deterrence slack (1 - q)(D - R + c) because the
leak-driven preference gap is at most (1 - q) R. Margin control: with
D + c < 2 (margins violated) the same escape fails deterrence.

Run: python scripts/experiments/late_turn_alignment_probe.py
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product

TYPES = tuple(product((0, 1), (0, 1)))  # (v, s)
PRIOR_ONE = F(9, 20)


def prior(t: tuple[int, int]) -> F:
    v, s = t
    return (PRIOR_ONE if v else 1 - PRIOR_ONE) * (PRIOR_ONE if s else 1 - PRIOR_ONE)


# ---------------------------------------------------------------- polynomials


def poly(*terms):
    out: dict[int, F] = {}
    for coef, exp in terms:
        out[exp] = out.get(exp, F(0)) + F(coef)
    return {e: c for e, c in out.items() if c != 0}


def padd(p, q):
    return poly(*[(c, e) for e, c in p.items()], *[(c, e) for e, c in q.items()])


def pmul(p, q):
    return poly(*[(cp * cq, ep + eq) for ep, cp in p.items() for eq, cq in q.items()])


def pconst(c):
    return poly((c, 0))


def leading(p):
    assert p, "a fully mixed mass is never identically zero"
    e = min(p)
    assert p[e] > 0
    return e, p[e]


def limit_belief(masses: dict) -> dict:
    leads = {k: leading(m) for k, m in masses.items()}
    e = min(x for x, _ in leads.values())
    weights = {k: (c if x == e else F(0)) for k, (x, c) in leads.items()}
    total = sum(weights.values())
    return {k: w / total for k, w in weights.items()}


def choice(chosen: bool, coef: F, exp: int):
    assert exp > 0 and coef > 0
    small = poly((coef, exp))
    big = poly((1, 0), (-coef, exp))
    return (big, small) if chosen else (small, big)


# --------------------------------------------------------------------- games


@dataclass(frozen=True)
class Game:
    name: str
    success: tuple[str, ...]
    failure: tuple[str, ...]
    a_success: dict  # action -> type -> payoff
    b_success: dict
    a_failure: dict
    b_failure: dict
    intended: str  # A's intended answer after success, for both v
    b_range: F

    def a_best(self, actions, table, belief) -> set[str]:
        value = {a: sum(w * table[a][t] for t, w in belief.items()) for a in actions}
        top = max(value.values())
        return {a for a, x in value.items() if x == top}


@dataclass(frozen=True)
class Behaviour:
    """Limit play of one type after waiting at P, with tremble orders."""
    wait: tuple[F, int]
    l1: bool
    off1: tuple[F, int]
    l2: bool
    off2: tuple[F, int]


@dataclass(frozen=True)
class Answers:
    """A's mixed answers: dicts action -> probability."""
    s1: dict
    s2: dict
    f1: dict
    f0: dict


@dataclass(frozen=True)
class Config:
    q: F
    d: F
    c: F


def masses(behaviour: dict, cfg: Config) -> dict:
    out: dict = {"S1": {}, "S2": {}, "F1": {}, "F0": {}}
    for t in TYPES:
        b = behaviour[t]
        wait = poly(b.wait)
        send1, hold1 = choice(b.l1, *b.off1)
        send2, hold2 = choice(b.l2, *b.off2)
        base = pmul(pconst(prior(t)), wait)
        at1 = pmul(base, send1)
        at2 = pmul(pmul(base, hold1), send2)
        never = pmul(pmul(base, hold1), hold2)
        out["S1"][t] = pmul(at1, pconst(cfg.q))
        out["S2"][t] = pmul(at2, pconst(cfg.q))
        out["F1"][t] = pmul(at1, pconst(1 - cfg.q))
        out["F0"][t] = padd(pmul(at2, pconst(1 - cfg.q)), never)
    return out


def beliefs(behaviour: dict, cfg: Config) -> dict:
    m = masses(behaviour, cfg)
    out = {}
    for v in (0, 1):
        for key in ("S1", "S2", "F1"):
            out[(key, v)] = limit_belief({t: m[key][t] for t in TYPES if t[0] == v})
    out["F0"] = limit_belief(m["F0"])
    return out


def expect(mix: dict, table: dict, t) -> F:
    return sum(p * table[a][t] for a, p in mix.items())


def b_plans(game: Game, cfg: Config, answers: dict, t) -> dict:
    v = t[0]
    sp = expect({game.intended: F(1)}, game.b_success, t)
    s1 = expect(answers[v].s1, game.b_success, t)
    s2 = expect(answers[v].s2, game.b_success, t)
    f1 = expect(answers[v].f1, game.b_failure, t)
    f0 = expect(answers[v].f0, game.b_failure, t)
    q, d, c = cfg.q, cfg.d, cfg.c
    return {"P": sp,
            "L1": q * s1 + (1 - q) * (f1 - d - c),
            "L2": q * s2 + (1 - q) * (f0 - d - c),
            "never": f0 - d}


def check(game: Game, cfg: Config, behaviour: dict, answers: dict) -> dict:
    """Exact check of a preserving native SE: consistency (beliefs are the
    limits of the given family), A's rationality at every set, B's rationality
    at P, L1, L2 for every type, and the intended law on path."""
    assert all(sum(mix.values()) == 1 and min(mix.values()) >= 0
               for ans in answers.values() for mix in (ans.s1, ans.s2, ans.f1, ans.f0))
    assert answers[0].f0 == answers[1].f0, "F0 is one information set"
    bel = beliefs(behaviour, cfg)
    # A at the on-path set: the intended answer is the unique best reply.
    for v in (0, 1):
        mu = {t: prior(t) for t in TYPES if t[0] == v}
        tot = sum(mu.values())
        mu = {t: w / tot for t, w in mu.items()}
        assert game.a_best(game.success, game.a_success, mu) == {game.intended}, (game.name, v)
    # A off path.
    for v in (0, 1):
        for key, table, actions in (("S1", game.a_success, game.success),
                                    ("S2", game.a_success, game.success),
                                    ("F1", game.a_failure, game.failure)):
            mix = getattr(answers[v], key.lower())
            best = game.a_best(actions, table, bel[(key, v)])
            assert all(p == 0 or a in best for a, p in mix.items()), (game.name, key, v, bel[(key, v)])
    best0 = game.a_best(game.failure, game.a_failure, bel["F0"])
    assert all(p == 0 or a in best0 for a, p in answers[0].f0.items()), (game.name, "F0", bel["F0"])
    # B.
    for t in TYPES:
        b = behaviour[t]
        val = b_plans(game, cfg, answers, t)
        assert (val["L2"] >= val["never"]) if b.l2 else (val["never"] >= val["L2"]), (game.name, t, val)
        cont2 = val["L2"] if b.l2 else val["never"]
        assert (val["L1"] >= cont2) if b.l1 else (cont2 >= val["L1"]), (game.name, t, val)
        cont1 = val["L1"] if b.l1 else cont2
        assert val["P"] >= cont1, (game.name, t, val)
    return bel


def rejected(*args) -> bool:
    try:
        check(*args)
    except AssertionError:
        return True
    return False


# ------------------------------------------------------------------- designs


def indicator(actions, rule):
    return {a: {t: F(rule(a, t)) for t in TYPES} for a in actions}


def failure_tables():
    a_fail = indicator(("0", "1"), lambda a, t: int(a) == t[0])
    b_fail = indicator(("0", "1"), lambda a, t: int(a) == t[1])
    return a_fail, b_fail


def game_d1() -> Game:
    succ = ("0", "m", "1")
    a_s = {a: {t: (F(3, 5) if a == "m" else F(int(a) == t[1])) for t in TYPES} for a in succ}
    b_s = {a: {t: (F(0) if a == "m" else F(int(a) == t[1])) for t in TYPES} for a in succ}
    a_f, b_f = failure_tables()
    return Game("D1", succ, ("0", "1"), a_s, b_s, a_f, b_f, "m", F(1))


def game_d2() -> Game:
    succ = ("x0", "m", "x1")
    a_s = {"m": {t: F(3, 5) for t in TYPES},
           "x0": {t: F(t[1] == 0) for t in TYPES},
           "x1": {t: F(t[1] == 1) for t in TYPES}}
    b_s = {"m": {t: F(0) for t in TYPES}, "x0": {t: F(1) for t in TYPES},
           "x1": {t: F(1) for t in TYPES}}
    a_f, b_f = failure_tables()
    return Game("D2", succ, ("0", "1"), a_s, b_s, a_f, b_f, "m", F(1))


def game_d3() -> Game:
    succ = ("x0", "m", "x1")
    a_s = {"m": {t: F(3, 5) for t in TYPES},
           "x0": {t: F(t[1] == 0) for t in TYPES},
           "x1": {t: F(t[1] == 1) for t in TYPES}}
    b_s = {"m": {t: F(0) for t in TYPES},
           "x0": {t: F(1) if t[1] == 0 else F(-1) for t in TYPES},
           "x1": {t: F(1) if t[1] == 1 else F(-1) for t in TYPES}}
    a_f, b_f = failure_tables()
    return Game("D3", succ, ("0", "1"), a_s, b_s, a_f, b_f, "m", F(2))


def pure(a):
    return {a: F(1)}


def two(a, pa, b):
    return {a: pa, b: 1 - pa}


def escape(game: Game, cfg: Config, reward: str, s_needed: int) -> tuple[dict, dict]:
    """The preserving assessment: A answers 0 at F0 (belief v = 0), a = v at F1;
    at S1(1) A mixes the intended answer with `reward` of probability p making
    type (1,0) indifferent between L1 and L2; both v = 1 types send at L1; the
    tilt w(1,1)/w(1,0) puts A at S1(1) exactly at indifference between the
    intended answer and `reward` (P(s = s_needed) = 3/5); S2 is reached only by
    floors whose coefficients give P(s = 1) = 1/2; the v = 0 types are
    indifferent and send at L1."""
    q = cfg.q
    gap = game.b_success[reward][(1, 0)] - game.b_success[game.intended][(1, 0)]
    p = (1 - q) / (q * gap)  # (1,0): q p gap - (1 - q) = 0
    target = {s_needed: F(3, 5), 1 - s_needed: F(2, 5)}
    # masses at S1(1) are prior * w; choose w(1,1)/w(1,0) for P(s = 1) = target[1]
    ratio = (target[1] / target[0]) * (prior((1, 0)) / prior((1, 1)))
    one = (F(1), 1)
    hold_ratio = (prior((1, 0)) / prior((1, 1))) / ratio  # P(s = 1) = 1/2 at S2(1)
    behaviour = {
        (1, 1): Behaviour((ratio, 2), True, (hold_ratio, 1), True, one),
        (1, 0): Behaviour((F(1), 2), True, (F(1), 1), True, one),
        (0, 1): Behaviour((F(1), 1), True, one, True, one),
        (0, 0): Behaviour((F(1), 1), True, one, True, one),
    }
    answers = {
        1: Answers(two(reward, p, game.intended), pure(game.intended), pure("1"), pure("0")),
        0: Answers(pure(game.intended), pure(game.intended), pure("0"), pure("0")),
    }
    return behaviour, answers


def pure_intended_rejected_for_all_tilts(game: Game, cfg: Config) -> int:
    """Negative control (Lemma 13.1): with the intended answer at every success
    set, A answering 0 at F0 and a = v at F1, the v = 1 types prefer opposite
    late turns; for every tilt and floor in the grid the assessment fails."""
    answers = {
        1: Answers(pure(game.intended), pure(game.intended), pure("1"), pure("0")),
        0: Answers(pure(game.intended), pure(game.intended), pure("0"), pure("0")),
    }
    v11 = b_plans(game, cfg, answers, (1, 1))
    v10 = b_plans(game, cfg, answers, (1, 0))
    assert v11["L1"] > v11["L2"] and v10["L2"] > v10["L1"], "opposite strict preferences"
    count = 0
    for k11, k10, j11, j10, m11, m10 in product(range(1, 5), range(1, 5), range(1, 4),
                                                 range(1, 4), range(1, 4), range(1, 4)):
        for c11, c10 in ((F(1), F(1)), (F(7), F(1, 5)), (F(1, 9), F(3))):
            behaviour = {
                (1, 1): Behaviour((c11, k11), True, (c10, j11), True, (F(1), m11)),
                (1, 0): Behaviour((c10, k10), False, (c11, j10), True, (F(1), m10)),
                (0, 1): Behaviour((F(1), 1), True, (F(1), 1), True, (F(1), 1)),
                (0, 0): Behaviour((F(1), 1), True, (F(1), 1), True, (F(1), 1)),
            }
            assert rejected(game, cfg, behaviour, answers)
            bel = beliefs(behaviour, cfg)
            pure1 = max(bel[("S1", 1)].values()) == 1
            pure2 = max(bel[("S2", 1)].values()) == 1
            assert pure1 or pure2, "Lemma 13.1"
            count += 1
    return count


def main() -> None:
    for game, reward, s_needed in ((game_d1(), "0", 0), (game_d2(), "x0", 0),
                                   (game_d3(), "x0", 0)):
        r = game.b_range
        configs = (Config(F(9, 10), 3 * r, 2 * r), Config(F(99, 100), 3 * r, 2 * r),
                   Config(F(999, 1000), 4 * r, r + F(1, 2)))
        for cfg in configs:
            assert cfg.d >= 3 * r and cfg.c > r, "approved margins: D >= 3R, c = p d > R"
            behaviour, answers = escape(game, cfg, reward, s_needed)
            bel = check(game, cfg, behaviour, answers)
            grid = pure_intended_rejected_for_all_tilts(game, cfg)
            print(f"{game.name} (R={r}) q={cfg.q} D={cfg.d} c={cfg.c}: preserving SE, A mixes "
                  f"{reward} w.p. {answers[1].s1[reward]} at S1(1), belief there "
                  f"{bel[('S1', 1)]}; pure intended answers rejected on {grid} tilts")
    # Margin control: D + c < 2 (forfeit and deposit below the margins).
    weak = Config(F(99, 100), F(1, 2), F(1))
    for game, reward in ((game_d1(), "0"), (game_d2(), "x0")):
        behaviour, answers = escape(game, weak, reward, 0)
        assert rejected(game, weak, behaviour, answers)
    print("margin control: with D + c < 2 the escape fails deterrence")
    print("verdict: no counterexample in D1-D3; each admits a preserving native SE "
          "through a small reward mixture that removes the opposite late preferences")


if __name__ == "__main__":
    main()
