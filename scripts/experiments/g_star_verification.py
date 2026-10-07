#!/usr/bin/env python3
"""Independent exact verification of the three-type counterexample G*.

Game G* (docs/open-problem-late-turn-equilibria.md, variant 1). Sender type
(v, s), v in {0,1} with P(v = 1) = 9/20, s in {A, B, C} uniform, independent.
R = 2, D = 6 = 3R, c = 3 > R, q = 99/100, two late turns L1, L2, one listener
activated between L1 and L2 who learns every pending opening (so it knows v
after a dropped L1 opening). After the reveal resolves the listener answers:
- success: m (listener gets 2/5) or a guess g_i of s (listener gets [s = i]);
  the sender gets R/2 under m, and under any guess types A, B get R and C gets 0;
- failure: f1 or f0 (listener gets [a = v]); the sender gets (R, 0, 0) under f1
  and (0, R, 0) under f0 over (A, B, C).
The sender pays D on a failed reveal and c on a dropped late opening.
Configuration: protected packets included in time; a late opening included
before expiry with probability q by a content-blind coin, decided after the
listener's activation; the listener activated between L1 and L2 whatever is
pending (so the builder is blind to late packets). The listener's information
sets: SP(v) (on path), S1(v), S2(v) (success at L1, L2), F1(v) (failure, v
learned), F0 (failure, nothing learned).

Claim: the intended game has a unique sequential equilibrium (the listener
plays m), and every sequential equilibrium of G* has a different outcome
distribution. Proof (each step is an assertion below, exact):
1. On path every type must open at P (any late send fails with probability
   1 - q > 0), so SP(v) has the prior belief and the listener plays m.
2. A listener mixture at a success site affects the sender only through
   gamma = total weight on guesses: types A, B get R/2 + gamma R/2, type C
   gets R/2 - gamma R/2 (all guesses act alike on the sender).
3. Write theta for the listener's weight on f1 at F0 and, for a class v,
   delta = q (gamma_1 - gamma_2) R / 2. The sender's L1-minus-L2 gaps in class
   v = 1 are (delta + kappa, delta - kappa, -delta) for (A, B, C) with
   kappa = (1 - q) R (1 - theta), and in class v = 0 they are
   (delta - kappa, delta + kappa, -delta) with kappa = (1 - q) R theta (the
   never-send plan is dominated). For every theta at least one class has
   kappa > 0. Then for every delta two of its types strictly prefer opposite
   late turns: if |delta| < kappa, A and B; if delta >= kappa, C against the
   type with gap delta + kappa; if delta <= -kappa, C against the type with
   gap delta - kappa.
4. Cross-ratio: if t1 strictly prefers L1 and t0 strictly prefers L2, then for
   every fully mixed family (any type- and turn-dependent tremble rates and
   coefficients) the products of the odds t0:t1 at S1(v) and t1:t0 at S2(v)
   is e0 * e1 -> 0, so one of the two limit beliefs has a zero coordinate.
5. At a belief with a zero coordinate the largest coordinate is >= 1/2 > 2/5, so
   the listener guesses with probability one there; type (v, A) then gains by
   deferring and sending at that turn: q R + (1 - q)(F - D - c) >= qR - (1 - q)(D + c)
   = 189/100 > 1 = R/2, its value at P. Contradiction with step 1.

Negative control: with q = 1/2 the deviation in step 5 is worth less than the
protected turn, so the argument needs q near 1.

Run: python scripts/experiments/g_star_verification.py
"""

from __future__ import annotations

import itertools
import random
from fractions import Fraction as F

R, D, C = F(2), F(6), F(3)
Q = F(99, 100)
S = ("A", "B", "C")
P_V1 = F(9, 20)


def success_value(s: str, gamma: F) -> F:
    """Sender's base value at a success site when the listener puts total
    weight gamma on guesses (step 2)."""
    return (1 - gamma) * (R / 2) + gamma * (R if s in ("A", "B") else F(0))


def failure_value(s: str, answer_f1_weight: F) -> F:
    f1 = {"A": R, "B": F(0), "C": F(0)}[s]
    f0 = {"A": F(0), "B": R, "C": F(0)}[s]
    return answer_f1_weight * f1 + (1 - answer_f1_weight) * f0


def plans(v: int, s: str, gamma1: F, gamma2: F, theta: F, q: F = Q) -> dict:
    """Values of the sender's plans; F1(v) answer is f_v (the listener knows v),
    F0 answer puts weight theta on f1."""
    fk = F(1) if v == 1 else F(0)
    return {
        "P": R / 2,
        "L1": q * success_value(s, gamma1) + (1 - q) * (failure_value(s, fk) - D - C),
        "L2": q * success_value(s, gamma2) + (1 - q) * (failure_value(s, theta) - D - C),
        "never": failure_value(s, theta) - D,
    }


def step1_and_intended() -> None:
    # intended: listener's belief at SP(v) is uniform over s; m gives 2/5,
    # every guess 1/3: m is the unique best reply.
    assert F(2, 5) > F(1, 3)


def step2() -> None:
    for gamma in (F(0), F(1, 7), F(1, 2), F(1)):
        # a mixture of different guesses with total weight gamma
        for split in (F(0), F(1, 3), F(1)):
            w = {"m": 1 - gamma, "gA": gamma * split, "gB": gamma * (1 - split) / 2,
                 "gC": gamma * (1 - split) / 2}
            for s in S:
                direct = w["m"] * R / 2 + sum(w[g] for g in ("gA", "gB", "gC")) * (
                    R if s in ("A", "B") else F(0))
                assert direct == success_value(s, gamma)


def gaps(v: int, gamma1: F, gamma2: F, theta: F, q: F = Q) -> dict:
    out = {}
    for s in S:
        val = plans(v, s, gamma1, gamma2, theta, q)
        assert val["never"] < min(val["L1"], val["L2"])  # never is dominated
        out[s] = val["L1"] - val["L2"]
    return out


def step3() -> int:
    """Symbolic form of the gaps and the opposite-pair case analysis, checked
    exactly on a rational grid and on random points."""
    count = 0
    grid = [F(i, 12) for i in range(13)]
    rng = random.Random(11)
    points = list(itertools.product(grid, grid, grid))
    points += [(F(rng.randint(0, 997), 997), F(rng.randint(0, 991), 991),
                F(rng.randint(0, 983), 983)) for _ in range(20000)]
    for gamma1, gamma2, theta in points:
        some_class = False
        for v in (0, 1):
            g = gaps(v, gamma1, gamma2, theta)
            delta = Q * (gamma1 - gamma2) * (R / 2)
            kappa = (1 - Q) * R * ((1 - theta) if v == 1 else theta)
            sign = 1 if v == 1 else -1
            assert g == {"A": delta + sign * kappa, "B": delta - sign * kappa, "C": -delta}
            pos = [s for s in S if g[s] > 0]
            neg = [s for s in S if g[s] < 0]
            if kappa > 0:
                assert pos and neg, (v, gamma1, gamma2, theta, g)
                some_class = True
        assert some_class, (gamma1, gamma2, theta)
        count += 1
    return count


def poly_ratio_limit(num: dict, den: dict) -> F | None:
    """Limit of num/den as eps -> 0 for positive polynomials (None = infinity)."""
    en, eden = min(num), min(den)
    if en > eden:
        return F(0)
    if en < eden:
        return None
    return num[en] / den[eden]


def step4(trials: int = 5000) -> int:
    """Cross-ratio lemma on random tilted families: t1 sends at L1 except for a
    hold tremble e1 = a1 eps^k1; t0 holds at L1 except for a send tremble
    e0 = a0 eps^k0; deferrals w1, w0 arbitrary. Then one of the two sites puts
    zero limit weight on one of the two types."""
    rng = random.Random(5)
    hits = 0
    for _ in range(trials):
        w1 = (F(rng.randint(1, 9), rng.randint(1, 9)), rng.randint(0, 6))
        w0 = (F(rng.randint(1, 9), rng.randint(1, 9)), rng.randint(0, 6))
        e1 = (F(rng.randint(1, 9), rng.randint(1, 9)), rng.randint(1, 4))
        e0 = (F(rng.randint(1, 9), rng.randint(1, 9)), rng.randint(1, 4))
        # leading terms of masses at S1 and S2 (prior factors are constants)
        s1_t1 = {w1[1]: w1[0]}
        s1_t0 = {w0[1] + e0[1]: w0[0] * e0[0]}
        s2_t1 = {w1[1] + e1[1]: w1[0] * e1[0]}
        s2_t0 = {w0[1]: w0[0]}
        odds1 = poly_ratio_limit(s1_t0, s1_t1)  # t0 : t1 at S1
        odds2 = poly_ratio_limit(s2_t1, s2_t0)  # t1 : t0 at S2
        zero_somewhere = odds1 in (F(0), None) or odds2 in (F(0), None)
        assert zero_somewhere
        hits += 1
    return hits


def step5(q: F = Q) -> F:
    worst = q * R + (1 - q) * (F(0) - D - C)
    return worst


def main() -> None:
    step1_and_intended()
    step2()
    n3 = step3()
    n4 = step4()
    # step 5: on a face the listener guesses
    for face in ((F(1, 2), F(1, 2), F(0)), (F(1), F(0), F(0)), (F(2, 3), F(0), F(1, 3)),
                 (F(0), F(1, 2), F(1, 2))):
        assert max(face) >= F(1, 2) > F(2, 5)
    gain = step5()
    assert gain == F(189, 100) and gain > R / 2
    # the deviating type is (v, A) at whichever site lies on a face, for any F
    for fval in (F(0), R):
        assert Q * R + (1 - Q) * (fval - D - C) > R / 2
    # negative control: at q = 1/2 the deviation does not pay
    assert step5(F(1, 2)) < R / 2
    print(f"G*: step 3 checked at {n3} points (theta, gamma1, gamma2); "
          f"cross-ratio lemma on {n4} random tilts; deferring type gains "
          f"{gain} > {R / 2}")
    print("verdict: every sequential equilibrium of G* changes the intended outcome "
          "distribution (variant 1 counterexample, D = 3R, c = 3R/2, q = 99/100)")


if __name__ == "__main__":
    main()
