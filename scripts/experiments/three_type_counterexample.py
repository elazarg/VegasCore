#!/usr/bin/env python3
"""Exact checks for the three-types-per-value counterexample (variant 1).

Game G*. Type t = (v, s), v in {0,1}, s in {A, B, C}; prior P(v=1) = 9/20,
s uniform and independent. R = 2, D = 6 (= 3R), c = 3 (> R), q = 99/100.
Protected turn P, late turns L1, L2; inclusion coin q; listener activated
between L1 and L2 sees a pending opening (learns v). Inclusion resolves at the
deadline. A answers once after resolution from the set
  {m, gA, gB, gC, f0, f1}.
Success: A gets 2/5 for m, [s = i] for gi, -1 for f0/f1.
         B gets R/2 for m, (R, R, 0) for any gi (by s = A, B, C), 0 for f*.
Failure: A gets [v = j] for fj, -1 otherwise.
         B gets phi(s, f1) = (R, 0, 0), phi(s, f0) = (0, R, 0); 0 otherwise.
Every claim below is an assertion with exact rationals.
"""

from fractions import Fraction as F
from itertools import product
import random

R, D, C, Q = F(2), F(6), F(3), F(99, 100)
S = ("A", "B", "C")
TYPES = tuple(product((0, 1), S))
SUCC = ("m", "gA", "gB", "gC", "f0", "f1")


def a_succ(a, t):
    if a == "m":
        return F(2, 5)
    if a in ("f0", "f1"):
        return F(-1)
    return F(int(a[1] == t[1]))


def b_succ(a, t):
    if a == "m":
        return R / 2
    if a in ("f0", "f1"):
        return F(0)
    return {"A": R, "B": R, "C": F(0)}[t[1]]


def a_fail(a, t):
    if a in ("f0", "f1"):
        return F(int(int(a[1]) == t[0]))
    return F(-1)


def b_fail(a, t):
    if a == "f1":
        return {"A": R, "B": F(0), "C": F(0)}[t[1]]
    if a == "f0":
        return {"A": F(0), "B": R, "C": F(0)}[t[1]]
    return F(0)


def best(table, belief):
    val = {a: sum(w * table(a, t) for t, w in belief.items()) for a in SUCC}
    top = max(val.values())
    return {a for a, x in val.items() if x == top}


def expect(table, mix, t):
    return sum(p * table(a, t) for a, p in mix.items())


# 1. Intended SE: at SP(v) the belief is uniform over s, m is the unique best reply.
for v in (0, 1):
    assert best(a_succ, {(v, s): F(1, 3) for s in S}) == {"m"}
# Failure sets: fj with j = v is A's unique best reply whenever A knows v.
for v in (0, 1):
    for w in product(range(4), repeat=3):
        if sum(w) == 0:
            continue
        bel = {(v, s): F(x, sum(w)) for s, x in zip(S, w)}
        assert best(a_fail, bel) == {f"f{v}"}

# 2. On every face of the simplex over s (one type has belief 0), A's best
#    replies at a success set are guesses only (max mu_i >= 1/2 > 2/5).
N = 60
for v in (0, 1):
    for excluded in S:
        others = [s for s in S if s != excluded]
        for k in range(N + 1):
            bel = {(v, excluded): F(0), (v, others[0]): F(k, N), (v, others[1]): F(N - k, N)}
            br = best(a_succ, bel)
            assert br <= {"gA", "gB", "gC"}, (bel, br)
            for a in br:  # every best reply pays B (R, R, 0)
                assert [b_succ(a, (v, s)) for s in S] == [R, R, F(0)]


# 3. B's late-plan values and the preference identity
#    pref(t) = val(L1) - val(L2) = q (sigma1 - sigma2) (R/2) d(s) + (1 - q) g_v delta(s)
#    with d = (1, 1, -1), delta = (R, -R, 0), g_1 = 1 - theta, g_0 = -theta.
def plans(t, r1, r2, theta):
    v = t[0]
    f1v = {f"f{v}": F(1)}
    f0 = {"f1": theta, "f0": 1 - theta}
    u1, u2 = expect(b_succ, r1, t), expect(b_succ, r2, t)
    p1, p0 = expect(b_fail, f1v, t), expect(b_fail, f0, t)
    return {"L1": Q * u1 + (1 - Q) * (p1 - D - C),
            "L2": Q * u2 + (1 - Q) * (p0 - D - C),
            "never": p0 - D}


d = {"A": 1, "B": 1, "C": -1}
delta = {"A": R, "B": -R, "C": F(0)}
rng = random.Random(1)


def rand_mix(actions):
    w = [rng.randint(0, 5) for _ in actions]
    if sum(w) == 0:
        w[0] = 1
    return {a: F(x, sum(w)) for a, x in zip(actions, w)}


for _ in range(2000):
    r1, r2 = rand_mix(("m", "gA", "gB", "gC")), rand_mix(("m", "gA", "gB", "gC"))
    theta = F(rng.randint(0, 20), 20)
    g1 = 1 - r1["m"]
    g2 = 1 - r2["m"]
    for t in TYPES:
        val = plans(t, r1, r2, theta)
        gv = (1 - theta) if t[0] == 1 else -theta
        assert val["L1"] - val["L2"] == Q * (g1 - g2) * (R / 2) * d[t[1]] + (1 - Q) * gv * delta[t[1]]
        # L2 strictly beats never for every response and every theta
        assert val["L2"] > val["never"]


# 4. Case analysis: for every theta and every guess probabilities at S1(v), S2(v),
#    some class v has a strictly opposite pair (one type strictly L1, one strictly L2).
def opposite_pair(x, g):
    pref = {"A": x + g, "B": x - g, "C": -x}
    return any(pref[s] > 0 for s in S) and any(pref[s] < 0 for s in S)


grid = [F(k, 10) for k in range(11)]
count = 0
for theta in grid:
    for gs in product(grid, repeat=4):  # guess prob at S1(1), S2(1), S1(0), S2(0)
        ok = False
        for v, (a1, a2) in ((1, gs[0:2]), (0, gs[2:4])):
            g = (1 - Q) * ((1 - theta) if v == 1 else -theta) * R
            x = Q * (a1 - a2) * (R / 2)
            if g != 0 and opposite_pair(x, g):
                ok = True
        assert ok
        count += 1

# 5. A type rewarded by a guess at a late success set strictly gains from
#    deviating at P, whatever A does at the failure sets.
for t in TYPES:
    if t[1] in ("A", "B"):
        worst_late = Q * R + (1 - Q) * (0 - D - C)
        assert worst_late > b_succ("m", t), worst_late

# 6. Margins.
assert D >= 3 * R and C > R

print(f"intended SE ok; face best replies are guesses; identity ok on 2000 random profiles;"
      f" opposite pair in some class on {count} grid profiles;"
      f" guess-rewarded deviation value {Q * R - (1 - Q) * (D + C)} > {R / 2}")
