"""Exact checks for single-slot attempts (SSA) with informed retry.

Comparison game: the types, prior, payoffs and listener of G*.
Sender plans after deferring the protected opening P:
  X  : attempt slot 1 (accepted w.p. q1); if dead, retry slot 2 (q2)
  Xn : attempt slot 1, no retry
  Y  : hold at slot 1, attempt slot 2 (q2)
  Z  : never attempt
A dead slot-1 attempt becomes public before the listener answers
(builder publishes it); a dead slot-2 attempt does not.
Charge c: expected audit charge for an owner with >= 1 dead attempt (cap 1).
Listener sites per class v: P, S1, S2E (dead slot-1 public, slot-2 success),
S2N (slot-2 success, nothing public), FE (v known), FN (no information).
"""
from fractions import Fraction as Fr
from itertools import product

TYPES = [(v, s) for v in (0, 1) for s in "ABC"]
PRIOR = {(v, s): (Fr(9, 20) if v == 1 else Fr(11, 20)) * Fr(1, 3) for v, s in TYPES}
DIR = {"A": 1, "B": 1, "C": -1}


def succ(R, s, g):
    """Sender value at a success site where the listener guesses w.p. g."""
    return R / 2 + g * (R / 2) * DIR[s]


def fail_known(R, v, s):
    """Listener knows v and answers f_v."""
    if s == "A":
        return R if v == 1 else 0
    if s == "B":
        return R if v == 0 else 0
    return 0


def fail_unknown(R, s, y):
    """Listener answers f1 w.p. y."""
    return {"A": y * R, "B": (1 - y) * R, "C": Fr(0)}[s]


COMPLETE = [False]


def plan_value(plan, t, L, R, D, c, q1, q2):
    """Tree evaluation. L = dict with g[(v,site)] and y (FN answer f1 prob).
    With COMPLETE[0], every dead attempt (slot 1 or 2) is public."""
    v, s = t
    g = lambda site: L["g"][(v, site)]
    if plan == "P":
        return succ(R, s, g("P"))
    if plan == "Z":
        return fail_unknown(R, s, L["y"]) - D
    if plan == "Y":
        yfail = fail_known(R, v, s) if COMPLETE[0] else fail_unknown(R, s, L["y"])
        return q2 * succ(R, s, g("S2N")) + (1 - q2) * (yfail - D - c)
    if plan == "Xn":
        return q1 * succ(R, s, g("S1")) + (1 - q1) * (fail_known(R, v, s) - D - c)
    if plan == "X":
        dead1 = q2 * succ(R, s, g("S2E")) + (1 - q2) * (fail_known(R, v, s) - D)
        return q1 * succ(R, s, g("S1")) + (1 - q1) * (dead1 - c)
    raise ValueError(plan)


SITES = ["P", "S1", "S2E", "S2N"]


def behaviour(gvals, y):
    return {"g": gvals, "y": y}


def zero_g():
    return {(v, site): Fr(0) for v in (0, 1) for site in SITES}


def vertex_behaviours():
    keys = [(v, site) for v in (0, 1) for site in SITES]
    for bits in product((0, 1), repeat=len(keys)):
        for y in (Fr(0), Fr(1)):
            yield behaviour({k: Fr(b) for k, b in zip(keys, bits)}, y)


# ---------------------------------------------------------------- split check

def lin(fn, R, D, c, q1, q2, v, s):
    """X - Y at g = 0 as a linear function of y: returns (a, b) with value a + b*y."""
    f0 = plan_value("X", (v, s), behaviour(zero_g(), Fr(0)), R, D, c, q1, q2) \
        - plan_value("Y", (v, s), behaviour(zero_g(), Fr(0)), R, D, c, q1, q2)
    f1 = plan_value("X", (v, s), behaviour(zero_g(), Fr(1)), R, D, c, q1, q2) \
        - plan_value("Y", (v, s), behaviour(zero_g(), Fr(1)), R, D, c, q1, q2)
    return (f0, f1 - f0)


def ev(l, y):
    return l[0] + l[1] * y


def roots(l):
    if l[1] == 0:
        return []
    return [-l[0] / l[1]]


def nonsplit_intervals(ls, lo, hi):
    """Within [lo, hi] where min/max selection is fixed, return the closed
    sub-intervals where class does NOT split:
      fC + min(fA,fB) >= 0  or  fC + max(fA,fB) <= 0."""
    fA, fB, fC = ls
    mid = (lo + hi) / 2
    mn, mx = (fA, fB) if ev(fA, mid) <= ev(fB, mid) else (fB, fA)
    l1 = (fC[0] + mn[0], fC[1] + mn[1])  # >= 0
    l2 = (fC[0] + mx[0], fC[1] + mx[1])  # <= 0
    out = []
    for l, sign in ((l1, 1), (l2, -1)):
        a, b = l[0] * sign, l[1] * sign  # want a + b y >= 0
        if b == 0:
            if a >= 0:
                out.append((lo, hi))
        elif b > 0:
            r = -a / b
            if r <= hi:
                out.append((max(lo, r), hi))
        else:
            r = -a / b
            if r >= lo:
                out.append((lo, min(hi, r)))
    return out


def split_covers(R, D, c, q1, q2):
    """True iff for every y in [0,1] some class has two types with opposite
    strict preferences between X and Y, for every success-site behaviour."""
    L = {v: [lin(None, R, D, c, q1, q2, v, s) for s in "ABC"] for v in (0, 1)}
    # verify the success shift acts along DIR with a common coefficient
    for B in list(vertex_behaviours())[::37]:
        for v in (0, 1):
            diffs = []
            for s in "ABC":
                full = plan_value("X", (v, s), B, R, D, c, q1, q2) - plan_value("Y", (v, s), B, R, D, c, q1, q2)
                base = ev(L[v]["ABC".index(s)], B["y"])
                diffs.append((full - base) * DIR[s])
            assert diffs[0] == diffs[1] == diffs[2], "success shift not along (1,1,-1)"
    pts = {Fr(0), Fr(1)}
    for v in (0, 1):
        fA, fB, fC = L[v]
        for l in (fA, fB, fC, (fA[0] - fB[0], fA[1] - fB[1]),
                  (fC[0] + fA[0], fC[1] + fA[1]), (fC[0] + fB[0], fC[1] + fB[1])):
            for r in roots(l):
                if 0 <= r <= 1:
                    pts.add(r)
    pts = sorted(pts)
    witness = None
    for lo, hi in zip(pts, pts[1:]):
        n1 = nonsplit_intervals(L[1], lo, hi)
        n0 = nonsplit_intervals(L[0], lo, hi)
        for a1, b1 in n1:
            for a0, b0 in n0:
                a, b = max(a1, a0), min(b1, b0)
                if a <= b:
                    witness = a
                    return False, witness
    return True, None


def strict_split_at(R, D, c, q1, q2, B):
    for v in (0, 1):
        d = [plan_value("X", (v, s), B, R, D, c, q1, q2) - plan_value("Y", (v, s), B, R, D, c, q1, q2) for s in "ABC"]
        if max(d) > 0 > min(d):
            return True
    return False


def brute_split(R, D, c, q1, q2, n=40):
    """Independent sanity check on a rational grid of listener behaviours."""
    grid = [Fr(i, n) for i in range(n + 1)]
    gg = [Fr(0), Fr(1, 3), Fr(1)]
    for y in grid:
        for g1, gE, gN in product(gg, repeat=3):
            for h1, hE, hN in product(gg, repeat=3):
                gv = zero_g()
                gv[(1, "S1")], gv[(1, "S2E")], gv[(1, "S2N")] = g1, gE, gN
                gv[(0, "S1")], gv[(0, "S2E")], gv[(0, "S2N")] = h1, hE, hN
                if not strict_split_at(R, D, c, q1, q2, behaviour(gv, y)):
                    return False
    return True


# ------------------------------------------------------------ other premises

def other_premises(R, D, c, q1, q2, face_sites):
    ok = {}
    # Y beats never, retry beats no retry, for every listener behaviour (vertices)
    ok["Y>Z"] = all(plan_value("Y", t, B, R, D, c, q1, q2) > plan_value("Z", t, B, R, D, c, q1, q2)
                    for B in vertex_behaviours() for t in TYPES)
    ok["X>Xn"] = all(plan_value("X", t, B, R, D, c, q1, q2) > plan_value("Xn", t, B, R, D, c, q1, q2)
                     for B in vertex_behaviours() for t in TYPES)
    # Profitable deferral when the listener guesses surely at a face site:
    # the guessed site gets g = 1, every other site arbitrary (vertices).
    via = {"S1": "X", "S2E": "X", "S2N": "Y"}
    for site in face_sites:
        best = None
        for B in vertex_behaviours():
            for v in (0, 1):
                gv = dict(B["g"])
                gv[(v, site)] = Fr(1)
                gv[(v, "P")] = Fr(0)  # intended answer on path
                BB = behaviour(gv, B["y"])
                gain = max(plan_value(via[site], (v, s), BB, R, D, c, q1, q2)
                           - plan_value("P", (v, s), BB, R, D, c, q1, q2) for s in "AB")
                best = gain if best is None else min(best, gain)
        ok["face " + site + " gain"] = best
    return ok


def window(R, D, c, q1, q2):
    """Closed-form obstruction window for the G* payoffs."""
    K = (1 - q2) * q1 * (D + R / 2) - (q2 - q1) * c
    two_k = 2 * K / ((1 - q2) * R)
    return (q1 - Fr(1, 2) < two_k < Fr(1, 2)), two_k


def report(name, R, D, c, q1, q2, face_sites, brute=True):
    covers, wit = split_covers(R, D, c, q1, q2)
    w, two_k = window(R, D, c, q1, q2)
    assert covers == w, (name, covers, w)
    print(f"--- {name}: R={R} D={D} c={c} q1={q1} q2={q2}")
    print(f"    split for every listener behaviour: {covers}"
          + ("" if covers else f" (non-split y = {wit})") + f"; 2k = {float(two_k):.5f}")
    if brute:
        b = brute_split(R, D, c, q1, q2)
        assert b == covers or (not covers), (name, b, covers)
        print(f"    grid sanity check agrees: {b if covers else 'n/a'}")
    prem = other_premises(R, D, c, q1, q2, face_sites)
    for k, v in prem.items():
        print(f"    {k}: {v if isinstance(v, bool) else str(v) + ' (' + format(float(v), '.5f') + ')'}")
    return covers, prem


def main():
    R, D = Fr(2), Fr(6)
    # Intended game: at the prior over s the safe answer is the unique best reply,
    # and on a face of the simplex some guess beats it.
    assert Fr(1, 3) < Fr(2, 5) < Fr(1, 2)

    # Instance I: lawful dead attempts (c = 0), unreliable first slot.
    for q1 in (Fr(0), Fr(1, 20)):
        covers, prem = report("I", R, D, Fr(0), q1, Fr(99, 100), ["S2E", "S2N"])
        assert covers and prem["Y>Z"] and prem["X>Xn"]
        assert prem["face S2E gain"] > 0 and prem["face S2N gain"] > 0

    # Instance II: charged dead attempts at G*'s margin c = 3, tuned builder.
    q2 = Fr(999, 1000)
    q1 = Fr(5994, 6013)
    covers, prem = report("II", R, D, Fr(3), q1, q2, ["S1", "S2N"], brute=False)
    assert covers and prem["Y>Z"] and prem["X>Xn"]
    assert prem["face S1 gain"] > 0 and prem["face S2N gain"] > 0
    # Raw options in II are dominated for every listener behaviour:
    c = Fr(3)
    assert c > R / 2 + (1 - q2) * R / q2          # extra visible openings / talk
    assert q1 * c > 0                               # pipelined slot-2 envelope costs q1*c, gains nothing

    # Instance III: every dead attempt public (complete observation), charge cc = 3
    # once per owner, tuned builder: split iff q1c(1-q2c)D < (q2c-q1c)cc < q1c(1-q2c)(D+R/2).
    COMPLETE[0] = True
    q2c = Fr(999, 1000)
    q1c = Fr(24975, 25054)
    cc = Fr(3)
    assert q1c * (1 - q2c) * D < (q2c - q1c) * cc < q1c * (1 - q2c) * (D + R / 2)
    L = {v: [lin(None, R, D, cc, q1c, q2c, v, s) for s in "ABC"] for v in (0, 1)}
    for v in (0, 1):
        fA, fB, fC = L[v]
        assert fA[1] == fB[1] == fC[1] == 0  # no dependence on the uninformed answer
        assert fC[0] + min(fA[0], fB[0]) < 0 < fC[0] + max(fA[0], fB[0])
    for B in list(vertex_behaviours())[::53]:
        assert strict_split_at(R, D, cc, q1c, q2c, B)
    prem = other_premises(R, D, cc, q1c, q2c, ["S1", "S2N"])
    print(f"--- III (complete observation): c={cc} q1c={q1c} q2c={q2c}: split in both classes; {prem}")
    assert prem["Y>Z"] and prem["X>Xn"] and prem["face S1 gain"] > 0 and prem["face S2N gain"] > 0
    # control: lawful dead attempts (cc = 0) under complete observation align every type on X
    for y in (Fr(0), Fr(1)):
        B = behaviour(zero_g(), y)
        assert all(plan_value("X", t, B, R, D, Fr(0), q1c, q2c) > plan_value("Y", t, B, R, D, Fr(0), q1c, q2c) for t in TYPES)
    COMPLETE[0] = False
    print("    control: with lawful dead attempts every type strictly prefers X")

    # Negative controls: the split premise fails.
    covers, _ = report("control: equal reliabilities", R, D, Fr(0), Fr(99, 100), Fr(99, 100), [], brute=False)
    assert not covers
    covers, _ = report("control: G* margin, equal reliabilities", R, D, Fr(3), Fr(99, 100), Fr(99, 100), [], brute=False)
    assert not covers
    covers, _ = report("control: II builder, deposit x10", R, D, Fr(30), q1, q2, [], brute=False)
    assert not covers
    covers, _ = report("control: I with q1 = 1/10", R, D, Fr(0), Fr(1, 10), Fr(99, 100), [], brute=False)
    assert not covers

    # Window formula agrees with the exact piecewise check on a parameter grid.
    n = 0
    for q1 in [Fr(i, 40) for i in range(0, 40)]:
        for q2 in (Fr(9, 10), Fr(99, 100), Fr(999, 1000)):
            for c in (Fr(0), Fr(1, 100), Fr(1, 10), Fr(1), Fr(3)):
                if q1 >= q2:
                    continue
                a, _ = split_covers(R, D, c, q1, q2)
                b, _ = window(R, D, c, q1, q2)
                assert a == b, (q1, q2, c)
                n += 1
    print(f"window formula agrees with exact check at {n} parameter points")

    # Reliability floor: if q_j * D > R at both late slots and every success site
    # uses the intended answer, every type strictly prefers attempting at slot 1
    # (lawful dead attempts), whatever the failure answer y.
    for q1 in (Fr(1, 3) + Fr(1, 100), Fr(1, 2), Fr(9, 10)):
        for q2 in (Fr(1, 2), Fr(99, 100)):
            assert q1 * D > R
            for y in (Fr(0), Fr(1, 2), Fr(1)):
                B = behaviour(zero_g(), y)
                assert all(plan_value("X", t, B, R, D, Fr(0), q1, q2) > plan_value("Y", t, B, R, D, Fr(0), q1, q2)
                           for t in TYPES)
    print("reliability floor q*D > R aligns every type on attempting (checked grid)")
    print("all assertions passed")


if __name__ == "__main__":
    main()
