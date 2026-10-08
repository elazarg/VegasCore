#!/usr/bin/env python3
"""Exact test of a timed-release reveal on the late-leak counterexample G*.

Background: docs/open-problem-late-turn-equilibria.md (game G*, mechanized in
Vegas/Examples/LateLeak). There the owner B opens its committed value v at a
protected turn P or late at L1, L2 (content-blind inclusion with probability
q); a listener activated between L1 and L2 sees pending packets; a leaked,
dropped L1 opening tells the listener v after the failure. Every sequential
equilibrium of G* changes the intended outcome law.

Timed-release mode (an ideal construct implementable by timed commitments):
the commitment carries validated recovery material, and a service transition
publishes v at the reveal's position; the reveal cannot fail and the runtime
offers the owner no opening action. The script decides, with exact fractions
and Kreps-Wilson consistency (fully mixed polynomial families in eps with
arbitrary type- and node-dependent tremble orders and coefficients):

Part 1 (no owner opening). Common types, prior, payoffs and listener of G*
(R = 2, D = 6, c = 3, q = 99/100).
- TR: the commitment is given (as in G*). B has no decision; the intended
  outcome is the unique SE outcome.
- PC: the commitment is a protected packet that B may omit (binding omission,
  forfeit D, nothing learned). Omission is strictly dominated when D > R/2,
  so the intended outcome is the unique SE outcome.
- LC: the commitment itself has a protected turn and two late turns with the
  G* inclusion and leak rules (a dropped binding forfeits D and costs c).
  * LC-recoverable: the listener can recover v from the recovery material of a
    pending commitment it saw and dropped before it answers (any holder can
    force-open a timed commitment). This is G* with "commit" in place of
    "open": the plan values coincide with the independent encoding of G* in
    late_turn_search.py, so G*'s impossibility applies verbatim (Lean:
    late_leak_not_preserved_when_deferral_pays).
  * LC-opaque: the listener cannot recover v from dropped material before it
    answers (it only sees that a binding was pending). A preserving SE exists
    (explicit assessment, type-independent trembles) whenever all types agree
    on sending versus never at a late turn: q(D - R/2) >= (1 - q) c or
    q(D + R/2) < (1 - q) c (opaque_construction_applies); otherwise this
    script decides nothing for LC-opaque.
  For LC-recoverable off the G* theorem's hypothesis, the structured search
  of late_turn_search.py is run; a hit is an exactly re-checked preserving
  SE, no hit leaves the point undecided.

Part 2 (owner early opening as a raw network packet). In addition to forced
release, B may send an early opening at a protected early turn Ep (always
included), at E1 (before the listener's activation: it leaks) or at E2 (after
it). Every early-opening envelope is seen by the audit and charged c' at
settlement whether or not it was included. Since v is published at the reveal
anyway and the listener of G* acts only afterwards, an early opening is a pure
timing signal there:
- c' = 0 (control): a preserving SE exists (uniform trembles), although some
  consistent completions are not equilibria (negative control).
- c' > R (above the deterrence bound, the spread of B's base utility): every
  early opening is strictly dominated whatever the listener does, so the
  intended outcome is the unique SE outcome.
- Interim extension (control showing when the forbidden action matters): the
  listener also takes an interim action y in {y0, y1} at activation, before
  release (listener gets [y = v], B gets g [y = 1]). Then the intended outcome
  is an SE outcome iff g <= c'; with c' = 0 and g > 0 no SE has it.

Part 3: the same verdicts over a grid of (D, c, q), including q near 1.

Run: python scripts/experiments/timed_release_probe.py
"""

from __future__ import annotations

import itertools
import sys
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import late_turn_search as lts  # noqa: E402  (independent encoding of G*)

S = ("A", "B", "C")
TYPES = tuple((v, s) for v in (0, 1) for s in S)
P_V1 = F(9, 20)
SUCCESS = ("m", "gA", "gB", "gC")
FAILURE = ("f1", "f0")
INTERIM = ("y0", "y1")


def prior(t) -> F:
    return (P_V1 if t[0] else 1 - P_V1) / 3


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


def leading(p):
    assert p, "a fully mixed reach mass is never identically zero"
    e = min(p)
    assert p[e] > 0
    return e, p[e]


def limit_belief(masses: dict) -> dict:
    leads = {k: leading(m) for k, m in masses.items()}
    e = min(x for x, _ in leads.values())
    weights = {k: (c if x == e else F(0)) for k, (x, c) in leads.items()}
    total = sum(weights.values())
    return {k: w / total for k, w in weights.items()}


# ------------------------------------------------------------ listener sites


def answers(site: str):
    kind = site.split("|")[0]
    if kind.startswith("Y"):
        return INTERIM
    if kind.startswith("F"):
        return FAILURE
    return SUCCESS


class Payoffs:
    def __init__(self, r: F, g: F = F(0)):
        self.r, self.g = r, g

    def listener(self, site: str, a: str, t) -> F:
        v, s = t
        if a == "m":
            return F(2, 5)
        if a.startswith("g"):
            return F(int(a[1] == s))
        if a in FAILURE:
            return F(int(a == f"f{v}"))
        return F(int(a == f"y{v}"))

    def sender(self, site: str, a: str, t) -> F:
        v, s = t
        r = self.r
        if a == "m":
            return r / 2
        if a.startswith("g"):
            return r if s in ("A", "B") else F(0)
        if a == "f1":
            return r if s == "A" else F(0)
        if a == "f0":
            return r if s == "B" else F(0)
        return self.g * int(a == "y1")

    def spread(self) -> F:
        """Range of B's base utility over all answer profiles (deterrence bound)."""
        return self.r + self.g


# --------------------------------------------------------------------- trees
# node: ("choice", name, {action: node}) | ("chance", [(p, node)])
#     | ("leaf", {decision point: site}, penalty)


def leaf(sites, pen=F(0)):
    return ("leaf", dict(sites), F(pen))


def tree_timed_release(t):
    return leaf({"final": f"SR|{t[0]}"})


def tree_protected_commitment(t, d):
    v = t[0]
    return ("choice", "Pc", {"commit": leaf({"final": f"SR|{v}"}),
                             "omit": leaf({"final": "F0"}, d)})


def tree_late(t, d, c, q, recoverable: bool, first="commit"):
    """G* timing. With first = 'open' and recoverable = True this is G*."""
    v = t[0]
    f1 = f"F1|{v}" if recoverable else "F1"
    l2 = ("choice", "L2", {
        "send": ("chance", [(q, leaf({"final": f"S2|{v}"})),
                            (1 - q, leaf({"final": "F0"}, d + c))]),
        "never": leaf({"final": "F0"}, d)})
    l1 = ("choice", "L1", {
        "send": ("chance", [(q, leaf({"final": f"S1|{v}"})),
                            (1 - q, leaf({"final": f1}, d + c))]),
        "hold": l2})
    return ("choice", "P", {first: leaf({"final": f"SP|{v}"}), "defer": l1})


def tree_early(t, q, cprime, interim: bool):
    """Forced release plus an optional charged early opening."""
    v = t[0]

    def lf(final, known, pen):
        sites = {"final": final}
        if interim:
            sites["interim"] = f"Y|{v}" if known else "Y|-"
        return leaf(sites, pen)

    e2 = ("choice", "E2", {
        "send": ("chance", [(q, lf(f"I2|{v}", False, cprime)),
                            (1 - q, lf(f"N|{v}", False, cprime))]),
        "none": lf(f"N|{v}", False, 0)})
    e1 = ("choice", "E1", {
        "send": ("chance", [(q, lf(f"I1|{v}", True, cprime)),
                            (1 - q, lf(f"D1|{v}", True, cprime))]),
        "hold": e2})
    return ("choice", "Ep", {"open": lf(f"IP|{v}", True, cprime), "wait": e1})


# ------------------------------------------------------------------- checker


class Assessment:
    def __init__(self, natural, tremble, mixes):
        self.natural = natural  # (t, node) -> action
        self.tremble = tremble  # (t, node, action) -> (coef, exp), non-natural
        self.mixes = mixes  # site -> {answer: prob}


def walk(node, t, a: Assessment, mass, out):
    kind = node[0]
    if kind == "leaf":
        out.append((node, mass))
    elif kind == "chance":
        for p, sub in node[1]:
            walk(sub, t, a, pmul(mass, poly((p, 0))), out)
    else:
        _, name, acts = node
        nat = a.natural[(t, name)]
        others = [x for x in acts if x != nat]
        small = {x: poly(a.tremble.get((t, name, x), (F(1), 1))) for x in others}
        big = poly((1, 0), *[(-c, e) for x in others for e, c in small[x].items()])
        for x, sub in acts.items():
            walk(sub, t, a, pmul(mass, big if x == nat else small[x]), out)
    return out


def leaf_value(node, pay: Payoffs, mixes, t) -> F:
    _, sites, pen = node
    return sum(sum(p * pay.sender(site, x, t) for x, p in mixes[site].items())
               for site in sites.values()) - pen


def value(node, pay, mixes, t) -> F:
    if node[0] == "leaf":
        return leaf_value(node, pay, mixes, t)
    if node[0] == "chance":
        return sum(p * value(sub, pay, mixes, t) for p, sub in node[1])
    return max(value(sub, pay, mixes, t) for sub in node[2].values())


def best_set(opts, f) -> set:
    vals = {x: f(x) for x in opts}
    top = max(vals.values())
    return {x for x, y in vals.items() if y == top}


def check(trees: dict, pay: Payoffs, a: Assessment, intended: dict) -> dict:
    """Exact check of an SE with the intended outcome law. Raises
    AssertionError on any violation; returns the limit beliefs."""
    reach: dict[str, dict] = {}
    path_law: dict = {}
    for t in TYPES:
        for node, mass in walk(trees[t], t, a, poly((prior(t), 0)), []):
            for site in node[1].values():
                reach.setdefault(site, {})
                reach[site][t] = padd(reach[site].get(t, {}), mass)
            if mass.get(0, F(0)) != 0:  # positive limit probability: on path
                for site in node[1].values():
                    for x, p in a.mixes[site].items():
                        if p:
                            key = (t, x)
                            path_law[key] = path_law.get(key, F(0)) + mass[0] * p
    beliefs = {}
    for site, by_type in reach.items():
        mu = limit_belief({t: m for t, m in by_type.items() if m})
        beliefs[site] = mu
        br = best_set(answers(site), lambda x: sum(w * pay.listener(site, x, t)
                                                   for t, w in mu.items()))
        assert all(p == 0 or x in br for x, p in a.mixes[site].items()), (site, mu, a.mixes[site])
    # sender rationality at every node (on and off path)
    for t in TYPES:
        stack = [trees[t]]
        while stack:
            node = stack.pop()
            if node[0] == "chance":
                stack.extend(sub for _, sub in node[1])
            elif node[0] == "choice":
                _, name, acts = node
                vals = {x: value(sub, pay, a.mixes, t) for x, sub in acts.items()}
                assert vals[a.natural[(t, name)]] == max(vals.values()), (t, name, vals)
                stack.extend(acts.values())
    assert path_law == intended, (path_law, intended)
    return beliefs


def intended_law(interim: bool) -> dict:
    law = {(t, "m"): prior(t) for t in TYPES}
    if interim:
        law.update({(t, "y0"): prior(t) for t in TYPES})
    return law


def natural_by_backward_induction(trees, pay, mixes, preference) -> dict:
    """B's natural choice at every node: a best reply, ties broken by order."""
    nat = {}
    for t in TYPES:
        stack = [trees[t]]
        while stack:
            node = stack.pop()
            if node[0] == "chance":
                stack.extend(sub for _, sub in node[1])
            elif node[0] == "choice":
                _, name, acts = node
                vals = {x: value(sub, pay, mixes, t) for x, sub in acts.items()}
                top = max(vals.values())
                nat[(t, name)] = min((x for x in acts if vals[x] == top), key=preference.index)
                stack.extend(acts.values())
    return nat


PREF = ["commit", "wait", "open", "hold", "none", "send", "never", "defer", "omit"]
# early-opening model prefers not opening; late model prefers sending at L1
PREF_LATE = ["commit", "open", "send", "hold", "never", "defer", "omit"]


def uniform_assessment(trees, pay, mixes, preference) -> Assessment:
    """Type-independent trembles (every non-natural choice has probability eps)."""
    return Assessment(natural_by_backward_induction(trees, pay, mixes, preference), {}, mixes)


def rejected(fn) -> bool:
    try:
        fn()
    except AssertionError:
        return True
    return False


# --------------------------------------------------------------------- part 1


def part1_timed_release(r=F(2)) -> None:
    """TR: B has no decision; the only listener sites are SR(v), on path with
    the prior belief, where m is the unique best reply. Unique SE outcome."""
    pay = Payoffs(r)
    trees = {t: tree_timed_release(t) for t in TYPES}
    mixes = {f"SR|{v}": {"m": F(1)} for v in (0, 1)}
    beliefs = check(trees, pay, Assessment({}, {}, mixes), intended_law(False))
    for v in (0, 1):
        mu = beliefs[f"SR|{v}"]
        assert mu == {t: F(1, 3) for t in TYPES if t[0] == v}
        assert best_set(SUCCESS, lambda x: sum(w * pay.listener("", x, t) for t, w in mu.items())) == {"m"}
    # no choice node at all: nothing for a tremble to tilt
    assert all(trees[t][0] == "leaf" for t in TYPES)


def part1_protected_commitment(r, d) -> bool:
    """PC: omission is strictly dominated iff D > R/2 (whatever the answer at
    F0), so in every SE B commits and the listener plays m at SR(v)."""
    pay = Payoffs(r)
    dominated = all(max(pay.sender("F0", x, t) for x in FAILURE) - d < r / 2 for t in TYPES)
    assert dominated == (d > r / 2)
    if dominated:
        trees = {t: tree_protected_commitment(t, d) for t in TYPES}
        mixes = {f"SR|{v}": {"m": F(1)} for v in (0, 1)} | {"F0": {"f0": F(1)}}
        check(trees, pay, uniform_assessment(trees, pay, mixes, PREF), intended_law(False))
    return dominated


def late_mixes(recoverable: bool) -> dict:
    mixes = {}
    for v in (0, 1):
        for k in ("SP", "S1", "S2"):
            mixes[f"{k}|{v}"] = {"m": F(1)}
        if recoverable:
            mixes[f"F1|{v}"] = {f"f{v}": F(1)}
    if not recoverable:
        mixes["F1"] = {"f0": F(1)}
    mixes["F0"] = {"f0": F(1)}
    return mixes


def part1_late_commitment(r, d, c, q, recoverable: bool) -> bool:
    """True iff the uniform-tremble assessment (m at every success site, best
    failure answers) is a preserving SE."""
    pay = Payoffs(r)
    trees = {t: tree_late(t, d, c, q, recoverable) for t in TYPES}
    mixes = late_mixes(recoverable)
    a = uniform_assessment(trees, pay, mixes, PREF_LATE)
    return not rejected(lambda: check(trees, pay, a, intended_law(False)))


def opaque_construction_applies(r, d, c, q) -> bool:
    """With m at every success site and f0 at both failure sites, a late
    send beats never by q R/2 + q (D - f) - (1 - q) c, where f = R for type
    (v, B) and 0 otherwise. The uniform-tremble construction works iff all
    types agree (ties go to sending): otherwise only some types send and a
    success site has a belief on a face of the simplex, where the listener
    guesses. When it fails the script decides nothing."""
    diff_a = q * r / 2 + q * d - (1 - q) * c
    diff_b = diff_a - q * r
    return diff_b >= 0 or diff_a < 0


def cross_check_with_gstar_encoding(r, d, c, q) -> None:
    """LC-recoverable equals G*: B's plan values agree with the independent
    encoding in late_turn_search.py for many listener mixtures."""
    pay = Payoffs(r)
    design = lts.design_gstar(q, d, c)
    assert design.b_range() == r
    sname = {"A": 0, "B": 1, "C": 2}
    grid = [F(0), F(1, 3), F(1)]
    for g1, g2, th1, th0 in itertools.product(grid, repeat=4):
        for v in (0, 1):
            mine = {
                f"SP|{v}": {"m": F(1)},
                f"S1|{v}": {"m": 1 - g1, "gA": g1},
                f"S2|{v}": {"m": 1 - g2, "gC": g2},
                f"F1|{v}": {"f1": th1, "f0": 1 - th1},
                "F0": {"f1": th0, "f0": 1 - th0},
            }
            theirs = {("A", "S", 1, v): {"m": 1 - g1, "x0": g1},
                      ("A", "S", 2, v): {"m": 1 - g2, "x2": g2},
                      ("A", "Fk", v): {"1": th1, "0": 1 - th1},
                      ("A", "Fu"): {"1": th0, "0": 1 - th0}}
            for s in S:
                t = (v, s)
                tree = tree_late(t, d, c, q, True, first="open")
                vals = lts.plan_values(design, theirs, (v, sname[s]))
                l2 = tree[2]["defer"][2]["hold"]
                assert value(tree[2]["open"], pay, mine, t) == vals["P"]
                assert value(tree[2]["defer"][2]["send"], pay, mine, t) == vals[1]
                assert value(l2[2]["send"], pay, mine, t) == vals[2]
                assert value(l2[2]["never"], pay, mine, t) == vals["never"]


def deferral_pays(r, d, c, q) -> bool:
    """Hypothesis of the mechanized impossibility for G* (LateLeakParameters.DeferralPays)."""
    return r > 0 and (1 - q) * c < q * (d - r) and r / 2 < q * r - (1 - q) * (d + c)


def recoverable_verdict(r, d, c, q) -> str:
    cross_check_with_gstar_encoding(r, d, c, q)
    if deferral_pays(r, d, c, q):
        assert not part1_late_commitment(r, d, c, q, True)
        return "no SE has the intended outcome (G* theorem)"
    hit = lts.search(lts.design_gstar(q, d, c), max_mix=2)
    if hit is not None:  # re-verified by late_turn_search.check (exact)
        return "preserving SE exists (verified search hit)"
    return "undecided here"


# --------------------------------------------------------------------- part 2


def early_mixes(interim: bool) -> dict:
    mixes = {}
    for v in (0, 1):
        for k in ("IP", "I1", "I2", "D1", "N"):
            mixes[f"{k}|{v}"] = {"m": F(1)}
        if interim:
            mixes[f"Y|{v}"] = {f"y{v}": F(1)}
    if interim:
        mixes["Y|-"] = {"y0": F(1)}
    return mixes


def early_survives(r, q, cprime, g=None) -> bool:
    """Uniform-tremble preserving SE with an early-opening packet available."""
    interim = g is not None
    pay = Payoffs(r, g or F(0))
    trees = {t: tree_early(t, q, cprime, interim) for t in TYPES}
    mixes = early_mixes(interim)
    a = uniform_assessment(trees, pay, mixes, PREF)
    return not rejected(lambda: check(trees, pay, a, intended_law(interim)))


def early_strictly_dominated(r, cprime, g=F(0)) -> bool:
    """Every early-opening plan is worse than not opening, for every listener
    behaviour: max base - c' < 0 <= min base (base utilities lie in
    [0, spread], and the path value R/2 is at least the minimum)."""
    pay = Payoffs(r, g)
    return pay.spread() - cprime < F(0)


def early_bad_completion_rejected(r, q) -> None:
    """Negative control at c' = 0: tilt the E1 trembles toward (1, A) so that
    I1(1) is a point mass; the listener must guess there, and (1, A) then
    strictly prefers sending at E1 to holding, so this assessment fails."""
    pay = Payoffs(r)
    trees = {t: tree_early(t, q, F(0), False) for t in TYPES}
    mixes = early_mixes(False)
    a = uniform_assessment(trees, pay, mixes, PREF)
    for t in TYPES:
        if t != (1, "A"):
            a.tremble[(t, "E1", "send")] = (F(1), 3)
    beliefs = None
    try:
        beliefs = check(trees, pay, a, intended_law(False))
    except AssertionError:
        pass
    assert beliefs is None  # m is not a best reply at the point mass
    a.mixes = dict(mixes)
    a.mixes["I1|1"] = {"gA": F(1)}
    assert rejected(lambda: check(trees, pay, a, intended_law(False)))
    vals = {x: value(sub, pay, a.mixes, (1, "A")) for x, sub in trees[(1, "A")][2]["wait"][2].items()}
    assert vals["send"] > vals["hold"] == r / 2


def interim_necessity(r, q, cprime, g) -> bool:
    """If g > c', no SE has the intended outcome: on path the interim belief is
    the prior (y0 strictly best), after a protected early opening v = 1 is
    public (y1 strictly best), and every final answer gives (1, A) at least
    R/2, so (1, A) gains at least g - c' > 0 by opening at Ep."""
    pay = Payoffs(r, g)
    on_path = {t: prior(t) for t in TYPES}
    assert best_set(INTERIM, lambda x: sum(w * pay.listener("Y|-", x, t) for t, w in on_path.items())) == {"y0"}
    # any belief at Y|1 is supported on v = 1 types (the packet shows v)
    assert best_set(INTERIM, lambda x: pay.listener("Y|1", x, (1, "A"))) == {"y1"}
    assert all(pay.sender("", x, (1, "A")) >= r / 2 for x in SUCCESS)
    worst_gain = g - cprime  # Ep: interim g, final >= R/2 = path value
    return worst_gain > 0


# --------------------------------------------------------------------- main


def main() -> None:
    r, d, c, q = F(2), F(6), F(3), F(99, 100)

    # ---- part 1 at G*'s parameters
    part1_timed_release(r)
    assert part1_protected_commitment(r, d)
    assert recoverable_verdict(r, d, c, q).startswith("no SE")
    # negative control: the same uniform assessment fails in G* itself
    assert not part1_late_commitment(r, d, c, q, True)
    assert part1_late_commitment(r, d, c, q, False)
    print("Part 1 (R=2, D=6, c=3, q=99/100):")
    print("  TR (commitment given, forced release): intended outcome is the unique SE outcome")
    print("  PC (protected commitment, omission allowed): omission strictly dominated; unique SE outcome")
    print("  LC-recoverable (late commitment turns, leaked material recoverable): = G*, "
          "no SE has the intended outcome")
    print("  LC-opaque (late commitment turns, material not recoverable before the answer): "
          "preserving SE exists")

    # ---- part 2 at G*'s parameters
    assert early_survives(r, q, F(0))
    early_bad_completion_rejected(r, q)
    for cp in (r + F(1, 100), 2 * r):
        assert early_strictly_dominated(r, cp)
        assert early_survives(r, q, cp)
    assert not early_strictly_dominated(r, r)  # the bound is strict
    g = r / 2
    assert not early_survives(r, q, F(0), g) and interim_necessity(r, q, F(0), g)
    assert early_survives(r, q, g, g) and not interim_necessity(r, q, g, g)
    assert not early_survives(r, q, g - F(1, 100), g) and interim_necessity(r, q, g - F(1, 100), g)
    assert early_strictly_dominated(r, r + g + F(1, 100), g)
    print("Part 2 (charged early-opening packet, c' charged whether or not included):")
    print("  G*: c' = 0 preserving SE exists (some consistent completions fail); "
          "c' > R: early opening strictly dominated, unique SE outcome")
    print(f"  interim control (g = {g}): intended outcome is an SE outcome iff g <= c'")

    # ---- part 3: parametric family
    print("Part 3 (R = 2):")
    print("  D    c    q          LC-opaque  LC-recoverable")
    qs = (F(1, 2), F(9, 10), F(99, 100), F(999, 1000), F(9999, 10000))
    tally = {}
    for dd, cc, qq in itertools.product((F(3), F(6), F(12)), (F(0), F(1), F(3), F(6)), qs):
        part1_timed_release(r)
        assert part1_protected_commitment(r, dd)
        opaque = part1_late_commitment(r, dd, cc, qq, False)
        assert opaque == opaque_construction_applies(r, dd, cc, qq), (dd, cc, qq)
        rec = recoverable_verdict(r, dd, cc, qq)
        tally[rec] = tally.get(rec, 0) + 1
        # part 2 for every point
        assert early_survives(r, qq, F(0))
        assert early_survives(r, qq, r + F(1, 100)) and early_strictly_dominated(r, r + F(1, 100))
        for gg in (r / 4, r):
            assert not early_survives(r, qq, F(0), gg)
            assert early_survives(r, qq, gg, gg)
            assert not early_survives(r, qq, gg - F(1, 100), gg)
            assert interim_necessity(r, qq, gg - F(1, 100), gg)
        print(f"  {str(dd):4} {str(cc):4} {str(qq):10} {'SE' if opaque else 'n/a':10} {rec}")
    print("  LC-recoverable tally:", tally)
    print("verdict: forced release removes the obstruction at the reveal; it returns if "
          "commitments have late turns whose leaked material is recoverable before the "
          "listener answers; a charged early opening is harmless in G* and deterred by c' > R "
          "in general")


if __name__ == "__main__":
    main()
