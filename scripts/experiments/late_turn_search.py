#!/usr/bin/env python3
"""Exact structured search for preserving sequential equilibria with several
sender types, several late turns and several listeners.

This is the richer search of plan section 16 for the problem stated in
docs/open-problem-late-turn-equilibria.md. Everything is exact rational
arithmetic and every reported equilibrium is re-checked by an independent
exact checker (consistency as limits of fully mixed polynomial families,
sequential rationality of every listener and every sender node, intended law
on path).

Model (one admissible configuration per design). Sender type t = (v, s) with
an independent prior. The opening of v is sent at the protected turn P (on
time) or at one of the late turns L1..Lk; a late opening is included before
expiry with probability q (content-blind coin). Listener l is activated once
between L_pos(l) and L_pos(l)+1 and then learns every pending opening, so it
knows v after a dropped opening sent at a turn j <= pos(l). Listener l answers
once after the reveal resolves, at one of: SP(v) (on path), S_j(v) (success at
L_j), Fk_l(v) (failure, v learned), Fu_l (failure, nothing learned). Listener
failure payoffs depend only on v (the leak matters), success payoffs on (v, s).
The sender gets a base utility summed over listeners, minus D on a failed
reveal, minus c if its late opening was dropped.

Structure of a candidate assessment. B sends at P on path; B's off-path
choices at each late node are the node-wise best replies (ties chosen by the
search); B's deferral and late trembles have one free coefficient per type and
node, so the limit belief at each success site S_j(v) can be any distribution
in the relative interior of its support (the types reaching it with the least
number of trembles); failure sites need only the probability of v, which is
free through the group coefficients. The search enumerates listener answers
per site (pure, or one two-answer mixture with a weight solved to make some
sender type indifferent), checks for each site that a common belief on its
support makes the chosen answers best replies, and checks sender rationality
and deterrence; a hit is then rebuilt as an explicit fully mixed family and
verified by the checker.

Designs and results (exact; each hit re-verified by `check`):
- E1: two types per v, two late turns, one listener (the D1 shape): a
  preserving SE with one small reward mixture at S1(1).
- E2: three types per v, three late turns, two listeners activated after L1
  and after L2, lopsided rewards (each guess rewards one type by 1/2 and hurts
  another by 1/10): a preserving SE with one mixture at q = 9/10 and with two
  small mixtures (weights 2/165 and 1/99 at S2(1)) at q = 99/100.
- G* (docs/open-problem-late-turn-equilibria.md): no preserving SE in the
  search space (up to two mixtures), consistent with the proof checked in
  g_star_verification.py. The search is not a proof of impossibility; it
  only finds equilibria of the structured form above.

Run: python scripts/experiments/late_turn_search.py
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass, field
from fractions import Fraction as F

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


def limit_belief(masses: dict) -> dict:
    nonzero = {k: m for k, m in masses.items() if m}
    assert nonzero, "an information set of a fully mixed family has positive mass"
    leads = {}
    for k, m in nonzero.items():
        e = min(m)
        assert m[e] > 0
        leads[k] = (e, m[e])
    e = min(x for x, _ in leads.values())
    weights = {k: (c if x == e else F(0)) for k, (x, c) in leads.items()}
    for k in masses:
        weights.setdefault(k, F(0))
    total = sum(weights.values())
    return {k: w / total for k, w in weights.items()}


# ------------------------------------------------------------------- designs


@dataclass
class Listener:
    name: str
    pos: int
    success: tuple[str, ...]
    a_success: dict  # answer -> (v, s) -> payoff
    b_success: dict  # answer -> (v, s) -> sender's payoff from this listener
    failure: tuple[str, ...]
    a_failure: dict  # answer -> v -> payoff
    b_failure: dict  # answer -> (v, s) -> sender's payoff
    intended: dict  # v -> intended success answer


@dataclass
class Design:
    name: str
    s_values: tuple[int, ...]
    p_v: F
    p_s: dict
    k: int
    listeners: list
    q: F
    d: F
    c: F

    @property
    def types(self):
        return [(v, s) for v in (0, 1) for s in self.s_values]

    def prior(self, t) -> F:
        v, s = t
        return (self.p_v if v else 1 - self.p_v) * self.p_s[s]

    def b_range(self) -> F:
        """Range of the sender's base utility over all answer profiles."""
        values = []
        for t in self.types:
            for outcome in ("success", "failure"):
                combos = itertools.product(*[
                    (lst.success if outcome == "success" else lst.failure) for lst in self.listeners])
                for combo in combos:
                    table = "b_success" if outcome == "success" else "b_failure"
                    values.append(sum(getattr(lst, table)[a][t]
                                      for lst, a in zip(self.listeners, combo)))
        return max(values) - min(values)


def best_set(answers, value_of) -> set:
    vals = {a: value_of(a) for a in answers}
    top = max(vals.values())
    return {a for a, x in vals.items() if x == top}


# ---------------------------------------------------------------- sender values


def site_value(design: Design, mixes: dict, t, key) -> F:
    """Sender's base value from all listeners' (mixed) answers at a site.
    key: ('S', j) success at L_j, ('F', j) failure after a send at L_j,
    ('N',) never sent."""
    v = t[0]
    total = F(0)
    for lst in design.listeners:
        if key[0] == "S":
            mix = mixes[(lst.name, "S", key[1], v)]
            total += sum(p * lst.b_success[a][t] for a, p in mix.items())
        else:
            learned = key[0] == "F" and key[1] <= lst.pos
            mix = mixes[(lst.name, "Fk", v)] if learned else mixes[(lst.name, "Fu")]
            total += sum(p * lst.b_failure[a][t] for a, p in mix.items())
    return total


def plan_values(design: Design, mixes: dict, t) -> dict:
    q, d, c = design.q, design.d, design.c
    out = {"P": sum(lst.b_success[lst.intended[t[0]]][t] for lst in design.listeners)}
    for j in range(1, design.k + 1):
        out[j] = q * site_value(design, mixes, t, ("S", j)) + (1 - q) * (
            site_value(design, mixes, t, ("F", j)) - d - c)
    out["never"] = site_value(design, mixes, t, ("N",)) - d
    return out


def node_choices(design: Design, vals: dict) -> tuple[dict, list]:
    """Continuation values and the set of best choices at each late node."""
    cont = {design.k + 1: vals["never"]}
    best = {}
    for j in range(design.k, 0, -1):
        send, hold = vals[j], cont[j + 1]
        cont[j] = max(send, hold)
        best[j] = {x for x, y in (("send", send), ("hold", hold)) if y == cont[j]}
    return cont, best


# ----------------------------------------------------------------- the checker


@dataclass
class Assessment:
    natural: dict  # type -> node -> 'send' | 'hold'
    wait: dict  # type -> (coef, exp)
    off: dict  # (type, node) -> (coef, exp) for the non-natural choice
    mixes: dict  # (listener, kind, ...) -> {answer: prob}


def masses(design: Design, a: Assessment) -> dict:
    out = {}
    for t in design.types:
        reach = pmul(pconst(design.prior(t)), poly(a.wait[t]))
        for j in range(1, design.k + 1):
            coef, exp = a.off[(t, j)]
            small = poly((coef, exp))
            big = poly((1, 0), (-coef, exp))
            send, hold = (big, small) if a.natural[t][j] == "send" else (small, big)
            out[(t, j)] = pmul(reach, send)
            reach = pmul(reach, hold)
        out[(t, "never")] = reach
    return out


def check(design: Design, a: Assessment) -> dict:
    """Exact check of a preserving native SE; returns the limit beliefs."""
    m = masses(design, a)
    q = design.q
    beliefs = {}
    for v in (0, 1):
        group = [t for t in design.types if t[0] == v]
        for j in range(1, design.k + 1):
            beliefs[("S", j, v)] = limit_belief({t: pmul(m[(t, j)], pconst(q)) for t in group})
        for lst in design.listeners:
            beliefs[(lst.name, "Fk", v)] = limit_belief({
                t: pmul(sum_poly([m[(t, j)] for j in range(1, lst.pos + 1)]), pconst(1 - q))
                for t in group})
    for lst in design.listeners:
        beliefs[(lst.name, "Fu")] = limit_belief({
            t: padd(pmul(sum_poly([m[(t, j)] for j in range(lst.pos + 1, design.k + 1)]),
                         pconst(1 - q)), m[(t, "never")])
            for t in design.types})
    # listeners
    for lst in design.listeners:
        for v in (0, 1):
            group = [t for t in design.types if t[0] == v]
            mu0 = {t: design.prior(t) for t in group}
            tot = sum(mu0.values())
            assert best_set(lst.success, lambda x: sum(mu0[t] * lst.a_success[x][t]
                                                       for t in group) / tot) == {lst.intended[v]}
            for j in range(1, design.k + 1):
                mu = beliefs[("S", j, v)]
                br = best_set(lst.success, lambda x: sum(mu[t] * lst.a_success[x][t] for t in group))
                mix = a.mixes[(lst.name, "S", j, v)]
                assert all(p == 0 or x in br for x, p in mix.items()), (lst.name, j, v, mu, mix)
            mu = beliefs[(lst.name, "Fk", v)]
            br = best_set(lst.failure, lambda x: lst.a_failure[x][v])
            mix = a.mixes[(lst.name, "Fk", v)]
            assert all(p == 0 or x in br for x, p in mix.items())
        mu = beliefs[(lst.name, "Fu")]
        br = best_set(lst.failure, lambda x: sum(w * lst.a_failure[x][t[0]] for t, w in mu.items()))
        mix = a.mixes[(lst.name, "Fu")]
        assert all(p == 0 or x in br for x, p in mix.items()), (lst.name, "Fu", mu, mix)
    # sender
    for t in design.types:
        vals = plan_values(design, a.mixes, t)
        cont, best = node_choices(design, vals)
        for j in range(1, design.k + 1):
            assert a.natural[t][j] in best[j], (t, j, vals)
        assert vals["P"] >= cont[1], (t, vals)
    return beliefs


def sum_poly(polys):
    out = {}
    for p in polys:
        out = padd(out, p)
    return out


# ------------------------------------------------------- belief feasibility


def feasible_belief(design: Design, v: int, support: list, constraints: list):
    """A belief in the relative interior of the face on `support` (types of
    group v) satisfying every constraint `lin . mu >= 0` (lin: type -> coef) and
    every equality given as two opposite constraints. Exact vertex
    enumeration in the face (dimension <= 2). Returns the belief or None."""
    n = len(support)
    if n == 1:
        mu = {support[0]: F(1)}
        return mu if all(sum(lin.get(t, F(0)) * w for t, w in mu.items()) >= 0
                         for lin in constraints) else None
    # coordinates: x_1..x_{n-1}, x_0 = 1 - sum
    def to_mu(x):
        mu = {support[i + 1]: x[i] for i in range(n - 1)}
        mu[support[0]] = 1 - sum(x)
        return mu

    halfspaces = []  # (a, b): a . x >= b
    for lin in constraints:
        c0 = lin.get(support[0], F(0))
        a_ = [lin.get(support[i + 1], F(0)) - c0 for i in range(n - 1)]
        halfspaces.append((a_, -c0))
    for i in range(n - 1):
        unit = [F(int(i == r)) for r in range(n - 1)]
        halfspaces.append((unit, F(0)))
    halfspaces.append(([F(-1)] * (n - 1), F(-1)))
    pts = []
    if n - 1 == 1:
        for a_, b in halfspaces:
            if a_[0] != 0:
                pts.append([b / a_[0]])
    else:
        for (a1, b1), (a2, b2) in itertools.combinations(halfspaces, 2):
            det = a1[0] * a2[1] - a1[1] * a2[0]
            if det != 0:
                pts.append([(b1 * a2[1] - b2 * a1[1]) / det, (a1[0] * b2 - a2[0] * b1) / det])
    feas = [x for x in pts if all(sum(ai * xi for ai, xi in zip(a_, x)) >= b for a_, b in halfspaces)]
    if not feas:
        return None
    uniq = []
    for x in feas:
        if x not in uniq:
            uniq.append(x)
    centre = [sum(x[i] for x in uniq) / len(uniq) for i in range(n - 1)]
    mu = to_mu(centre)
    if all(w > 0 for w in mu.values()):
        return mu
    return None


def site_constraints(lst: Listener, v: int, group: list, answers: dict) -> list:
    """Constraints making every answer in `answers` (support of the mix) a best
    reply of `lst` at success."""
    out = []
    for x in answers:
        for y in lst.success:
            out.append({t: lst.a_success[x][t] - lst.a_success[y][t] for t in group})
    return out


# -------------------------------------------------------------- the search


@dataclass
class SearchResult:
    assessment: Assessment
    beliefs: dict
    description: str


def supports(design: Design, natural: dict, v: int) -> dict:
    """Support of each success site S_j(v): types reaching it with the fewest
    non-natural choices (deferral at P is one for everyone)."""
    group = [t for t in design.types if t[0] == v]
    out = {}
    for j in range(1, design.k + 1):
        cost = {}
        for t in group:
            n = sum(1 for i in range(1, j) if natural[t][i] != "hold")
            n += 0 if natural[t][j] == "send" else 1
            cost[t] = n
        least = min(cost.values())
        out[j] = [t for t in group if cost[t] == least]
    return out


def build(design: Design, natural: dict, mixes: dict, site_beliefs: dict,
          fu_v: dict) -> Assessment:
    """Fully mixed family realizing the chosen site beliefs. One deferral
    exponent per value of v (fu_v picks which group dominates the failure
    sets); coefficients per type and node solve for the target beliefs."""
    wait, off = {}, {}
    for t in design.types:
        wait[t] = (F(1), 1 if t[0] == fu_v["dominant"] else design.k + 3)
        for j in range(1, design.k + 1):
            off[(t, j)] = (F(1), 1)
    # coefficients: walk sites in order and fix the coefficient of the first
    # non-natural choice on each support type's path that is not yet fixed.
    for v in (0, 1):
        sup = supports(design, natural, v)
        for j in range(1, design.k + 1):
            target = site_beliefs.get((v, j))
            if target is None:
                continue
            # current relative weights without the free coefficient
            free = {}
            for t in sup[j]:
                path = [(i, "hold") for i in range(1, j)] + [(j, "send")]
                nonnat = [i for i, ch in path if natural[t][i] != ch]
                free[t] = nonnat[-1] if nonnat else None
            weights = {}
            for t in sup[j]:
                w = design.prior(t) * wait[t][0]
                path = [(i, "hold") for i in range(1, j)] + [(j, "send")]
                for i, ch in path:
                    if natural[t][i] != ch and free[t] != i:
                        w *= off[(t, i)][0]
                weights[t] = w
            if any(f is None for f in free.values()):
                # natural path: adjust the deferral coefficient instead
                for t in sup[j]:
                    if free[t] is None:
                        wait[t] = (target[t] / weights[t] * wait[t][0], wait[t][1])
                continue
            for t in sup[j]:
                off[(t, free[t])] = (target[t] / weights[t], 1)
    return Assessment(natural, wait, off, mixes)


def search(design: Design, max_mix: int = 1, verbose: bool = False, per_group: int = 20):
    """Structured search; returns the first verified preserving SE or None."""
    lsts = design.listeners
    for fu_answers in itertools.product(*[lst.failure for lst in lsts]):
        for dominant in (0, 1):
            fu = {lst.name: a for lst, a in zip(lsts, fu_answers)}
            if not all(fu[lst.name] in best_set(lst.failure, lambda x: lst.a_failure[x][dominant])
                       for lst in lsts):
                continue
            base_mix = {}
            for lst in lsts:
                base_mix[(lst.name, "Fu")] = {fu[lst.name]: F(1)}
                for v in (0, 1):
                    fk = best_set(lst.failure, lambda x: lst.a_failure[x][v])
                    base_mix[(lst.name, "Fk", v)] = {sorted(fk)[0]: F(1)}
            hits = {v: list(itertools.islice(search_group(design, base_mix, v, max_mix), per_group))
                    for v in (0, 1)}
            if verbose:
                print(f"  Fu {fu_answers} dominant {dominant}: group hits "
                      f"{len(hits[0])}, {len(hits[1])}")
            for h0, h1 in itertools.product(hits[0], hits[1]):
                natural, mixes, site_beliefs = {}, dict(base_mix), {}
                for nat, mx, sb in (h0, h1):
                    natural.update(nat)
                    mixes.update(mx)
                    site_beliefs.update(sb)
                a = build(design, natural, mixes, site_beliefs, {"dominant": dominant})
                try:
                    beliefs = check(design, a)
                except AssertionError as failure:
                    if verbose:
                        print("  rejected by the checker:", failure)
                    continue
                return SearchResult(a, beliefs, f"Fu answers {fu_answers}, dominant v={dominant}")
    return None


def joint_tuples(design: Design, v: int, group: list) -> list:
    """Joint pure answer tuples (one per listener) that are best replies at a
    common belief in the relative interior of some support face."""
    out = []
    faces = [list(c) for n in range(1, len(group) + 1) for c in itertools.combinations(group, n)]
    for tup in itertools.product(*[lst.success for lst in design.listeners]):
        cons_all = []
        for lst, ans in zip(design.listeners, tup):
            cons_all += site_constraints(lst, v, group, [ans])
        if any(feasible_belief(design, v, face, cons_all) is not None for face in faces):
            out.append(tup)
    return out


def search_group(design: Design, base_mix: dict, v: int, max_mix: int):
    """Yield (natural, mixes, site beliefs) for group v."""
    lsts = design.listeners
    group = [t for t in design.types if t[0] == v]
    tuples = joint_tuples(design, v, group)
    site_keys = [(lst, j) for j in range(1, design.k + 1) for lst in lsts]
    sites = list(range(1, design.k + 1))
    for n_mix in range(0, max_mix + 1):
        for per_site in itertools.product(tuples, repeat=len(sites)):
            combo = [ans for tup in per_site for ans in tup]
            positions = list(itertools.combinations(range(len(site_keys)), n_mix))
            for pos in positions:
                alts = [[a for a in site_keys[i][0].success if a != combo[i]] for i in pos]
                for alt in itertools.product(*alts):
                    mixing = list(zip(pos, alt))
                    yield from try_profile(design, base_mix, v, group, site_keys, combo, mixing)


def affine_candidates(design, group, mixes_at, n):
    """Points in (0,1)^n where some type is indifferent between two plans
    (n <= 2 mixture weights); plan values are affine in the weights."""
    if n == 0:
        return [()]
    zero = tuple(F(0) for _ in range(n))
    basis = [tuple(F(int(i == r)) for r in range(n)) for i in range(n)]
    lines = []  # (coeffs, rhs): coeffs . p = rhs
    for t in group:
        v0 = plan_values(design, mixes_at(zero), t)
        vb = [plan_values(design, mixes_at(b), t) for b in basis]
        for a_, b_ in itertools.combinations(list(v0), 2):
            d0 = v0[a_] - v0[b_]
            coeffs = [vb[i][a_] - vb[i][b_] - d0 for i in range(n)]
            if any(x != 0 for x in coeffs):
                lines.append((coeffs, -d0))
    pts = set()
    if n == 1:
        for (a1,), b in lines:
            p = b / a1
            if 0 < p < 1:
                pts.add((p,))
    else:
        for (a1, b1), (a2, b2) in itertools.combinations(lines, 2):
            det = a1[0] * a2[1] - a1[1] * a2[0]
            if det != 0:
                p = ((b1 * a2[1] - b2 * a1[1]) / det, (a1[0] * b2 - a2[0] * b1) / det)
                if all(0 < x < 1 for x in p):
                    pts.add(p)
    return sorted(pts)


def try_profile(design, base_mix, v, group, site_keys, combo, mixing):
    """Yield the assessments of group v for one answer profile; `mixing` lists
    (site index, alternative answer); the weights are solved so that sender
    types become indifferent between plans."""
    def mixes_at(p):
        mx = dict(base_mix)
        weight = {idx: (alt, w) for (idx, alt), w in zip(mixing, p)}
        for idx, ((lst, j), ans) in enumerate(zip(site_keys, combo)):
            if idx in weight:
                alt, w = weight[idx]
                mx[(lst.name, "S", j, v)] = {ans: 1 - w, alt: w}
            else:
                mx[(lst.name, "S", j, v)] = {ans: F(1)}
        return mx

    for p in affine_candidates(design, group, mixes_at, len(mixing)):
        mx = mixes_at(p)
        natural, tie_nodes, ok = {}, [], True
        for t in group:
            vals = plan_values(design, mx, t)
            cont, best = node_choices(design, vals)
            if vals["P"] < cont[1]:
                ok = False
                break
            natural[t] = {j: ("send" if "send" in best[j] else "hold") for j in best}
            tie_nodes += [(t, j) for j, b in best.items() if len(b) == 2]
        if not ok:
            continue
        for choice in itertools.product(("send", "hold"), repeat=len(tie_nodes)):
            nat = {t: dict(natural[t]) for t in group}
            for (t, j), ch in zip(tie_nodes, choice):
                nat[t][j] = ch
            beliefs = beliefs_for(design, v, group, nat, site_keys, mx)
            if beliefs is not None:
                own = {k: val for k, val in mx.items() if len(k) == 4 and k[1] == "S" and k[3] == v}
                yield nat, own, beliefs


def beliefs_for(design, v, group, natural, site_keys, mx):
    sup = supports(design, natural, v)
    out = {}
    for j in range(1, design.k + 1):
        cons = []
        for lst, jj in site_keys:
            if jj != j:
                continue
            mix = mx[(lst.name, "S", j, v)]
            cons += site_constraints(lst, v, group, [a for a, w in mix.items() if w > 0])
        mu = feasible_belief(design, v, sup[j], cons)
        if mu is None:
            return None
        out[(v, j)] = mu
    return out


# -------------------------------------------------------------------- designs


def guess_listener(name, pos, s_values, m_value, b_success, a_fail_v=True, intended="m"):
    succ = ("m",) + tuple(f"x{s}" for s in s_values)
    a_s = {"m": {(v, s): m_value for v in (0, 1) for s in s_values}}
    for s0 in s_values:
        a_s[f"x{s0}"] = {(v, s): F(int(s == s0)) for v in (0, 1) for s in s_values}
    fail = ("0", "1")
    a_f = {"0": {0: F(1), 1: F(0)}, "1": {0: F(0), 1: F(1)}}
    return Listener(name, pos, succ, a_s, b_success, fail, a_f, None, {0: intended, 1: intended})


def design_e1(q, d, c) -> Design:
    """Two types per v, two late turns, one listener (the D1 shape)."""
    s_values = (0, 1)
    lst = guess_listener("A", 1, s_values, F(3, 5), None)
    lst.b_success = {"m": {t: F(0) for t in itertools.product((0, 1), s_values)},
                     "x0": {t: F(int(t[1] == 0)) for t in itertools.product((0, 1), s_values)},
                     "x1": {t: F(int(t[1] == 1)) for t in itertools.product((0, 1), s_values)}}
    lst.b_failure = {"0": {t: F(int(t[1] == 0)) for t in itertools.product((0, 1), s_values)},
                     "1": {t: F(int(t[1] == 1)) for t in itertools.product((0, 1), s_values)}}
    return Design("E1", s_values, F(9, 20), {0: F(11, 20), 1: F(9, 20)}, 2, [lst], q, d, c)


def design_e2(q, d, c, eps=F(1, 10)) -> Design:
    """Three types per v, three late turns, two listeners activated after L1
    and after L2. Listener answers x_s reward type s+1 fully and hurt type s
    slightly (lopsided); the intended answer m is a best reply only at
    interior beliefs (max probability <= 2/5). Failure answers: [a = v] for the
    listener; the sender's failure value depends on s and the answer, so the
    two leak points make the three types prefer different late turns."""
    s_values = (0, 1, 2)
    types = list(itertools.product((0, 1), s_values))
    lsts = []
    for name, pos in (("A1", 1), ("A2", 2)):
        lst = guess_listener(name, pos, s_values, F(2, 5), None)
        b_s = {"m": {t: F(0) for t in types}}
        for s0 in s_values:
            b_s[f"x{s0}"] = {t: (F(1, 2) if t[1] == (s0 + 1) % 3 else (-eps if t[1] == s0 else F(0)))
                            for t in types}
        lst.b_success = b_s
        # sender's failure value: answer a = v is good for s = pos - 1 and bad
        # for s = pos, so a leak at this listener separates those two types
        lst.b_failure = {a: {t: (F(1, 2) if (int(a) == t[0]) == (t[1] == pos - 1) else F(0))
                             for t in types} for a in ("0", "1")}
        lsts.append(lst)
    p_s = {0: F(1, 3), 1: F(1, 3), 2: F(1, 3)}
    return Design("E2", s_values, F(9, 20), p_s, 3, lsts, q, d, c)


def design_gstar(q, d, c) -> Design:
    """The three-type counterexample G* (s in A, B, C as 0, 1, 2; R = 2)."""
    s_values = (0, 1, 2)
    types = list(itertools.product((0, 1), s_values))
    r = F(2)
    lst = guess_listener("A", 1, s_values, F(2, 5), None)
    b_s = {"m": {t: r / 2 for t in types}}
    for s0 in s_values:
        b_s[f"x{s0}"] = {t: (r if t[1] in (0, 1) else F(0)) for t in types}
    lst.b_success = b_s
    lst.b_failure = {"1": {t: (r if t[1] == 0 else F(0)) for t in types},
                     "0": {t: (r if t[1] == 1 else F(0)) for t in types}}
    return Design("G*", s_values, F(9, 20), {0: F(1, 3), 1: F(1, 3), 2: F(1, 3)}, 2, [lst],
                  q, d, c)


def main_gstar() -> None:
    gstar = design_gstar(F(99, 100), F(6), F(3))
    assert gstar.b_range() == 2
    for mix in (0, 1, 2):
        assert search(gstar, max_mix=mix) is None
    print("G* (q=99/100, D=6, c=3): no preserving SE found by the structured search "
          "(consistent with the proof in g_star_verification.py)")


def main() -> None:
    main_gstar()
    for maker in (design_e1, design_e2):
        for q in (F(9, 10), F(99, 100)):
            probe = maker(q, F(1), F(1))
            r = probe.b_range()
            design = maker(q, 3 * r, r + F(1, 2))
            assert design.d >= 3 * r and design.c > r
            hit = search(design, max_mix=1)
            if hit is None:
                hit = search(design, max_mix=2)
            if hit is None:
                print(f"{design.name} q={q} R={r}: no preserving SE found by the structured search")
            else:
                mixes = {k: v for k, v in hit.assessment.mixes.items() if len(v) > 1}
                print(f"{design.name} q={q} R={r}: preserving SE ({hit.description}); "
                      f"mixed answers {mixes}")


if __name__ == "__main__":
    main()
