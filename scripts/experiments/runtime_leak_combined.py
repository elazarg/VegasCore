#!/usr/bin/env python3
"""Exact test: does the late-leak obstruction survive as a whole, with a valid
stateless leak rule and every non-restoring runtime feature at once?

Background: docs/runtime-features-vs-late-leak.md (feature by feature, mostly
with G*'s selective leak) and docs/open-problem-late-turn-equilibria.md (G*).
G*'s selective leak is not a stateless observation rule. This script replaces
it by a valid rule and combines all features that did not restore
preservation one by one. Summary: docs/runtime-features-vs-late-leak.md,
section "Combined, with a valid leak rule".

Runtime model (one late slot, deadline 2, reaction delay 0, inclusion bound 1;
the settle-late builder T2 of runtime_features_late_leak.py):
  clock 0: sender B activated at P (protected), protected inclusion step;
  clock 1: B activated at L1; the listener A is activated k times
  (observe-only: its answer event is not ready); B activated at L2; one
  inclusion step for all late packets (Luce law forced by blindness);
  clock 2: the reveal expires; A is activated and answers.
Leak rule (a kernel of the observer and the pending pool only): at every
activation of A, each pending authentic-looking opening of B is seen
independently with probability lam; every other pending packet (B's raw
signals) is seen surely; B sees A's pending packets surely. A dropped opening
stays pending, so a dropped L2 opening is exposed once (at the answer), an
L1 opening k times before L2 and once more at the answer if it was dropped.
Features, all at once: the blind retry (second opening at L2), raw signals at
P, at L1 (after P too) and at L2, charged by the capped escrow (one charge c
per owner, so a signal after a certain charge is free), the listener's raw
packets at every observe-only activation (owner-only inclusion, cost c_L once),
and the contract constraints (`contract_checks_k`).

Method (exact fractions, every claim an assert):
- the reduction certificate, extended (`certificate`): (P1) every extra sender
  option in the subtree after a silent deferral is strictly worse than a fixed
  core continuation at every member of its information set for every listener
  behaviour; (P2) opening at L2 beats never; (P3) the L1-minus-L2 gap is, as a
  polynomial identity in the listener's whole behaviour (mid packets and
  answers, free simplex coordinates), d-direction plus kappa times e-direction
  with kappa_1 + kappa_0 = (1-q) alpha (1-lam) R, alpha = 1 - (1-lam)^k, and
  kappa_1 = K(1 - theta), kappa_0 = K theta for the averaged answer theta at
  the uninformative failure; (P4) every path of every type to a success site
  where the L1 opening was seen before L2 passes the silent deferral and the
  L1 opening, the sites are disjoint from the L2 success sites, and the
  listener has perfect recall (so message factors cancel in belief ratios);
  (P5) the deviations on a face pay.  With the G* case lemma this gives the
  four steps of the G* argument for every listener behaviour.
- the exact leak boundary: with a face forced at the L1-seen success sites the
  best escape is a choice of theta; the escape value is checked exactly and an
  explicit SE is constructed (and Kreps-Wilson verified) at the boundary side
  where it exists.
- negative controls: the certificate fails where an SE is constructed
  (k too small, lam = 1), and hidden signals break premise P4.

Run: python scripts/experiments/runtime_leak_combined.py
"""

from __future__ import annotations

import itertools
import random
import sys
from dataclasses import dataclass, replace
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import runtime_features_late_leak as rf  # noqa: E402
from timed_release_probe import limit_belief  # noqa: E402

TYPES, S_LABELS = rf.TYPES, rf.S_LABELS
SUCCESS, FAILURE = rf.SUCCESS, rf.FAILURE
GUESSES = ("gA", "gB", "gC")


@dataclass(frozen=True)
class Combo:
    r: F = F(2)
    d: F = F(6)
    c: F = F(3)
    q: F = F(99, 100)
    lam: F = F(1, 2)
    k: int = 1
    retry: bool = True
    signals: bool = True
    alphabet: int = 2
    listener: bool = True
    lp_seen: bool = True  # the rule shows A's pending packets to B
    sig_seen: bool = True  # the rule shows B's raw signals to A
    c_l: F = F(1, 10)

    def deferral_pays(self) -> bool:
        return rf.Cfg(r=self.r, d=self.d, c=self.c, q=self.q).deferral_pays()

    def alpha(self) -> F:
        """Probability that a pending L1 opening is seen before L2."""
        return 1 - (1 - self.lam) ** self.k

    def a_known(self) -> F:
        """Probability that v is known after a dropped L1 opening."""
        al = self.alpha()
        return al + (1 - al) * self.lam


def own_label(e) -> str:
    act, kind, x = e
    return f"{act}:{kind}" + ("" if kind == "open" else str(x))


def hist_str(hist) -> str:
    return ";".join(f"{o}/{a}" if a else o for o, a in hist) or "start"


class ComboBuilder:
    """Per-type trees in the format of runtime_features_late_leak.Builder."""

    def __init__(self, cfg: Combo):
        self.cfg = cfg
        self.w = cfg.q / (1 - cfg.q)

    def trees(self) -> dict:
        return {t: self.root(t) for t in TYPES}

    def sig_actions(self):
        return [f"sig{x}" for x in range(self.cfg.alphabet)] if self.cfg.signals else []

    def root(self, t):
        acts = {"open": self.p_success(t), "wait": self.l1(t, ())}
        for x, a in enumerate(self.sig_actions()):
            acts[a] = self.l1(t, (("P", "sig", x),))
        return ("S", ("P",), acts)

    def p_success(self, t):
        """Protected opening included at clock 0; the reveal is complete, so A
        answers at its first activation, after B's L1 activation (a raw
        signal there is charged and, under the rule, seen)."""
        if not self.cfg.signals:
            return self.answer_p(t, None)
        acts = {"wait": self.answer_p(t, None)}
        for x, a in enumerate(self.sig_actions()):
            acts[a] = self.answer_p(t, x)
        return ("S", ("L1", "after P"), acts)

    def answer_p(self, t, x):
        cfg = self.cfg
        shown = x is not None and cfg.sig_seen
        key = f"ans|P|v={t[0]}" + (f"|L1:sig{x}" if shown else "")
        pen = F(0) if x is None else cfg.c
        label = "P" if x is None else "P+sig"
        return ("L", key, {a: ("T", (label, a), rf.sender_base(a, t, cfg.r) - pen, rf.listener_u(a, t))
                           for a in SUCCESS})

    def l1(self, t, em):
        v = t[0]
        acts = {"open": self.mid(t, em + (("L1", "open", v),), 1, (), False, ()),
                "wait": self.mid(t, em, 1, (), False, ())}
        for x, a in enumerate(self.sig_actions()):
            acts[a] = self.mid(t, em + (("L1", "sig", x),), 1, (), False, ())
        return ("S", ("L1", tuple(own_label(e) for e in em)), acts)

    def mid(self, t, em, i, hist, seen, lpk):
        """Observe-only activation i of A (1 <= i <= k)."""
        cfg = self.cfg
        if i > cfg.k:
            return self.l2(t, {"em": em, "hist": hist, "seen": seen, "lpk": lpk})
        opened = any(k == "open" for _, k, _ in em)
        new_sigs = ([own_label(e) for e in em if e[1] == "sig"] if (i == 1 and cfg.sig_seen) else [])

        def after(saw):
            obs = ",".join(new_sigs + ([f"open{t[0]}"] if saw else [])) or "-"
            seen2 = seen or saw
            if cfg.listener:
                key = f"mid{i}|{hist_str(hist)}|{obs}"
                return ("L", key, {a: self.mid(t, em, i + 1, hist + ((obs, a),), seen2, lpk + (a,))
                                   for a in ("quiet", "pkt")})
            return self.mid(t, em, i + 1, hist + ((obs, None),), seen2, lpk)

        if opened and not seen:
            if cfg.lam == 1:
                return after(True)
            return ("C", [(cfg.lam, after(True)), (1 - cfg.lam, after(False))])
        return after(False)

    def l2(self, t, st):
        cfg = self.cfg
        em, v = st["em"], t[0]
        opened = any(k == "open" for _, k, _ in em)
        seen_lp = tuple(st["lpk"]) if (cfg.listener and cfg.lp_seen) else None
        key = ("L2", tuple(own_label(e) for e in em), seen_lp)
        if opened:
            acts = {"wait": self.end(t, st)}
            if cfg.retry:
                acts["retry"] = self.end(t, dict(st, em=em + (("L2", "open", v),)))
        else:
            acts = {"open": self.end(t, dict(st, em=em + (("L2", "open", v),))),
                    "wait": self.end(t, st)}
        for x, a in enumerate(self.sig_actions()):
            acts[a] = self.end(t, dict(st, em=em + (("L2", "sig", x),)))
        return ("S", key, acts)

    def end(self, t, st):
        """The one late inclusion step (T2): Luce law over the fresh openings."""
        fresh = [i for i, (_, k, _) in enumerate(st["em"]) if k == "open"]
        if not fresh:
            return self.answer(t, st, None)
        tot = 1 + len(fresh) * self.w
        out = [(self.w / tot, self.answer(t, st, i)) for i in fresh]
        out.append((1 / tot, self.answer(t, st, None)))
        return ("C", out)

    def answer(self, t, st, inc):
        cfg = self.cfg
        v = t[0]
        em = st["em"]
        success = inc is not None
        dropped = [i for i, (_, k, _) in enumerate(em) if k == "open" and i != inc]
        charged = any(k == "sig" for _, k, _ in em) or bool(dropped)
        new_sigs = [own_label(e) for e in em if e[1] == "sig" and e[0] == "L2"] if cfg.sig_seen else []
        # pending openings A has not seen yet: each seen with probability lam now
        fresh_view = [i for i in dropped if not (em[i][0] == "L1" and st["seen"])]
        res = f"ok:{inc}" if success else "fail"
        lpen = cfg.c_l if "pkt" in st["lpk"] else F(0)

        def node(seen_now):
            known = success or st["seen"] or bool(seen_now)
            parts = [f"h={hist_str(st['hist'])}", f"res={res}"]
            if seen_now:
                parts.append("late=" + ",".join(map(str, seen_now)))
            if new_sigs:
                parts.append("sig=" + ",".join(new_sigs))
            if known:
                parts.append(f"v={v}")
            menu = SUCCESS if success else FAILURE
            pen = (F(0) if success else cfg.d) + (cfg.c if charged else F(0))
            return ("L", "ans|" + "|".join(parts),
                    {a: ("T", ("late", a), rf.sender_base(a, t, cfg.r) - pen, rf.listener_u(a, t) - lpen)
                     for a in menu})

        if not fresh_view:
            return node(())
        if cfg.lam == 1:
            return node(tuple(fresh_view))
        out = []
        for mask in itertools.product((True, False), repeat=len(fresh_view)):
            p = F(1)
            for b in mask:
                p *= cfg.lam if b else 1 - cfg.lam
            out.append((p, node(tuple(i for i, b in zip(fresh_view, mask) if b))))
        return ("C", out)


class TreeGame:
    """The engine interface of runtime_features_late_leak.Game for given trees."""

    def __init__(self, cfg: Combo):
        self.cfg = cfg
        self.trees = ComboBuilder(cfg).trees()
        self.members: dict = {}
        for t, root in self.trees.items():
            for path, node in rf.iter_nodes(root):
                if node[0] in ("S", "L"):
                    self.members.setdefault(rf.iset_of(t, node), []).append((t, path, node))
        self.actions = {}
        for iset, mem in self.members.items():
            acts = tuple(mem[0][2][2])
            assert all(set(m[2][2]) == set(acts) for m in mem), iset
            self.actions[iset] = acts


# ------------------------------------------------- multivariate polynomials


def mp(*terms) -> dict:
    out: dict = {}
    for coef, mono in terms:
        mono = tuple(sorted(mono))
        out[mono] = out.get(mono, F(0)) + F(coef)
    return {m: c for m, c in out.items() if c != 0}


def mp_add(*ps) -> dict:
    return mp(*[(c, m) for p in ps for m, c in p.items()])


def mp_mul(p, q) -> dict:
    return mp(*[(cp * cq, mp_ + mq) for mp_, cp in p.items() for mq, cq in q.items()])


def mp_scale(p, s) -> dict:
    return mp(*[(c * s, m) for m, c in p.items()])


def coord(key, acts, a, pinned) -> dict:
    """Probability of action a at listener set `key` in free simplex
    coordinates: the first action is 1 minus the others."""
    if key in pinned:
        return mp((1, ())) if a == pinned[key] else {}
    if a != acts[0]:
        return mp((1, ((key, a),)))
    return mp((1, ()), *[(-1, ((key, b),)) for b in acts[1:]])


def plan_poly(node, rule, pinned) -> dict:
    k = node[0]
    if k == "T":
        return mp((node[2], ()))
    if k == "C":
        return mp_add(*[mp_scale(plan_poly(ch, rule, pinned), p) for p, ch in node[1]])
    if k == "S":
        return plan_poly(node[2][rule(node[1])], rule, pinned)
    acts = tuple(node[2])
    return mp_add(*[mp_mul(coord(node[1], acts, a, pinned), plan_poly(ch, rule, pinned))
                    for a, ch in node[2].items()])


def f1_weight_poly(node, rule, pinned) -> dict:
    """Probability, along `rule`, of reaching a failure site where v is
    unknown and the listener answers f1."""
    k = node[0]
    if k == "T":
        return {}
    if k == "C":
        return mp_add(*[mp_scale(f1_weight_poly(ch, rule, pinned), p) for p, ch in node[1]])
    if k == "S":
        return f1_weight_poly(node[2][rule(node[1])], rule, pinned)
    acts = tuple(node[2])
    if acts == FAILURE and "v=" not in node[1]:
        return coord(node[1], acts, "f1", pinned)
    return mp_add(*[mp_mul(coord(node[1], acts, a, pinned), f1_weight_poly(ch, rule, pinned))
                    for a, ch in node[2].items()])


# ---------------------------------------------------------- the certificate


def core_rule(name):
    return rf.core_plan(name)


def lb_rule(node, rule, pinned, forced=None):
    """Sender follows `rule`; the listener minimizes, per node (information
    sets relaxed: a sound lower bound); `forced` restricts some sites."""
    forced = forced or {}
    k = node[0]
    if k == "T":
        return node[2]
    if k == "C":
        return sum(p * lb_rule(ch, rule, pinned, forced) for p, ch in node[1])
    if k == "S":
        return lb_rule(node[2][rule(node[1])], rule, pinned, forced)
    if node[1] in pinned:
        acts = [pinned[node[1]]]
    else:
        acts = forced.get(node[1], list(node[2]))
    return min(lb_rule(node[2][a], rule, pinned, forced) for a in acts)


def continuation_rule(key):
    """Fixed core continuation below an L1 or L2 decision: open at L2 if not
    yet opened, otherwise wait."""
    if key[0] == "L2":
        return "wait" if any(x.endswith(":open") for x in key[1]) else "open"
    raise AssertionError(key)


def silent_sender_isets(game):
    """Sender information sets below the silent deferral (key starts L1 or L2,
    no own extra before)."""
    out = {}
    for iset, mem in game.members.items():
        if iset[0] != "S":
            continue
        key = iset[2]
        if key[0] == "L1" and key[1] == ():
            out[iset] = mem
        if key[0] == "L2" and key[1] in ((), ("L1:open",)):
            out[iset] = mem
    return out


def answer_tables(node, acc, prob=F(1)):
    """For a subtree without sender or mid decisions: site -> action ->
    expected sender payoff contribution (probability times payoff)."""
    k = node[0]
    if k == "C":
        for p, ch in node[1]:
            answer_tables(ch, acc, prob * p)
    elif k == "L":
        assert all(ch[0] == "T" for ch in node[2].values()), node[1]
        tab = acc.setdefault(node[1], {a: F(0) for a in node[2]})
        for a, ch in node[2].items():
            tab[a] += prob * ch[2]
    else:
        raise AssertionError("sender decision below an L2 node")
    return acc


def exact_affine_margin(better, worse, pinned) -> F:
    """min over every listener behaviour of V(better) - V(worse) when both
    subtrees contain only nature and answer sites (shared sites coupled):
    the difference is affine across sites, so the minimum is the sum over
    sites of the smallest per-action difference."""
    tb, tw = answer_tables(better, {}), answer_tables(worse, {})
    total = F(0)
    for site in set(tb) | set(tw):
        acts = list((tb.get(site) or tw.get(site)).keys())
        if site in pinned:
            acts = [pinned[site]]
        total += min(tb.get(site, {}).get(a, F(0)) - tw.get(site, {}).get(a, F(0)) for a in acts)
    return total


def p1_extras_dominated(game) -> list:
    """Every extra option (retry, signals) at every silent-subtree sender set
    is strictly worse than some core action, at every member, for every
    listener behaviour (separate bounds when the sites are disjoint, the
    exact coupled minimum at L2, where only answers remain). Returns the
    failures."""
    pinned = rf.pinned_answers(game)
    fails = []
    for iset, mem in silent_sender_isets(game).items():
        key = iset[2]
        for a in game.actions[iset]:
            if a in ("open", "wait"):
                continue
            ok = False
            for b in ("open", "wait"):
                if b not in game.actions[iset]:
                    continue
                if all(rf.ub(node[2][a], pinned) < lb_rule(node[2][b], continuation_rule, pinned)
                       for _, _, node in mem):
                    ok = True
                    break
                if key[0] == "L2" and all(exact_affine_margin(node[2][b], node[2][a], pinned) > 0
                                          for _, _, node in mem):
                    ok = True
                    break
            if not ok:
                fails.append((iset, a))
    return fails


def p2_send_beats_never(game) -> None:
    pinned = rf.pinned_answers(game)
    n = 0
    for iset, mem in silent_sender_isets(game).items():
        if iset[2][0] == "L2" and iset[2][1] == ():
            for _, _, node in mem:
                assert rf.ub(node[2]["wait"], pinned) < lb_rule(node[2]["open"], continuation_rule, pinned)
                n += 1
    assert n > 0


def p3_gap_identity(game) -> int:
    """Polynomial identity in the listener's whole behaviour."""
    cfg = game.cfg
    pinned = rf.pinned_answers(game)
    big_k = (1 - cfg.q) * cfg.alpha() * (1 - cfg.lam) * cfg.r
    thetas = []
    gaps = {}
    for t in TYPES:
        root = game.trees[t]
        l1 = plan_poly(root, core_rule("L1"), pinned)
        l2 = plan_poly(root, core_rule("L2"), pinned)
        gaps[t] = mp_add(l1, mp_scale(l2, -1))
        thetas.append(mp_scale(f1_weight_poly(root, core_rule("L2"), pinned),
                               1 / ((1 - cfg.q) * (1 - cfg.lam))))
    theta = thetas[0]
    assert all(th == theta for th in thetas), "the uninformative failure is shared"
    one = mp((1, ()))
    for v in (0, 1):
        ga, gb, gc = (gaps[(v, s)] for s in S_LABELS)
        # one reward direction: C's gap is minus the mean of A's and B's
        assert mp_add(gc, mp_scale(mp_add(ga, gb), F(1, 2))) == {}
        kappa = mp_scale(mp_add(ga, mp_scale(gb, -1)), F(1, 2) if v == 1 else F(-1, 2))
        want = mp_scale(mp_add(one, mp_scale(theta, -1)), big_k) if v == 1 else mp_scale(theta, big_k)
        assert kappa == want, v
    assert big_k > 0
    return sum(len(g) for g in gaps.values())


def reach_sites(node, rule, acc, path_tag=None):
    """Answer sites reached by `rule` for some listener behaviour and nature."""
    k = node[0]
    if k == "C":
        for _, ch in node[1]:
            reach_sites(ch, rule, acc)
    elif k == "S":
        reach_sites(node[2][rule(node[1])], rule, acc)
    elif k == "L":
        if all(ch[0] == "T" for ch in node[2].values()):
            acc.add(node[1])
        else:
            for ch in node[2].values():
                reach_sites(ch, rule, acc)
    return acc


def site_families(game):
    """S1s(v): success sites of the L1 plan where the opening was seen before
    L2; Sm(v): success sites of the L2 plan."""
    s1s, sm = {}, {}
    for v in (0, 1):
        t = (v, "A")
        l1 = reach_sites(game.trees[t], core_rule("L1"), set())
        l2 = reach_sites(game.trees[t], core_rule("L2"), set())
        succ1 = {k for k in l1 if "res=ok" in k}
        s1s[v] = {k for k in succ1 if f"open{v}" in k.split("|res=")[0]}
        sm[v] = {k for k in l2 if "res=ok" in k}
        assert s1s[v] and sm[v] and not (s1s[v] & sm[v])
        assert succ1 - s1s[v] <= sm[v], "an unseen L1 success shares the L2 site"
        for s in S_LABELS:  # the families do not depend on s
            assert reach_sites(game.trees[(v, s)], core_rule("L1"), set()) == l1
            assert reach_sites(game.trees[(v, s)], core_rule("L2"), set()) == l2
    return s1s, sm


def p4_structure(game, s1s, sm) -> bool:
    """Every path of every type to an S1s site passes the silent deferral and
    the L1 opening; listener sites record the listener's own history (perfect
    recall), so message factors are common to all types at a site."""
    targets = set().union(*s1s.values())
    ok = True

    def go(node, p_act, l1_act):
        nonlocal ok
        k = node[0]
        if k == "T":
            return
        if k == "C":
            for _, ch in node[1]:
                go(ch, p_act, l1_act)
            return
        if k == "L":
            if node[1] in targets and (p_act, l1_act) != ("wait", "open"):
                ok = False
            for ch in node[2].values():
                go(ch, p_act, l1_act)
            return
        key = node[1]
        for a, ch in node[2].items():
            if key == ("P",):
                go(ch, a, l1_act)
            elif key[0] == "L1" and key[1] != "after P":
                go(ch, p_act, a)
            else:
                go(ch, p_act, l1_act)

    for t in TYPES:
        go(game.trees[t], None, None)
    # perfect recall of A: every site key carries the full mid history
    for iset, mem in game.members.items():
        if iset[0] == "L" and iset[1].startswith("ans|h="):
            assert all(m[2][1] == iset[1] for m in mem)
    return ok


def deviation_values(game, s1s, sm):
    """P5. Face at S1s(v): the listener guesses there; the better of (v, A),
    (v, B) (the one f(v) rewards) deviates to the L1 plan. Face at Sm(v):
    (v, A) deviates to the L2 plan. Lower bounds over every other listener
    behaviour."""
    pinned = rf.pinned_answers(game)
    out = {}
    for v in (0, 1):
        better = (v, "A") if v == 1 else (v, "B")
        f1 = {k: list(GUESSES) for k in s1s[v]}
        out[("S1s", v)] = lb_rule(game.trees[better], core_rule("L1"), pinned, f1)
        fm = {k: list(GUESSES) for k in sm[v]}
        out[("Sm", v)] = lb_rule(game.trees[(v, "A")], core_rule("L2"), pinned, fm)
    return out


def dev_formula(cfg: Combo, w: F) -> F:
    """L1-plan value of a type guessed at every S1s site, answered m at every
    Sm site, with failure weight w (the probability of a failure answer that
    gives it R)."""
    q, r, al = cfg.q, cfg.r, cfg.alpha()
    return q * (al * r + (1 - al) * r / 2) + (1 - q) * r * w - (1 - q) * (cfg.d + cfg.c)


def escape_weight(cfg: Combo) -> F:
    """Smallest worst failure weight the listener can achieve when every class
    with kappa_v > 0 has its face at S1s (theta = averaged f1 at the
    uninformative failure): min over theta of max over face classes of the
    better of A, B. With a = P(v known | L1 drop), b = 1 - a:
    theta in (0,1): both classes, a + b max(theta, 1-theta) >= a + b/2;
    theta = 0 or 1: one class, max(a, b)."""
    a = cfg.a_known()
    b = 1 - a
    assert a + b == 1
    return min(max(a, b), a + b / 2)


def escape_weight_check(cfg: Combo) -> None:
    """The closed form against an exact scan of theta's breakpoints."""
    a = cfg.a_known()
    b = 1 - a
    best = None
    for theta in [F(0), F(1)] + [F(i, 64) for i in range(1, 64)]:
        if theta == 0:  # kappa_0 = 0: only class 1 needs a face
            w = max(a, b)
        elif theta == 1:
            w = max(a, b)
        else:
            w = max(a + b * theta, b * (1 - theta), a + b * (1 - theta), b * theta)
        best = w if best is None else min(best, w)
    assert best == escape_weight(cfg)


def certificate(cfg: Combo, game=None) -> dict:
    """All premises; returns a dict of results. `no_se` is True iff the
    extended G* argument applies (no SE with the intended outcome)."""
    game = game or TreeGame(cfg)
    out = {"deferral_pays": cfg.deferral_pays()}
    out["p1_fails"] = p1_extras_dominated(game)
    p2_send_beats_never(game)
    out["p3_terms"] = p3_gap_identity(game) if cfg.lam < 1 else None
    s1s, sm = site_families(game)
    out["p4"] = p4_structure(game, s1s, sm)
    dev = deviation_values(game, s1s, sm)
    out["dev"] = dev
    half = cfg.r / 2
    # the tree lower bounds equal the closed form with the worst failure weight
    for v in (0, 1):
        assert dev[("S1s", v)] == dev_formula(cfg, cfg.a_known())
        assert dev[("Sm", v)] > half  # G* hypothesis (face at Sm always pays)
    w_star = escape_weight(cfg)
    escape_weight_check(cfg)
    out["escape_value"] = dev_formula(cfg, w_star)
    out["no_se"] = (out["deferral_pays"] and not out["p1_fails"] and out["p4"]
                    and cfg.lam < 1 and out["escape_value"] > half)
    return out


# ------------------------------------------------- face dichotomy (sampled)


def face_dichotomy_samples(game, s1s, sm, n=30, seed=7) -> int:
    """Illustration of step 3 under arbitrary tilts: with t1 opening at L1 and
    t0 holding (both after the silent deferral; extras and everything else
    trembled with random type/node rates), either t0 is absent from every
    S1s(v) site or t1 is absent from every Sm(v) site."""
    rng = random.Random(seed)
    hits = 0
    for _ in range(n):
        v = rng.choice((0, 1))
        t1, t0 = rng.sample([(v, s) for s in S_LABELS], 2)
        beh, trem = {}, {}
        for iset, acts in game.actions.items():
            if iset[0] == "S":
                t, key = iset[1], iset[2]
                if key == ("P",):
                    a = "open"
                elif key[0] == "L1" and key[1] == ():
                    a = "open" if t == t1 else "wait"
                elif key[0] == "L2":
                    a = continuation_rule(key) if key[1] in ((), ("L1:open",)) else "wait"
                    a = a if a in acts else acts[0]
                else:
                    a = "wait" if "wait" in acts else acts[0]
            else:
                a = acts[0] if rng.random() < 0.7 else rng.choice(acts)
            beh[iset] = {a: F(1)}
            for b in acts:
                if b != a:
                    trem[(iset, b)] = (F(rng.randint(1, 9), rng.randint(1, 9)), rng.randint(1, 3))
        reach = rf.reaches(game, beh, trem)
        absent0 = absent1 = True
        for key in s1s[v]:
            mem = game.members[("L", key)]
            mu = limit_belief({(t, p): reach[(t, p)] for t, p, _ in mem})
            if sum(w for (t, _), w in mu.items() if t == t0) > 0:
                absent0 = False
        for key in sm[v]:
            mem = game.members[("L", key)]
            mu = limit_belief({(t, p): reach[(t, p)] for t, p, _ in mem})
            if sum(w for (t, _), w in mu.items() if t == t1) > 0:
                absent1 = False
        assert absent0 or absent1
        hits += 1
    return hits


# --------------------------------------------------- explicit constructions


def solve_fixed(game, pref, trem, fixed, rounds=200):
    """runtime_features_late_leak.solve with some listener sets held at given
    mixtures (they must be best replies: check_se verifies it)."""
    pinned = rf.pinned_answers(game)
    depth = {iset: min(len(path) for _, path, _ in mem) for iset, mem in game.members.items()}
    beh = {}
    for iset, acts in game.actions.items():
        if iset in fixed:
            beh[iset] = dict(fixed[iset])
        elif iset[0] == "L" and iset[1] in pinned:
            beh[iset] = {pinned[iset[1]]: F(1)}
        else:
            beh[iset] = {pref(iset, acts)[0]: F(1)}
    for _ in range(rounds):
        _, _, qvals = rf.assessment_q(game, beh, trem)
        bad = {iset: qs for iset, qs in qvals.items() if iset not in fixed
               and qs[next(iter(beh[iset]))] != max(qs.values())}
        if not bad:
            try:
                rf.check_se(game, beh, trem)
            except AssertionError:
                return None
            return beh
        deepest = max(depth[i] for i in bad)
        for iset, qs in bad.items():
            if depth[iset] == deepest:
                top = max(qs.values())
                beh[iset] = {next(a for a in pref(iset, game.actions[iset]) if qs[a] == top): F(1)}
    return None


def escape_theta(cfg: Combo) -> F:
    a = cfg.a_known()
    b = 1 - a
    return F(0) if max(a, b) <= a + b / 2 else F(1, 2)


def construct_escape_se(cfg: Combo, game=None):
    """At or below the boundary: an SE with the intended outcome, built as in
    `escape_weight`. theta (averaged f1 at the uninformative failure) is 0 or
    1/2; classes with kappa_v > 0 get a face at S1s(v) where the listener
    guesses; a class with kappa_v = 0 gets m everywhere (delta = 0, all its
    types indifferent). Tilts (deferral coefficients per type): the types
    that open at L1 get 1/(1 - alpha), so every Sm(v) belief is uniform
    (max 1/3 <= 2/5); for theta = 1/2 class 1 is scaled by 11/9 so that
    P(v = 1 | Fu) = 1/2 and the mixed failure answer is a best reply.
    Returns (beh, trem) verified by check_se, or None."""
    game = game or TreeGame(cfg)
    theta = escape_theta(cfg)
    s1s, sm = site_families(game)
    faces = [v for v in (0, 1) if (theta < 1 if v == 1 else theta > 0)]
    guess_of = {1: "gA", 0: "gB"}
    al, q, r = cfg.alpha(), cfg.q, cfg.r
    big_k = (1 - q) * al * (1 - cfg.lam) * r
    delta = q * al * r / 2
    l1_types = set()
    for v in faces:
        kap = big_k * ((1 - theta) if v == 1 else theta)
        gaps = {"A": delta + (kap if v == 1 else -kap), "B": delta + (-kap if v == 1 else kap), "C": -delta}
        assert all(g != 0 for g in gaps.values())
        l1_types |= {(v, s) for s, g in gaps.items() if g > 0}

    def pref(iset, acts):
        if iset[0] == "L":
            key = iset[1]
            for v in faces:
                if key in s1s[v]:
                    return sorted(acts, key=lambda x: (x != guess_of[v], rf.LISTENER_ORDER.index(x)))
        if iset[0] == "S" and iset[2][0] == "L1" and iset[2][1] == ():
            want = "open" if iset[1] in l1_types else "wait"
            return sorted(acts, key=lambda x: (x != want, rf.SENDER_ORDER.index(x)))
        return rf.default_pref(iset, acts)

    trem = {}
    for t in TYPES:
        coef = 1 / (1 - al) if t in l1_types else F(1)
        if theta == F(1, 2) and t[0] == 1:
            coef *= F(11, 9)
        trem[(("S", t, ("P",)), "wait")] = (coef, 1)
    fixed = {}
    if 0 < theta < 1:
        for iset in game.actions:
            if iset[0] == "L" and "res=fail" in iset[1] and "v=" not in iset[1] and "sig" not in iset[1]:
                fixed[iset] = {"f1": theta, "f0": 1 - theta}
    beh = solve_fixed(game, pref, trem, fixed)
    if beh is None:
        return None
    # the limit answers realize the escape: guesses at the face sites, m at
    # every Sm site, theta at the main uninformative failure
    for v in faces:
        for key in s1s[v]:
            if "pkt" not in key:
                assert set(beh[("L", key)]) <= set(GUESSES)
    return beh, trem


def construct_signal_escape(cfg: Combo, theta: F, game=None):
    """The escape through raw signals (charged c at L1, then the opening at
    L2), for c near R/2. No type opens at L1 with positive probability, so the
    cross ratio has nothing to act on; the listener answers m at every S1s
    and Sm site (interior beliefs by tilts) and guesses at the signal site.
    theta = 1/2: (1, A) signals with sig1 and (0, B) with sig0, the others
    hold; P(v = 1 | Fu) = 1/2 (class 1 scaled by 11/9) and the listener mixes
    f1, f0 equally there. theta = 0: only (1, A) signals; class 0 has
    kappa_0 = 0 and all its types are indifferent; the listener answers f0
    at Fu. Tilts: a signaller defers at rate eps, opens at L1 or sends the
    other symbol at rate eps^2; a holder of a class with a signaller defers
    at rate eps^2 (so every Sm and S1s belief is uniform). Returns (beh, trem)
    verified by check_se, or None."""
    game = game or TreeGame(cfg)
    sigt = {(1, "A"): "sig1", (0, "B"): "sig0"} if theta == F(1, 2) else {(1, "A"): "sig1"}
    sig_classes = {t[0] for t in sigt}

    def pref(iset, acts):
        if iset[0] == "S" and iset[2] == ("L1", ()):
            want = sigt.get(iset[1], "wait")
            return sorted(acts, key=lambda a: (a != want, rf.SENDER_ORDER.index(a)))
        if iset[0] == "S" and iset[2][0] == "L1" and iset[2][1] != "after P":
            return sorted(acts, key=rf.WAIT_FIRST.index)
        return rf.default_pref(iset, acts)

    trem = {}
    for t in TYPES:
        z = F(11, 9) if (theta == F(1, 2) and t[0] == 1) else F(1)
        if t in sigt:
            trem[(("S", t, ("P",)), "wait")] = (z, 1)
            trem[(("S", t, ("L1", ())), "open")] = (F(1), 2)
            other = [a for a in (f"sig{x}" for x in range(cfg.alphabet)) if a != sigt[t]]
            for a in other:
                trem[(("S", t, ("L1", ())), a)] = (F(1), 2)
        elif t[0] in sig_classes:
            trem[(("S", t, ("P",)), "wait")] = (z, 2)
    fixed = {}
    if theta == F(1, 2):
        for iset in game.actions:
            if iset[0] == "L" and "res=fail" in iset[1] and "v=" not in iset[1] and "sig" not in iset[1]:
                fixed[iset] = {"f1": theta, "f0": 1 - theta}
    beh = solve_fixed(game, pref, trem, fixed, rounds=80)
    if beh is None:
        return None
    # nobody opens at L1 after the silent deferral; the signallers signal
    for t in TYPES:
        b = beh[("S", t, ("L1", ()))]
        assert b == {sigt.get(t, "wait"): F(1)}, (t, b)
    return beh, trem


def signal_threshold(cfg: Combo) -> F:
    """Exact level above which a raw signal at L1 (or at L2 after the L1
    opening) is strictly worse than the best core continuation for every
    listener behaviour: the type rewarded by a guess at the signal site and
    by the failure answer there, against m at every core success site and
    the opposite failure answer."""
    return cfg.r / 2 + (1 - cfg.q) * (1 - cfg.lam) * cfg.r / cfg.q


def retry_threshold(game) -> F:
    """Exact level above which the blind retry is strictly worse than waiting
    at every member of every L2 set after the L1 opening, for every listener
    behaviour (the coupled minimum is affine in c)."""
    pinned = rf.pinned_answers(game)
    worst = None
    for iset, mem in silent_sender_isets(game).items():
        if "retry" not in game.actions[iset]:
            continue
        for _, _, node in mem:
            m = exact_affine_margin(node[2]["wait"], node[2]["retry"], pinned)
            worst = m if worst is None else min(worst, m)
    return worst


def dev_formula_exact(cfg: Combo) -> tuple:
    return dev_formula(cfg, escape_weight(cfg)), cfg.r / 2


# --------------------------------------------------- contract with k mids


def contract_checks_k(k: int, q: F = F(99, 100)) -> int:
    """T2 with owner-only inclusion and up to k listener packets (one per
    observe-only activation): erasure identity (BlindToLatePackets) at the
    inclusion step for every pending late packet, non-owner packets never
    included, the owner's inclusion law q, 2q/(1+q); AsyncTimely and the
    protected/late split as in runtime_features_late_leak.contract_checks."""
    deadline, delay, bound = 2, 0, 1
    assert delay + bound < deadline and 0 + bound < deadline and not (1 + bound < deadline)
    w = q / (1 - q)

    def law(pending):
        cands = [p for p in pending if p["event"] and p["author"] == "B"]
        tot = 1 + len(cands) * w
        out = {("include", p["id"]): w / tot for p in cands}
        out[("skip",)] = 1 / tot
        return out

    n = 0
    for l1, l2, n_lp in itertools.product(("none", "open", "sig"), ("none", "open", "sig"), range(k + 1)):
        pend = []
        serial = itertools.count()
        for kind in (l1,):
            if kind != "none":
                pend.append({"id": ("B", next(serial)), "author": "B", "event": kind == "open"})
        for j in range(n_lp):
            pend.append({"id": ("A", j), "author": "A", "event": True})
        if l2 != "none":
            pend.append({"id": ("B", next(serial)), "author": "B", "event": l2 == "open"})
        lw = law(pend)
        assert sum(lw.values()) == 1
        for pk in pend:
            if not pk["event"]:
                continue
            alpha = lw.get(("include", pk["id"]), F(0))
            other = law([x for x in pend if x["id"] != pk["id"]])
            for cmd, pc in lw.items():
                if cmd != ("include", pk["id"]):
                    assert pc == (1 - alpha) * other.get(cmd, F(0))
        assert all(cmd[1][0] == "B" for cmd in lw if cmd[0] == "include")
        opens = sum(1 for x in (l1, l2) if x == "open")
        ok = sum(p for cmd, p in lw.items() if cmd[0] == "include")
        assert ok == ({0: F(0), 1: q, 2: 2 * q / (1 + q)}[opens])
        n += 1
    return n


# ------------------------------------------------------------------ driver


POINTS = [  # (D, c, q), R = 2
    (F(6), F(3), F(99, 100)),
    (F(6), F(3), F(999, 1000)),
    (F(6), F(3), F(9999, 10000)),
    (F(12), F(6), F(999, 1000)),
    (F(24), F(12), F(9999, 10000)),
    (F(12), F(3), F(99, 100)),
    (F(6), F(1), F(99, 100)),
    (F(6), F(0), F(999, 1000)),
]


def min_k(cfg: Combo, kmax=60):
    for k in range(1, kmax + 1):
        c = replace(cfg, k=k)
        if dev_formula_exact(c)[0] > c.r / 2:
            return k
    return None


def threshold_in_c(cfg: Combo, fn) -> F:
    """Root of an affine function of c (fn(cfg) is affine in cfg.c)."""
    m0, m1 = fn(replace(cfg, c=F(0))), fn(replace(cfg, c=F(1)))
    assert m0 != m1
    return m0 / (m0 - m1)


def retry_c(cfg: Combo) -> F:
    return threshold_in_c(cfg, lambda c: retry_threshold(TreeGame(c)))


def leak_boundary_k1(cfg: Combo):
    """k = 1: alpha = lam, a = 2 lam - lam^2 < 1/3 near the boundary, so the
    escape weight is (1 + a)/2 and the no-SE condition is the quadratic
    q lam R/2 + (1-q) R (1 + 2 lam - lam^2)/2 > (1-q)(R/2 + D + c), i.e.
    (1-q) lam^2 - (q + 2(1-q)) lam + 2(1-q)(D + c)/R < 0 (R/2 cancels).
    Returns the coefficients (A, B, C) of A lam^2 + B lam + C."""
    q, r = cfg.q, cfg.r
    return (1 - q, -(q + 2 * (1 - q)), 2 * (1 - q) * (cfg.d + cfg.c) / r)


def family_q(d: F, c: F, lam=F(1, 2), k=1, r=F(2)):
    """Smallest q = 1 - 10^-n (n <= 6) at which the certificate applies to
    the builder with this lam and k, for the fixed margins (D, c)."""
    for n in range(1, 7):
        q = 1 - F(1, 10 ** n)
        cfg = Combo(r=r, d=d, c=c, q=q, lam=lam, k=k, listener=False)
        if not cfg.deferral_pays() or c <= signal_threshold(cfg) or c <= retry_c(cfg):
            continue
        if dev_formula_exact(cfg)[0] <= r / 2:
            continue
        return q
    return None


def main() -> None:
    assert rf.case_lemma() > 0
    for k in (1, 2, 3):
        assert contract_checks_k(k) > 0
    rf.selective_leak_not_stateless()
    print("Contract (T2, owner-only, up to 3 listener packets): erasure identity, inclusion laws")
    half = F(1)

    # 1. the main configuration: G*'s margins, lam = 1/2, k = 1, all features
    base = Combo()
    game = TreeGame(base)
    res = certificate(base, game)
    assert res["no_se"] and not res["p1_fails"] and res["p4"]
    s1s, sm = site_families(game)
    assert face_dichotomy_samples(game, s1s, sm) == 30
    print(f"G* margins, lam=1/2, k=1, all features: no preserving SE "
          f"(escape value {res['escape_value']} > R/2; P1-P5 hold)")
    print(f"  extras: signal threshold {signal_threshold(base)}, retry threshold {retry_c(base)}")

    # 2. the leak window at k = 1 and its closure by more observe-only activations
    a_, b_, c_ = leak_boundary_k1(base)
    for lam, side in ((F(89, 1000), "SE"), (F(9, 100), "no")):
        assert (a_ * lam ** 2 + b_ * lam + c_ < 0) == (side == "no")
    for lam, k, side in ((F(1, 20), 1, "SE"), (F(89, 1000), 1, "SE"), (F(9, 100), 1, "no"),
                         (F(1, 10), 1, "no"), (F(1, 20), 2, "no"), (F(1, 20), 3, "no")):
        cfg = replace(base, lam=lam, k=k)
        g = TreeGame(cfg)
        res = certificate(cfg, g)
        assert res["no_se"] == (side == "no"), (lam, k)
        if side == "SE":
            assert res["escape_value"] <= half
            built = construct_escape_se(cfg, g)
            assert built is not None, (lam, k)
        print(f"  lam={lam}, k={k}: {side} (escape value {float(res['escape_value']):.6f})")
    # small lam: enough activations always suffice (listener packets omitted
    # for tree size; they were included above up to k = 3)
    for lam in (F(1, 100), F(1, 1000)):
        cfg = replace(base, lam=lam, listener=False)
        k = min_k(cfg, kmax=400)
        assert k is not None
        if k <= 20:
            assert certificate(replace(cfg, k=k))["no_se"]
            assert not certificate(replace(cfg, k=k - 1))["no_se"]
        print(f"  lam={lam}: no preserving SE from k={k} observe-only activations")
    # deterministic rule (lam = 1): complete observation, positive control
    cfg = replace(base, lam=F(1))
    assert rf.solve(TreeGame(cfg)) is not None
    print("  lam=1 (deterministic rule): verified preserving SE (complete observation)")

    # 3. the grid at lam = 1/2, k = 1
    print("Grid (R = 2, lam = 1/2, k = 1, all features):")
    for d, c, q in POINTS:
        cfg = replace(base, d=d, c=c, q=q)
        res = certificate(cfg)
        sig, ret = signal_threshold(cfg), retry_c(cfg)
        if res["no_se"]:
            verdict = "no preserving SE"
        elif c == F(1):
            assert construct_signal_escape(cfg, F(1, 2)) is not None
            assert construct_signal_escape(cfg, F(0)) is not None
            verdict = "SE (signal escape)"
        elif c == F(0):
            assert rf.solve(TreeGame(cfg)) is not None
            verdict = "SE (retry pooling)"
        else:
            verdict = "?"
        print(f"  D={d} c={c} q={q}: {verdict}; signal thr {float(sig):.5f}, retry thr {float(ret):.5f}")
    # the signal window at D = 6, q = 99/100: escapes up to (1-q)(1-lam)(1-alpha)R/q above R/2
    for c in (F(1), F(201, 200)):
        assert construct_signal_escape(replace(base, c=c), F(0)) is not None
    assert construct_signal_escape(replace(base, c=F(501, 500)), F(1, 2)) is not None
    upper = base.r / 2 + (1 - base.q) * (1 - base.lam) * (1 - base.alpha()) * base.r / base.q
    assert F(201, 200) <= upper < signal_threshold(base)
    print(f"  signal escape verified at c = 1, 501/500, 201/200 (design bound {upper}); "
          f"certificate above {signal_threshold(base)}")
    # the retry window: pooling on the double send at small c
    assert rf.solve(TreeGame(replace(base, c=F(1, 100)))) is not None
    print("  retry pooling verified at c = 1/100 (q = 99/100) and c = 0 (q = 999/1000)")

    # 4. fixed margins, builder chosen afterwards: q -> 1
    print("Fixed margins (R = 2), builder lam = 1/2, k = 1, q chosen after the margins:")
    for d, c in ((F(3), F(11, 10)), (F(3), F(3)), (F(6), F(3)), (F(60), F(2)), (F(60), F(30)),
                 (F(600), F(101, 100)), (F(21, 10), F(1001, 1000))):
        q = family_q(d, c)
        assert q is not None, (d, c)
        cfg = Combo(d=d, c=c, q=q)
        if q <= F(9999, 10000):
            assert certificate(cfg)["no_se"]
        assert certificate(replace(cfg, listener=False))["no_se"]
        print(f"  D={d} c={c}: no preserving SE at q={q}")
    # at c = R/2 the signal escape works for every q (R/2 - (1-q)D <= c)
    for d, q in ((F(6), F(999, 1000)), (F(60), F(999, 1000))):
        assert construct_signal_escape(Combo(d=d, c=F(1), q=q), F(0)) is not None
    print("  c = R/2: verified preserving SE (signal escape) at q = 999/1000, D = 6 and 60")
    print("verdict: with a valid stateless leak rule (openings seen w.p. lam at each listener "
          "activation, other packets surely), the settle-late builder and every non-restoring "
          "feature at once, no SE preserves G*'s intended outcome whenever c > R/2 + (1-q)(1-lam)R/q, "
          "c exceeds the retry threshold, the G* hypotheses hold and the escape value exceeds R/2; "
          "for every fixed D > R and c > R/2 some q < 1 meets all of these")


if __name__ == "__main__":
    main()
