#!/usr/bin/env python3
"""Exact test: does the late-leak obstruction G* survive the extra options of
the actual asynchronous runtime?

Background: docs/open-problem-late-turn-equilibria.md (game G*, mechanized in
Vegas/Examples/LateLeak). Types (v, s), v in {0, 1} with P(v = 1) = 9/20, s in
{A, B, C} uniform; R = 2, D = 6, c = 3, q = 99/100. The sender opens at a
protected turn P or late at L1, L2 (content-blind inclusion coin q); a listener
activated between L1 and L2 sees a pending L1 opening (selective leak). No
sequential equilibrium of G* has the intended outcome (every type opens at P,
the listener plays m). Summary of results: docs/runtime-features-vs-late-leak.md.

Runtime model (one late slot, deadline 2, reaction delay 0, inclusion bound 1):
  clock 0: sender activation P; protected inclusion step; clock -> 1;
  sender activation L1; listener activation (observe only, its answer event
  is not ready); [T1: inclusion step 1]; sender activation L2; final inclusion
  step; [optional sender activation `post`]; clock -> 2; expiry; listener answers.
Two blind schedulers (both satisfy AsyncContract, AsyncTimely and
BlindToLatePackets, checked on explicit traces in `contract_checks`):
  T1: a late packet can be included only at the first inclusion step after it
      was sent (with probability q when it is the only fresh one); the L1 result
      is therefore known at L2, and an L1 packet not included is dropped.
  T2: one inclusion step after L2 for all late packets.
Several fresh candidates at one step get the Luce law forced by blindness:
each with weight q/(1-q) against 1 for no inclusion. Every activation emits at
most one packet; a packet without an accepting receipt (dropped opening, extra
opening, raw signal) is forbidden, and the audit charges the owner c at most
once (capped escrow); D is the failure forfeit.

Features (alone and combined):
1. retries (a fresh opening at L2 after an L1 opening: informed under T1, a
   blind double send under T2);
2. raw messages: free post-charge talk after a known L1 drop (T1, at L2), a
   post-result activation with talk (free once charged), and pre-charge
   signals at P or L1 (forbidden, charged, visible at the listener's
   activations);
3. contract constraints (`contract_checks`);
4. listener raw packets at its observe-only activation (charged c_L), either
   pure messages seen by the sender or, under an author-blind builder, packets
   competing for inclusion with the owner's late opening (jamming).
Also: a stateless symmetric leak (each pending opening seen with probability
lambda at every listener activation), the leak law the runtime's
ObservationRule can express, in place of G*'s selective leak.

Method (exact fractions, every claim an assert):
- `Game`/`check_se`: generic finite two-player tree, Kreps-Wilson consistency by
  fully mixed polynomial families in eps (type- and node-dependent trembles),
  one-shot sequential rationality at every information set (perfect recall),
  intended outcome law on path. `solve` finds a candidate by best-reply
  iteration with type-independent trembles; every positive verdict is
  `check_se`-verified.
- negative verdicts: the reduction certificate (extra options strictly
  dominated for every listener behaviour, or payoff-equivalent through pinned
  answers; the core is G*: plan values equal the independent encoding of
  late_turn_search.py at every pure listener behaviour) plus the G* theorem; or
  a feature-specific variant of its four steps, whose premises are asserted.
- negative controls: the uniform assessment is rejected in G* itself, and each
  positive construction fails once its feature is removed.

Run: python scripts/experiments/runtime_features_late_leak.py
"""

from __future__ import annotations

import itertools
import random
import sys
from dataclasses import dataclass, replace
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import late_turn_search as lts  # noqa: E402  (independent encoding of G*)
from timed_release_probe import limit_belief, pmul, poly  # noqa: E402

S_LABELS = ("A", "B", "C")
TYPES = tuple((v, s) for v in (0, 1) for s in S_LABELS)
P_V1 = F(9, 20)
SUCCESS = ("m", "gA", "gB", "gC")
FAILURE = ("f1", "f0")
CORE = ("open", "wait", "quiet")
INTENDED_LABEL = ("P", "m")


def prior(t) -> F:
    return (P_V1 if t[0] else 1 - P_V1) / 3


def listener_u(a: str, t) -> F:
    v, s = t
    if a == "m":
        return F(2, 5)
    if a.startswith("g"):
        return F(int(a[1] == s))
    return F(int(a == f"f{v}"))


def sender_base(a: str, t, r: F) -> F:
    s = t[1]
    if a == "m":
        return r / 2
    if a.startswith("g"):
        return r if s in ("A", "B") else F(0)
    if a == "f1":
        return r if s == "A" else F(0)
    return r if s == "B" else F(0)


# ------------------------------------------------------------------ the model


@dataclass(frozen=True)
class Cfg:
    r: F = F(2)
    d: F = F(6)
    c: F = F(3)
    q: F = F(99, 100)
    timing: str = "T2"
    retry: bool = False
    sig_p: bool = False
    sig_l1: bool = False
    alphabet: int = 2
    talk_l2: bool = False
    post: bool = False
    talk_visible: bool = True
    listener: str | None = None  # None, "message", "jam"
    c_l: F = F(1, 10)
    leak: F | None = None  # None: selective leak of G*; else stateless probability

    def deferral_pays(self) -> bool:
        """Hypothesis of the mechanized G* theorem."""
        r, d, c, q = self.r, self.d, self.c, self.q
        return r > 0 and (1 - q) * c < q * (d - r) and r / 2 < q * r - (1 - q) * (d + c)


def own_label(e) -> str:
    act, kind, x = e
    return f"{act}:{kind}" + ("" if kind == "open" else str(x))


class Builder:
    """Per-type game trees. Nodes: ("S", key, {a: child}) sender decision
    (information set (type, key)); ("L", key, {a: child}) listener decision;
    ("C", [(p, child)]); ("T", label, u_sender, u_listener)."""

    def __init__(self, cfg: Cfg):
        self.cfg = cfg
        self.w = cfg.q / (1 - cfg.q)

    def trees(self) -> dict:
        return {t: self.root(t) for t in TYPES}

    def root(self, t):
        cfg = self.cfg
        acts = {"open": self.p_success(t), "wait": self.l1(t, ())}
        if cfg.sig_p:
            for x in range(cfg.alphabet):
                acts[f"sig{x}"] = self.l1(t, (("P", "sig", x),))
        return ("S", ("P",), acts)

    def p_success(self, t):
        """Protected opening included at clock 0. On path the listener answers
        at its first activation; with pre-charge signals the sender may first
        emit a (charged) raw signal at L1, visible to the listener."""
        cfg = self.cfg
        if not cfg.sig_l1:
            return self.answer_p(t, None)
        acts = {"wait": self.answer_p(t, None)}
        for x in range(cfg.alphabet):
            acts[f"sig{x}"] = self.answer_p(t, x)
        return ("S", ("L1", "after P"), acts)

    def answer_p(self, t, x):
        cfg = self.cfg
        key = f"ans|P|v={t[0]}" + ("" if x is None else f"|sig{x}")
        pen = F(0) if x is None else cfg.c
        label = "P" if x is None else "P+sig"
        return ("L", key, {a: ("T", (label, a), sender_base(a, t, cfg.r) - pen, listener_u(a, t))
                           for a in SUCCESS})

    def l1(self, t, em):
        cfg = self.cfg
        v = t[0]
        acts = {"open": self.mid(t, em + (("L1", "open", v),)), "wait": self.mid(t, em)}
        if cfg.sig_l1:
            for x in range(cfg.alphabet):
                acts[f"sig{x}"] = self.mid(t, em + (("L1", "sig", x),))
        return ("S", ("L1", tuple(own_label(e) for e in em)), acts)

    def mid(self, t, em):
        """Listener's observe-only activation between L1 and L2."""
        cfg = self.cfg
        sigs = [f"{a}:sig{x}" for a, k, x in em if k == "sig"]
        opened = any(k == "open" for _, k, _ in em)

        def after(seen):
            obs = ",".join(sigs + ([f"open{t[0]}"] if opened and seen else [])) or "-"
            st = {"em": em, "mid": obs, "seen": opened and seen, "inc": None, "jam_inc": False}
            if cfg.listener:
                return ("L", f"mid|{obs}", {"quiet": self.step1(t, dict(st, lp=False)),
                                            "pkt": self.step1(t, dict(st, lp=True))})
            return self.step1(t, dict(st, lp=False))

        if opened and cfg.leak is not None and cfg.leak < 1:
            return ("C", [(cfg.leak, after(True)), (1 - cfg.leak, after(False))])
        return after(True)

    def luce(self, t, st, fresh, jam, step, cont):
        n = len(fresh) + int(jam)
        if n == 0:
            return cont(t, st)
        tot = 1 + n * self.w
        out = [(self.w / tot, cont(t, dict(st, inc=(step, i)))) for i in fresh]
        if jam:
            out.append((self.w / tot, cont(t, dict(st, jam_inc=True))))
        out.append((1 / tot, cont(t, st)))
        return ("C", out)

    def step1(self, t, st):
        if self.cfg.timing != "T1":
            return self.l2(t, st)
        fresh = [i for i, (a, k, _) in enumerate(st["em"]) if a == "L1" and k == "open"]
        jam = self.cfg.listener == "jam" and st["lp"]
        return self.luce(t, st, fresh, jam, "step1", self.l2)

    def l2(self, t, st):
        cfg = self.cfg
        if st["inc"] is not None:
            return self.post(t, st)
        em = st["em"]
        v = t[0]
        opened = any(k == "open" for _, k, _ in em)
        key = ("L2", tuple(own_label(e) for e in em), "jam on ledger" if st["jam_inc"] else "",
               st["lp"] if cfg.listener else None)
        if opened:
            acts = {"wait": self.step2(t, st)}
            if cfg.retry:
                acts["retry"] = self.step2(t, dict(st, em=em + (("L2", "open", v),)))
            if cfg.talk_l2 and cfg.timing == "T1":
                for x in range(cfg.alphabet):
                    acts[f"talk{x}"] = self.step2(t, dict(st, em=em + (("L2", "talk", x),)))
        else:
            acts = {"open": self.step2(t, dict(st, em=em + (("L2", "open", v),))),
                    "wait": self.step2(t, st)}
        return ("S", key, acts)

    def step2(self, t, st):
        cfg = self.cfg
        em = st["em"]
        if cfg.timing == "T1":
            fresh = [i for i, (a, k, _) in enumerate(em) if a == "L2" and k == "open"]
            return self.luce(t, st, fresh, False, "step2", self.post)
        fresh = [i for i, (_, k, _) in enumerate(em) if k == "open"]
        jam = cfg.listener == "jam" and st["lp"]
        return self.luce(t, st, fresh, jam, "end", self.post)

    @staticmethod
    def result(st) -> str:
        return "fail" if st["inc"] is None else f"ok:{st['inc'][0]}:{st['inc'][1]}"

    def post(self, t, st):
        cfg = self.cfg
        if not cfg.post:
            return self.answer(t, st)
        em = st["em"]
        key = ("post", tuple(own_label(e) for e in em), self.result(st),
               st["lp"] if cfg.listener else None, st["jam_inc"])
        acts = {"quiet": self.answer(t, st)}
        for x in range(cfg.alphabet):
            acts[f"talk{x}"] = self.answer(t, dict(st, em=em + (("post", "talk", x),)))
        return ("S", key, acts)

    def answer(self, t, st):
        cfg = self.cfg
        v = t[0]
        em, inc = st["em"], st["inc"]
        success = inc is not None
        dropped = [i for i, (_, k, _) in enumerate(em) if k == "open" and (inc is None or inc[1] != i)]
        charged = any(k in ("sig", "talk") for _, k, _ in em) or bool(dropped)
        talks = [f"{a}:talk{x}" for a, k, x in em if k == "talk"] if cfg.talk_visible else []
        res = self.result(st)

        def node(late_seen):
            known = success or st["seen"] or late_seen
            parts = [f"mid={st['mid']}", f"res={res}"]
            if cfg.listener:
                parts.append(f"lp={int(st['lp'])}")
            if st["jam_inc"]:
                parts.append("jam on ledger")
            if late_seen:
                parts.append("late seen")
            if talks:
                parts.append("talk=" + ",".join(talks))
            if known:
                parts.append(f"v={v}")
            menu = SUCCESS if success else FAILURE
            pen = (F(0) if success else cfg.d) + (cfg.c if charged else F(0))
            lpen = cfg.c_l if st["lp"] else F(0)
            return ("L", "ans|" + "|".join(parts),
                    {a: ("T", ("late", a), sender_base(a, t, cfg.r) - pen, listener_u(a, t) - lpen)
                     for a in menu})

        if cfg.leak is not None and dropped:
            if cfg.leak == 1:
                return node(True)
            p_seen = 1 - (1 - cfg.leak) ** len(dropped)
            return ("C", [(p_seen, node(True)), (1 - p_seen, node(False))])
        return node(False)


# --------------------------------------------------------------------- engine


def iter_nodes(node, path=()):
    yield path, node
    if node[0] in ("S", "L"):
        for a, ch in node[2].items():
            yield from iter_nodes(ch, path + (a,))
    elif node[0] == "C":
        for i, (_, ch) in enumerate(node[1]):
            yield from iter_nodes(ch, path + (i,))


def iset_of(t, node):
    return ("S", t, node[1]) if node[0] == "S" else ("L", node[1])


class Game:
    def __init__(self, cfg: Cfg):
        self.cfg = cfg
        self.trees = Builder(cfg).trees()
        self.members: dict = {}
        for t, root in self.trees.items():
            for path, node in iter_nodes(root):
                if node[0] in ("S", "L"):
                    self.members.setdefault(iset_of(t, node), []).append((t, path, node))
        self.actions = {}
        for iset, mem in self.members.items():
            acts = tuple(mem[0][2][2])
            assert all(set(m[2][2]) == set(acts) for m in mem), iset
            self.actions[iset] = acts

    def node_at(self, t, path):
        node = self.trees[t]
        for step in path:
            node = node[2][step] if node[0] in ("S", "L") else node[1][step][1]
        return node


def action_poly(game, beh, trem, iset, a):
    lim = beh[iset]
    if lim.get(a, 0) == 0:
        return poly(trem.get((iset, a), (F(1), 1)))
    zero = [b for b in game.actions[iset] if lim.get(b, 0) == 0]
    terms = [trem.get((iset, b), (F(1), 1)) for b in zero]
    return poly((lim[a], 0), *[(-lim[a] * cf, e) for cf, e in terms])


def reaches(game, beh, trem) -> dict:
    out = {}

    def go(t, node, path, mass):
        out[(t, path)] = mass
        if node[0] in ("S", "L"):
            iset = iset_of(t, node)
            for a, ch in node[2].items():
                go(t, ch, path + (a,), pmul(mass, action_poly(game, beh, trem, iset, a)))
        elif node[0] == "C":
            for i, (p, ch) in enumerate(node[1]):
                go(t, ch, path + (i,), pmul(mass, poly((p, 0))))

    for t, root in game.trees.items():
        go(t, root, (), poly((prior(t), 0)))
    return out


def values(game, beh) -> dict:
    """Expected (sender, listener) payoff of each node under the limit profile."""
    memo = {}

    def val(t, node, path):
        if node[0] == "T":
            r = (node[2], node[3])
        elif node[0] == "C":
            subs = [(p, val(t, ch, path + (i,))) for i, (p, ch) in enumerate(node[1])]
            r = (sum(p * x[0] for p, x in subs), sum(p * x[1] for p, x in subs))
        else:
            iset = iset_of(t, node)
            subs = {a: val(t, ch, path + (a,)) for a, ch in node[2].items()}
            r = (sum(p * subs[a][0] for a, p in beh[iset].items()),
                 sum(p * subs[a][1] for a, p in beh[iset].items()))
        memo[(t, path)] = r
        return r

    for t, root in game.trees.items():
        val(t, root, ())
    return memo


def assessment_q(game, beh, trem):
    """Limit beliefs and action values (for the mover) at every information set."""
    reach = reaches(game, beh, trem)
    vals = values(game, beh)
    beliefs, qvals = {}, {}
    for iset, mem in game.members.items():
        mu = limit_belief({(t, path): reach[(t, path)] for t, path, _ in mem})
        beliefs[iset] = mu
        who = 0 if iset[0] == "S" else 1
        qvals[iset] = {a: sum(w * vals[(t, path + (a,))][who] for (t, path), w in mu.items())
                       for a in game.actions[iset]}
    return reach, beliefs, qvals


def check_se(game, beh, trem=None, intended=True) -> dict:
    """Exact Kreps-Wilson check; raises AssertionError on any violation."""
    trem = trem or {}
    for iset, mix in beh.items():
        assert sum(mix.values()) == 1 and all(p >= 0 for p in mix.values()), iset
    reach, beliefs, qvals = assessment_q(game, beh, trem)
    for iset, qs in qvals.items():
        top = max(qs.values())
        bad = [a for a, p in beh[iset].items() if p > 0 and qs[a] != top]
        assert not bad, (iset, qs, beh[iset])
    if intended:
        law = {}
        for t, root in game.trees.items():
            for path, node in iter_nodes(root):
                if node[0] == "T":
                    p0 = reach[(t, path)].get(0, F(0))
                    if p0:
                        law[(t, node[1])] = law.get((t, node[1]), F(0)) + p0
        assert law == {(t, INTENDED_LABEL): prior(t) for t in TYPES}, law
    return beliefs


SENDER_ORDER = ["open", "retry", "wait", "quiet", "sig0", "sig1", "sig2", "talk0", "talk1", "talk2"]
LISTENER_ORDER = ["m", "f0", "f1", "gA", "gB", "gC", "quiet", "pkt"]
WAIT_FIRST = ["wait", "open"] + [a for a in SENDER_ORDER if a not in ("wait", "open")]


def default_pref(iset, acts):
    order = SENDER_ORDER if iset[0] == "S" else LISTENER_ORDER
    return sorted(acts, key=order.index)


def solve(game, pref=default_pref, trem=None, rounds=200):
    """Best-reply iteration from a pure profile (type-independent trembles),
    in backward-induction order: each round revises only the deepest
    information sets whose prescribed action is not a best reply. Returns a
    pure profile passing check_se, or None (a heuristic: None proves nothing)."""
    trem = trem or {}
    pinned = pinned_answers(game)
    depth = {iset: min(len(path) for _, path, _ in mem) for iset, mem in game.members.items()}
    beh = {iset: {pinned.get(iset[1]) if iset[0] == "L" and iset[1] in pinned
                  else pref(iset, acts)[0]: F(1)}
           for iset, acts in game.actions.items()}
    for _ in range(rounds):
        _, _, qvals = assessment_q(game, beh, trem)
        bad = {iset: qs for iset, qs in qvals.items()
               if qs[next(iter(beh[iset]))] != max(qs.values())}
        if not bad:
            try:
                check_se(game, beh, trem)
            except AssertionError:
                return None
            return beh
        deepest = max(depth[i] for i in bad)
        for iset, qs in bad.items():
            if depth[iset] == deepest:
                top = max(qs.values())
                beh[iset] = {next(a for a in pref(iset, game.actions[iset]) if qs[a] == top): F(1)}
    return None


# ------------------------------------------------- reduction certificates


def pinned_answers(game) -> dict:
    """Listener information sets with an answer strictly best at every member
    (hence at every belief): failure sites where v is known."""
    out = {}
    for iset, mem in game.members.items():
        if iset[0] != "L" or any(ch[0] != "T" for ch in mem[0][2][2].values()):
            continue
        for a in game.actions[iset]:
            if all(node[2][a][3] > node[2][b][3] for _, _, node in mem
                   for b in game.actions[iset] if b != a):
                out[iset[1]] = a
    return out


def ub(node, pinned):
    """Upper bound of the sender's value over every continuation and every
    listener behaviour (information-set constraints relaxed: sound)."""
    k = node[0]
    if k == "T":
        return node[2]
    if k == "C":
        return sum(p * ub(ch, pinned) for p, ch in node[1])
    acts = [pinned[node[1]]] if k == "L" and node[1] in pinned else list(node[2])
    return max(ub(node[2][a], pinned) for a in acts)


def lb_core(node, pinned):
    """Value the sender guarantees with core actions only, against every
    listener behaviour (sound when sender information sets are singletons)."""
    k = node[0]
    if k == "T":
        return node[2]
    if k == "C":
        return sum(p * lb_core(ch, pinned) for p, ch in node[1])
    if k == "S":
        return max(lb_core(node[2][a], pinned) for a in node[2] if a in CORE)
    acts = [pinned[node[1]]] if node[1] in pinned else list(node[2])
    return min(lb_core(node[2][a], pinned) for a in acts)


def only_pinned_below(node, pinned) -> bool:
    k = node[0]
    if k == "T":
        return True
    if k == "C":
        return all(only_pinned_below(ch, pinned) for _, ch in node[1])
    if k == "L":
        return node[1] in pinned and all(only_pinned_below(ch, pinned) for ch in node[2].values())
    return all(a in CORE for a in node[2]) and all(only_pinned_below(ch, pinned) for ch in node[2].values())


def sender_isets_singleton(game) -> bool:
    return all(len(mem) == 1 for iset, mem in game.members.items() if iset[0] == "S")


def subtree_keys(node, kind):
    out = set()
    for _, n in iter_nodes(node):
        if n[0] == kind:
            out.add(n[1])
    return out


def exact_dominated(node, extra, pinned, cap=20000) -> bool | None:
    """Exact version for coupled sites: some core plan from `node` beats every
    plan starting with `extra` at every pure listener behaviour on the
    listener sets below `node` (values are multi-affine in the listener's
    behaviour, so vertices suffice). None if the enumeration exceeds `cap`."""
    lkeys = sorted(k for k in subtree_keys(node, "L") if k not in pinned)
    skeys = sorted(subtree_keys(node, "S") - {node[1]}, key=str)
    acts_l, acts_s = {}, {}
    for _, n in iter_nodes(node):
        if n[0] == "L":
            acts_l[n[1]] = list(n[2])
        elif n[0] == "S":
            acts_s[n[1]] = list(n[2])
    n_l = 1
    for k in lkeys:
        n_l *= len(acts_l[k])
    n_s = 1
    for k in skeys:
        n_s *= len(acts_s[k])
    if n_l * n_s * len(node[2]) > cap:
        return None
    plans = [dict(zip(skeys, combo)) for combo in itertools.product(*[acts_s[k] for k in skeys])]
    vertices = []
    for combo in itertools.product(*[acts_l[k] for k in lkeys]):
        lbeh = {k: {a: F(1)} for k, a in zip(lkeys, combo)}
        lbeh.update({k: {a: F(1)} for k, a in pinned.items()})
        vertices.append(lbeh)

    def val(first, plan, lbeh):
        rule = lambda key: first if key == node[1] else plan[key]  # noqa: E731
        return plan_value(node, rule, lbeh)

    core = [(a, p) for a in node[2] if a in CORE for p in plans
            if all(x in CORE for x in p.values())]
    for plan in plans:
        if not any(all(val(extra, plan, lb) < val(a, p, lb) for lb in vertices) for a, p in core):
            return False
    return True


def extras_certificate(game) -> list:
    """Every extra sender option below silent deferral is strictly dominated by
    a core plan for every listener behaviour, or (talk into pinned sites only)
    payoff-equivalent. Returns the failures."""
    assert sender_isets_singleton(game)
    pinned = pinned_answers(game)
    failures = []
    for t in TYPES:
        deferral = game.trees[t][2]["wait"]
        for path, node in iter_nodes(deferral):
            if node[0] != "S":
                continue
            base = lb_core(node, pinned)
            for a, ch in node[2].items():
                if a in CORE:
                    continue
                top = ub(ch, pinned)
                if top < base:
                    continue
                if top <= base and only_pinned_below(ch, pinned) and ub(ch, pinned) == lb_core(ch, pinned):
                    continue
                if exact_dominated(node, a, pinned):
                    continue
                failures.append((t, node[1], a, top, base))
    return failures


def plan_value(node, rule, lbeh):
    k = node[0]
    if k == "T":
        return node[2]
    if k == "C":
        return sum(p * plan_value(ch, rule, lbeh) for p, ch in node[1])
    if k == "S":
        return plan_value(node[2][rule(node[1])], rule, lbeh)
    return sum(p * plan_value(node[2][a], rule, lbeh) for a, p in lbeh[node[1]].items())


def core_plan(name):
    """Core plans of G*: open at P, at L1, at L2, never."""
    def rule(key):
        if key[0] == "P":
            return "open" if name == "P" else "wait"
        if key[0] == "L1":
            return "open" if name == "L1" else "wait"
        if key[0] == "L2":
            opened = any(x.endswith(":open") for x in key[1])
            return "open" if (name == "L2" and not opened) else "wait"
        return "quiet"
    return rule


def final_sites(node, rule, lbeh, acc=None):
    acc = set() if acc is None else acc
    k = node[0]
    if k == "C":
        for _, ch in node[1]:
            final_sites(ch, rule, lbeh, acc)
    elif k == "S":
        final_sites(node[2][rule(node[1])], rule, lbeh, acc)
    elif k == "L":
        if all(ch[0] == "T" for ch in node[2].values()):
            acc.add(node[1])
        else:
            for a, p in lbeh[node[1]].items():
                if p:
                    final_sites(node[2][a], rule, lbeh, acc)
    return acc


TO_LTS = {"m": "m", "gA": "x0", "gB": "x1", "gC": "x2", "f0": "0", "f1": "1"}


def core_matches_gstar(game) -> int:
    """At every pure listener behaviour (answers at the sites core plans reach,
    and mid-activation choices), each type's four core plan values equal the
    independent G* encoding of late_turn_search.py evaluated at the sites the
    plans reach. Plan values are multi-affine in the listener's behaviour, so
    this proves the identity everywhere (it is the averaging lemma when the
    listener's mid packets split the sites)."""
    cfg = game.cfg
    design = lts.design_gstar(cfg.q, cfg.d, cfg.c)
    pinned = pinned_answers(game)
    count = 0
    # only the mid activations core plans pass through (signal sites are never reached)
    mids = sorted(k[1] for k in game.actions
                  if k[0] == "L" and k[1] in ("mid|-", "mid|open0", "mid|open1"))
    for mid_choice in itertools.product(*[game.actions[("L", k)] for k in mids]):
        base = {k: {a: F(1)} for k, a in zip(mids, mid_choice)}
        for v in (0, 1):
            group = [t for t in TYPES if t[0] == v]
            rules = {n: core_plan(n) for n in ("P", "L1", "L2", "never")}
            probe = dict(base)
            for k in game.actions:
                if k[0] == "L" and k[1] not in probe:
                    probe[k[1]] = {game.actions[k][0]: F(1)}
            t0 = group[0]
            s1 = final_sites(game.trees[t0], rules["L1"], probe)
            s2 = final_sites(game.trees[t0], rules["L2"], probe)
            nv = final_sites(game.trees[t0], rules["never"], probe)
            sp = final_sites(game.trees[t0], rules["P"], probe)
            succ1 = [k for k in s1 if "res=ok" in k]
            fail1 = [k for k in s1 if "res=fail" in k]
            succ2 = [k for k in s2 if "res=ok" in k]
            fail2 = [k for k in s2 if "res=fail" in k]
            assert len(succ1) == len(fail1) == len(succ2) == len(fail2) == 1 and len(sp) == 1
            assert nv == set(fail2) and fail1[0] in pinned
            free = [succ1[0], succ2[0], fail2[0]]
            for combo in itertools.product(SUCCESS, SUCCESS, FAILURE):
                lbeh = dict(probe)
                for k, a in zip(free, combo):
                    lbeh[k] = {a: F(1)}
                lbeh[fail1[0]] = {pinned[fail1[0]]: F(1)}
                lbeh[next(iter(sp))] = {"m": F(1)}
                mixes = {("A", "S", 1, v): {TO_LTS[combo[0]]: F(1)},
                         ("A", "S", 2, v): {TO_LTS[combo[1]]: F(1)},
                         ("A", "Fk", v): {TO_LTS[pinned[fail1[0]]]: F(1)},
                         ("A", "Fu"): {TO_LTS[combo[2]]: F(1)}}
                for t in group:
                    ref = lts.plan_values(design, mixes, (v, S_LABELS.index(t[1])))
                    root = game.trees[t]
                    assert plan_value(root, rules["P"], lbeh) == ref["P"]
                    assert plan_value(root, rules["L1"], lbeh) == ref[1]
                    assert plan_value(root, rules["L2"], lbeh) == ref[2]
                    assert plan_value(root, rules["never"], lbeh) == ref["never"]
                    count += 1
    return count


def send_beats_wait_at_l2(game) -> None:
    """At every L2 node of a sender who has not opened, opening strictly beats
    never opening for every listener behaviour (premise of the G* argument)."""
    assert sender_isets_singleton(game)
    pinned = pinned_answers(game)
    for t in TYPES:
        for _, node in iter_nodes(game.trees[t]):
            if node[0] == "S" and node[1][0] == "L2" and "open" in node[2]:
                assert ub(node[2]["wait"], pinned) < lb_core(node[2]["open"], pinned), (t, node[1])


def reduction_verdict(cfg: Cfg) -> bool:
    """True iff the certificate applies: then no SE of the variant has the
    intended outcome (G* theorem through the reduction lemma)."""
    assert cfg.deferral_pays()
    game = Game(cfg)
    if extras_certificate(game):
        return False
    send_beats_wait_at_l2(game)
    core_matches_gstar(game)
    return True


# ------------------------------------------------------------ the variants


def gstar_baseline(cfg: Cfg) -> None:
    for timing in ("T1", "T2"):
        game = Game(replace(cfg, timing=timing))
        n = core_matches_gstar(game)
        assert n == 2 * 3 * 4 ** 2 * 2 * 1  # classes x types x answer vertices
        assert solve(game) is None  # negative control: no uniform preserving assessment


def informed_retry(cfg: Cfg, **extra):
    game = Game(replace(cfg, timing="T1", retry=True, **extra))
    return solve(game), game


def talk_pref(iset, acts):
    """Ties: wait at L1; after a dropped late opening type A talks 1, B talks
    0, C reports v (talk1 for v = 1)."""
    if iset[0] == "S" and iset[2][0] == "L1" and iset[2][1] != "after P":
        return sorted(acts, key=WAIT_FIRST.index)
    if iset[0] == "S" and iset[2][0] == "post" and iset[2][2] == "fail" and iset[2][1]:
        t = iset[1]
        want = {"A": "talk1", "B": "talk0", "C": f"talk{t[0]}"}[t[1]]
        return sorted(acts, key=lambda a: (a != want, SENDER_ORDER.index(a)))
    return default_pref(iset, acts)


def post_talk(cfg: Cfg, **extra):
    game = Game(replace(cfg, post=True, **extra))
    return solve(game, talk_pref), game


def signal_thresholds(cfg: Cfg):
    """Pre-charge signals at L1: (domination certified, face/chain range)."""
    game = Game(replace(cfg, sig_p=True, sig_l1=True))
    dominated = not extras_certificate(game)
    face_chain = cfg.c < cfg.q * cfg.r / 2 - (1 - cfg.q) * cfg.d
    return dominated, face_chain


def signal_face_deviation(cfg: Cfg) -> None:
    """Face/chain argument, last step: if the listener guesses at the success
    site of a signal-then-L2 plan, the better of types (v, A), (v, B) gains
    over the protected opening by that plan, whatever the failure answer,
    iff c < qR/2 - (1 - q)D (their average is independent of that answer)."""
    game = Game(replace(cfg, sig_p=True, sig_l1=True))

    def rule(key):
        if key[0] == "P":
            return "wait"
        if key[0] == "L1":
            return "sig0"
        if key[0] == "L2":
            return "open"
        return "quiet"

    bound = cfg.q * cfg.r / 2 - (1 - cfg.q) * cfg.d
    for v in (0, 1):
        succ = f"ans|mid=L1:sig0|res=ok:end:1|v={v}"
        fail = "ans|mid=L1:sig0|res=fail"
        avgs = set()
        for theta in FAILURE:
            lbeh = {k[1]: {game.actions[k][0]: F(1)} for k in game.actions if k[0] == "L"}
            lbeh[succ], lbeh[fail] = {"gA": F(1)}, {theta: F(1)}
            va = plan_value(game.trees[(v, "A")], rule, lbeh)
            vb = plan_value(game.trees[(v, "B")], rule, lbeh)
            avgs.add((va + vb) / 2)
        assert len(avgs) == 1
        avg = avgs.pop()
        assert avg == cfg.q * cfg.r + (1 - cfg.q) * (cfg.r / 2 - cfg.d) - cfg.c
        assert (avg > cfg.r / 2) == (cfg.c < bound)


def jam_threshold(cfg: Cfg) -> F:
    """Listener jams a pending late opening iff c_L <= (3/5)(q - q/(1+q))."""
    return F(3, 5) * (cfg.q - cfg.q / (1 + cfg.q))


def jam_gain_identity(cfg: Cfg) -> None:
    """At the listener's mid activation after seeing a pending L1 opening, the
    gain of jamming over staying quiet is (q - q_J)(1 - s) - c_L, where s is the
    listener's value at the (equal-belief) success sites and q_J = q/(1+q).
    Checked at random beliefs and every answer, in T1 and T2 (no retries)."""
    rng = random.Random(3)
    for timing in ("T1", "T2"):
        game = Game(replace(cfg, timing=timing, listener="jam"))
        pinned = pinned_answers(game)
        qj = cfg.q / (1 + cfg.q)
        for v in (0, 1):
            key = ("L", f"mid|open{v}")
            mem = game.members[key]
            for a in SUCCESS:
                lbeh = {}
                for k in game.actions:
                    if k[0] == "L":
                        acts = game.actions[k]
                        lbeh[k[1]] = {a if a in acts else acts[0]: F(1)}
                for _ in range(5):
                    raw = [F(rng.randint(1, 50)) for _ in mem]
                    mu = {m[0]: x / sum(raw) for m, x in zip(mem, raw)}
                    s = sum(mu[t] * listener_u(a, t) for t in mu)

                    def lval(node):
                        k = node[0]
                        if k == "T":
                            return node[3]
                        if k == "C":
                            return sum(p * lval(ch) for p, ch in node[1])
                        if k == "S":
                            return lval(node[2]["wait"])
                        if all(ch[0] == "T" for ch in node[2].values()):
                            pin = pinned.get(node[1])
                            return lval(node[2][pin if pin else next(iter(lbeh[node[1]]))])
                        return lval(node[2][next(iter(lbeh[node[1]]))])

                    jam = sum(mu[t] * lval(node[2]["pkt"]) for t, _, node in mem)
                    quiet = sum(mu[t] * lval(node[2]["quiet"]) for t, _, node in mem)
                    assert jam - quiet == (cfg.q - qj) * (1 - s) - cfg.c_l, (timing, a)
    assert cfg.q - cfg.q / (1 + cfg.q) == cfg.q ** 2 / (1 + cfg.q)


def jam_pref(iset, acts):
    if iset[0] == "L" and iset[1].startswith("mid|open"):
        return sorted(acts, key=["pkt", "quiet"].index)
    if iset[0] == "S" and iset[2][0] == "L1" and iset[2][1] != "after P":
        return sorted(acts, key=WAIT_FIRST.index)
    return default_pref(iset, acts)


def jam_variant(cfg: Cfg, timing: str, c_l: F):
    game = Game(replace(cfg, timing=timing, listener="jam", c_l=c_l))
    return solve(game, jam_pref), game


# ------------------------------------------------------- the symmetric leak


def lambda_star(cfg: Cfg) -> F:
    """Above it, a face at the leaked-success site lets (v, A) gain by L1."""
    return (1 - cfg.q) * (cfg.r + 2 * (cfg.d + cfg.c)) / (cfg.q * cfg.r)


def lambda_leak_certificate(cfg: Cfg, lam: F) -> None:
    """Stateless leak with probability lam at every listener activation, T2.
    Sites: S1s(v) (L1 success, opening seen at mid), Sm(v) (success, nothing
    seen at mid: L1 unseen or L2), pinned v-known failures, Fu (nothing seen).
    Checks: (i) L1 - L2 gap = delta d + kappa e with kappa = (1-q) lam (1-lam) R
    (1 - theta) for v = 1 and (1-q) lam (1-lam) R theta for v = 0 (the G* gap
    with kappa scaled by lam(1-lam) > 0, so the G* case analysis gives opposite
    strict preferences); (ii) L2 beats never at every listener behaviour;
    (iii) the deviation through a guessing S1s site pays iff lam > lambda_star."""
    c = replace(cfg, leak=lam)
    game = Game(c)
    pinned = pinned_answers(game)
    q, r = c.q, c.r
    rho = lam * (1 - lam)
    d_vec = {"A": 1, "B": 1, "C": -1}
    for v in (0, 1):
        s1s = f"ans|mid=open{v}|res=ok:end:0|v={v}"
        sm = f"ans|mid=-|res=ok:end:0|v={v}"
        fu = "ans|mid=-|res=fail"
        for k in (s1s, sm):
            assert ("L", k) in game.actions
        for a1, a2, af in itertools.product(SUCCESS, SUCCESS, FAILURE):
            lbeh = {k[1]: {pinned.get(k[1], game.actions[k][0]): F(1)} for k in game.actions if k[0] == "L"}
            lbeh[s1s], lbeh[sm], lbeh[fu] = {a1: F(1)}, {a2: F(1)}, {af: F(1)}
            g1, g2 = F(int(a1 != "m")), F(int(a2 != "m"))
            theta = F(int(af == "f1"))
            delta = q * lam * (g1 - g2) * r / 2
            kappa = (1 - q) * rho * r * ((1 - theta) if v == 1 else theta)
            e = {"A": 1 if v == 1 else -1, "B": -1 if v == 1 else 1, "C": 0}
            for s in S_LABELS:
                t = (v, s)
                l1 = plan_value(game.trees[t], core_plan("L1"), lbeh)
                l2 = plan_value(game.trees[t], core_plan("L2"), lbeh)
                nv = plan_value(game.trees[t], core_plan("never"), lbeh)
                assert l1 - l2 == delta * d_vec[s] + kappa * e[s], (lam, v, s)
                assert l2 > nv
            if a1 != "m" and a2 == "m":
                worst = min(plan_value(game.trees[(v, "A")], core_plan("L1"),
                                       dict(lbeh, **{fu: {x: F(1)}})) for x in FAILURE)
                assert (worst > r / 2) == (lam > lambda_star(c)) or worst == r / 2


def case_lemma() -> int:
    """G* step 3 in abstract form: for kappa > 0 and any delta, the gap vectors
    (delta + kappa, delta - kappa, -delta) and (delta - kappa, delta + kappa,
    -delta) each contain a strictly positive and a strictly negative entry."""
    n = 0
    vals = [F(i, 7) for i in range(-21, 22)]
    for delta, kappa in itertools.product(vals, vals):
        if kappa <= 0:
            continue
        for g in ((delta + kappa, delta - kappa, -delta), (delta - kappa, delta + kappa, -delta)):
            assert any(x > 0 for x in g) and any(x < 0 for x in g)
            n += 1
    return n


# ----------------------------------------------------- contract on traces


def contract_checks(timing: str, author_blind: bool, q: F = F(99, 100)) -> int:
    """Explicit traces of the runtime model over all raw sender emissions
    (nothing / opening / raw signal at P, L1 and L2, also after completion),
    the listener's raw packet at its mid activation and every scheduler
    outcome. Checks AsyncTimely, Opportunity, ProtectedInclusion
    (sole-identifier, strict clock), CompletesPlay, that L1/L2 sends are late,
    BlindToLatePackets (erasure identity at every inclusion step, for every
    pending late packet), the inclusion probabilities used by the game trees,
    and that the listener answers only once the reveal completed (off path its
    mid activation is observe-only). `author_blind`: the builder includes
    event-addressed late packets of any author (allows jamming)."""
    deadline, delay, bound, ready_at = 2, 0, 1, 0
    assert delay + bound < deadline  # AsyncTimely
    assert ready_at + bound < deadline  # a clock-0 send is protected
    assert not (1 + bound < deadline)  # a clock-1 send is late (unprotected)
    w = q / (1 - q)

    def law(pending, step):
        cands = [p for p in pending if p["event"] and p["sent"] == 1 and p["fresh"] == step
                 and (p["author"] == "B" or author_blind)]
        tot = 1 + len(cands) * w
        out = {("include", p["id"]): w / tot for p in cands}
        out[("skip",)] = 1 / tot
        return out

    traces = 0
    menus = ("none", "open", "sig")
    late_steps = ("s1", "s2") if timing == "T1" else ("end", "end")
    for p_act, l1_act, l2_act, a_act in itertools.product(menus, menus, menus, ("none", "pkt")):
        serial = itertools.count()
        own_ids = []

        def packet(kind, sent, fresh, author="B"):
            pid = (author, next(serial)) if author == "B" else ("A", 0)
            if author == "B" and kind == "open":
                own_ids.append(pid)
            return {"id": pid, "author": author, "event": kind in ("open", "pkt"),
                    "kind": kind, "sent": sent, "fresh": fresh}

        # clock 0: the owner is activated while its event is ready (Opportunity)
        activations_b = [0]
        pending = [packet(p_act, 0, "s0")] if p_act != "none" else []
        ledger, completed = [], False
        for pk in list(pending):  # protected step: a clock-0 opening is included
            if pk["kind"] == "open":
                pending.remove(pk)
                ledger.append(pk)
                completed = True
        # clock 1
        assert ready_at + delay < 1 and ready_at in activations_b  # Opportunity
        if l1_act != "none":
            pending.append(packet(l1_act, 1, late_steps[0]))
        answered_at_mid = completed  # answer event ready only after completion
        if a_act == "pkt" and not completed:
            pending.append(packet("pkt", 1, late_steps[0], author="A"))
        l2_packet = packet(l2_act, 1, late_steps[1]) if l2_act != "none" else None
        branches = [(F(1), pending, ledger, completed)]
        steps = ("s1", "s2") if timing == "T1" else ("end",)
        for step in steps:
            if step != "s1":  # owner activation L2 precedes the last step
                branches = [(pr, pend + ([l2_packet] if l2_packet else []), led, comp)
                            for pr, pend, led, comp in branches]
            nxt = []
            for pr, pend, led, comp in branches:
                lw = law(pend, step)
                for pk in pend:  # BlindToLatePackets
                    if not (pk["event"] and pk["sent"] == 1):
                        continue
                    alpha = lw.get(("include", pk["id"]), F(0))
                    other = law([x for x in pend if x["id"] != pk["id"]], step)
                    assert set(other) <= set(lw)
                    for cmd, pc in lw.items():
                        if cmd != ("include", pk["id"]):
                            assert pc == (1 - alpha) * other.get(cmd, F(0)), (timing, cmd)
                for cmd, pc in lw.items():
                    pend2, led2, comp2 = list(pend), list(led), comp
                    if cmd[0] == "include":
                        pk = next(x for x in pend2 if x["id"] == cmd[1])
                        pend2.remove(pk)
                        led2.append(pk)
                        comp2 = comp2 or (pk["author"] == "B" and pk["kind"] == "open")
                    nxt.append((pr * pc, pend2, led2, comp2))
            branches = nxt
        assert sum(pr for pr, *_ in branches) == 1
        n_open_late = sum(1 for p in (l1_act, l2_act) if p == "open")
        for pr, pend, led, comp in branches:
            # clock 2, before expiry: a sole-identifier clock-0 opening has a
            # receipt once 0 + bound < 2 (it was included at the protected step)
            for pid in own_ids[:1]:
                if p_act == "open" and len(own_ids) == 1:
                    assert any(x["id"] == pid for x in led)
            traces += 1
            # expiry completes the event (CompletesPlay); the listener answers
            # now unless the protected opening completed the reveal earlier
        assert answered_at_mid == (p_act == "open")
        # inclusion law of the owner's late openings, as in the game trees
        if p_act != "open" and a_act == "none":
            ok = sum(pr for pr, _, led, _ in branches
                     if any(x["author"] == "B" and x["kind"] == "open" for x in led))
            if n_open_late == 1:
                assert ok == q
            elif n_open_late == 2:
                assert ok == (1 - (1 - q) ** 2 if timing == "T1" else 2 * q / (1 + q))
        if p_act != "open" and a_act == "pkt" and l1_act == "open" and l2_act != "open":
            ok = sum(pr for pr, _, led, _ in branches
                     if any(x["author"] == "B" and x["kind"] == "open" for x in led))
            assert ok == (q / (1 + q) if author_blind else q)
    return traces


def selective_leak_not_stateless() -> None:
    """The selective leak of G* is not a stateless ObservationRule: at the mid
    activation the pending pool [opening(B, serial 0, v)] must be shown, while
    on the hold path the dropped L2 opening is the identical message
    (B, serial 0, same payload) in the identical pool at the answer, and G*
    hides it. The symmetric rule (each pending opening seen with probability
    lam) depends only on (observer, pool)."""
    l1_opening = ("B", 0, ("open", "reveal", 1))
    l2_opening_after_hold = ("B", 0, ("open", "reveal", 1))
    assert l1_opening == l2_opening_after_hold
    selective = {("mid", (l1_opening,)): "shown", ("answer", (l2_opening_after_hold,)): "hidden"}
    assert selective[("mid", (l1_opening,))] != selective[("answer", (l2_opening_after_hold,))]


# ----------------------------------------------------------------- driver


POINTS = [  # (D, c, q) with R = 2, all inside the G* theorem's hypothesis
    (F(6), F(3), F(99, 100)),
    (F(6), F(3), F(999, 1000)),
    (F(6), F(3), F(9999, 10000)),
    (F(12), F(6), F(999, 1000)),
    (F(24), F(12), F(9999, 10000)),
    (F(12), F(3), F(99, 100)),
    (F(6), F(1), F(99, 100)),
    (F(6), F(0), F(999, 1000)),
]


def blind_retry_bound(cfg: Cfg) -> F:
    """Under T2 the double send (L1 opening, then a second opening at L2) is
    strictly dominated by the single L1 opening for every listener behaviour
    iff c exceeds this value (vertex maximum of its gain: success odds
    2q/(1+q) against q, the second packet surely charged)."""
    return (cfg.r * (1 - cfg.q / 2) + (1 - cfg.q) * cfg.d) / (1 + cfg.q)


def decide(cfg: Cfg) -> str:
    """'no' by the reduction certificate, 'SE' by a verified construction,
    '?' when neither applies."""
    if reduction_verdict(cfg):
        return "no"
    return "SE" if solve(Game(cfg)) is not None else "?"


def verdicts(cfg: Cfg, full: bool) -> dict:
    out = {}
    assert cfg.deferral_pays()
    gstar_baseline(cfg)
    out["G*"] = "no"
    # 1. retries
    beh, game = informed_retry(cfg)
    assert beh is not None
    out["informed retry (T1)"] = "SE"
    out["blind retry (T2)"] = decide(replace(cfg, retry=True))
    if full:  # exact domination threshold of the blind double send
        bnd = blind_retry_bound(cfg)
        for c, dom in ((bnd, False), (bnd + F(1, 10 ** 4), True)):
            assert (not extras_certificate(Game(replace(cfg, c=c, retry=True)))) == dom
    # 2. raw messages
    out["talk after L1 drop (T1)"] = "no" if reduction_verdict(
        replace(cfg, timing="T1", talk_l2=True)) else "?"
    beh, _ = post_talk(cfg)
    assert beh is not None
    out["talk after result (post)"] = "SE"
    if full:
        beh, _ = post_talk(cfg, alphabet=3)
        assert beh is not None
    dominated, face_chain = signal_thresholds(cfg)
    signal_face_deviation(cfg)
    if full:  # exact domination threshold of L1-time signals
        bnd = cfg.r / 2 + (1 - cfg.q) * cfg.r / cfg.q
        for c, dom in ((bnd, False), (bnd + F(1, 10 ** 5), True)):
            sig = Game(replace(cfg, c=c, sig_p=True, sig_l1=True))
            assert (not extras_certificate(sig)) == dom
    if dominated:
        assert reduction_verdict(replace(cfg, sig_p=True, sig_l1=True))
    out["pre-charge signals"] = "no" if (dominated or face_chain) else decide(
        replace(cfg, sig_p=True, sig_l1=True))
    # 4. listener packets
    out["listener messages"] = "no" if reduction_verdict(replace(cfg, listener="message")) else "?"
    thr = jam_threshold(cfg)
    if full:
        jam_gain_identity(replace(cfg, c_l=thr))
    for timing in ("T1", "T2"):
        for cl in (F(0), thr / 2, thr):
            beh, _ = jam_variant(cfg, timing, cl)
            assert beh is not None, (timing, cl)
        # just above: jamming is strictly worse at every consistent belief
        # (s >= 2/5), so the listener never jams and the message argument applies
        assert (cfg.q - cfg.q / (1 + cfg.q)) * (1 - F(2, 5)) - (thr + F(1, 10 ** 6)) < 0
    out["listener jamming"] = f"SE iff c_L <= {thr}"
    # leak
    lam_s = lambda_star(cfg)
    for lam in (F(1, 2), F(9, 10), lam_s / 2, min(lam_s + F(1, 1000), F(99, 100))):
        lambda_leak_certificate(cfg, lam)
    beh = solve(Game(replace(cfg, leak=F(1))))
    assert beh is not None  # complete observation: positive control
    out["symmetric leak (T2)"] = f"no for {lam_s} < lam < 1; SE at lam = 1"
    # combinations
    neg = replace(cfg, retry=True, sig_p=True, sig_l1=True, listener="message")
    out["combined (T2, no post)"] = decide(neg) if dominated else (
        "SE" if solve(Game(neg)) is not None else "?")
    if full:
        beh, _ = informed_retry(cfg, sig_p=True, sig_l1=True, talk_l2=True, listener="message")
        assert beh is not None
        beh, _ = post_talk(cfg, retry=True, listener="message")
        assert beh is not None
        out["combined with a restoring feature"] = "SE"
    return out


def negative_controls(cfg: Cfg) -> None:
    # without the feature, the constructions fail
    assert solve(Game(replace(cfg, timing="T1"))) is None
    assert solve(Game(cfg), talk_pref) is None
    assert jam_variant(cfg, "T1", jam_threshold(cfg) + F(1, 100))[0] is None
    # a bad completion of the informed-retry construction: tilt L2-send
    # trembles so that S2(1) is a point mass on (1, A); the listener must then
    # guess there and (1, A) deviates by deferring.
    game = Game(replace(cfg, timing="T1", retry=True))
    beh = solve(game)
    trem = {}
    for t in TYPES:
        if t != (1, "A"):
            trem[(("S", t, ("L1", ())), "wait")] = (F(1), 3)
    try:
        check_se(game, beh, trem)
        bad_ok = True
    except AssertionError:
        bad_ok = False
    assert not bad_ok


def main() -> None:
    cfg = Cfg()
    assert case_lemma() > 0
    selective_leak_not_stateless()
    for timing in ("T1", "T2"):
        for ab in (False, True):
            n = contract_checks(timing, ab)
            assert n > 0
    negative_controls(cfg)
    print("Contract: T1 and T2 schedulers (owner-only and author-blind inclusion) satisfy "
          "AsyncTimely, Opportunity, ProtectedInclusion, CompletesPlay, BlindToLatePackets")
    print("G* parameters R=2, D=6, c=3, q=99/100:")
    res = verdicts(cfg, full=True)
    for k, v in res.items():
        print(f"  {k:36} {v}")
    print("Grid (R = 2):")
    for d, c, q in POINTS[1:]:
        p = replace(cfg, d=d, c=c, q=q)
        r = verdicts(p, full=False)
        print(f"  D={d} c={c} q={q}: " + "; ".join(f"{k}: {v}" for k, v in r.items()))
    print("verdict: an informed retry, free talk reaching the listener after a dropped "
          "no-leak opening, or cheap listener jamming (author-blind builder) restore "
          "preservation; a blind double send is dominated iff c > (R(1-q/2)+(1-q)D)/(1+q) "
          "and restores it at the tested c = 0 point; above that bound, blind retries, pre-charge "
          "signals (outside a narrow window of c), talk after the leaked drop, listener "
          "messages, the contract constraints and a symmetric stateless leak "
          "(lambda above a small bound) leave the obstruction intact")


if __name__ == "__main__":
    main()
