#!/usr/bin/env python3
"""Exact test of the timed-release reveal mode under the settle-late builder
family, with the owner's quantifier order (design constants first, builder
afterwards).

Background: docs/se-schedule-generalization.md (section "Optional
timed-release mode"), docs/open-problem-late-turn-equilibria.md (section
"Timed release"), docs/runtime-features-vs-late-leak.md (section "Combined,
with a valid leak rule", script runtime_leak_combined.py, mechanized as
Vegas/Examples/LateLeak/SettleLateGame.lean).

Timed release moves the owner's decision from the reveal to the commitment:
the binding carries recovery material, a service publishes the value at the
reveal's position, and the owner has no opening action. What remains of the
late-leak game is therefore a late *commitment* game: the sender of type
(v, s) may commit at the protected turn P, or defer and commit at L1 or L2 of
the settle-late builder (one inclusion step after L2, Luce law q per fresh
commitment, blind retry), while a listener activated k times between L1 and
L2 sees a pending commitment with probability lambda per activation and every
other pending packet surely. A never-included binding is a public binding
omission (charge c) and a failed reveal (forfeit D).

Three readings of the material, chosen by the schedule constants:
- sealed: a dropped commitment tells the listener only that a binding was
  pending; the listener never learns v after a failure;
- recoverable at the answer: a dropped commitment seen at some activation can
  be force-opened before the listener's failure answer;
- recoverable at the mid activation: already the observe-only activation
  recovers the value (this is the mechanized settle-late game verbatim, with
  "commit" for "open"; the script checks the deferral subtrees coincide).
The schedule bookkeeping (`schedule_bookkeeping`) says which reading a given
privacy delay t, recovery bound T (t <= T) and failure resolution produce.

Owner opening packets stay available as raw packets: on the protected path
the owner has `after_p` activations before the listener's first activation
(a junk signal and then an opening, the P2 bundle), and after a late
commitment it may add an opening at L2 (verifiable where the listener saw or
sees the commitment). Two escrows: capped (one charge c per owner, the
current design: an opening after a charged packet or after a drop is free)
and per-packet (c per signal, drop or omission, c' per opening, total capped
by the deposit). The interim extension gives the listener an action y at its
first activation (listener gets [y = v], sender g[y = y1]).

Method (exact fractions, every claim an assert): the engine of
runtime_features_late_leak.py (Kreps-Wilson consistency by fully mixed
polynomial families with type- and node-dependent trembles, one-shot
rationality under perfect recall, intended law on path). Positive verdicts
are explicit assessments passing `check_se`, found by best-reply iteration,
if needed after pruning first raw packets whose best conceivable value is at
most the node's equilibrium value (verified exactly; see `uniform_se` for
why such a subtree glues in). Negative verdicts port the
five-premise certificate of runtime_leak_combined.py (extras dominated, L2
beats never, the gap identity in the listener's whole behaviour, the site
structure, the deviations on a face) to the commitment game, with the exact
escape analysis over the uninformative failure answer. Negative controls:
the sealed construction is rejected in the recoverable variants, and the
bundles that defeat preservation below a threshold survive at it.

Run: python scripts/experiments/timed_release_settle_late_probe.py
"""

from __future__ import annotations

import itertools
import sys
from dataclasses import dataclass, replace
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import runtime_features_late_leak as rf  # noqa: E402
import runtime_leak_combined as rlc  # noqa: E402

TYPES, S_LABELS = rf.TYPES, rf.S_LABELS
SUCCESS, FAILURE = rf.SUCCESS, rf.FAILURE
GUESSES = ("gA", "gB", "gC")
SENDER_PREF = ["commit", "wait", "retry", "open", "sig0", "sig1", "sig2"]
LISTENER_PREF = ["m", "f0", "f1", "gA", "gB", "gC", "y0+quiet", "quiet", "y0", "y0+pkt",
                 "pkt", "y1+quiet", "y1", "y1+pkt"]


@dataclass(frozen=True)
class Timed:
    r: F = F(2)
    d: F = F(6)
    c: F = F(3)
    q: F = F(99, 100)
    lam: F = F(1, 2)
    k: int = 1
    escrow: str = "capped"  # or "per-packet"
    c_open: F = F(3)  # c', the per-packet charge of an owner opening packet
    deposit: F | None = None  # per-packet total cap (None: unbounded)
    recover: str | None = None  # None (sealed), "answer", "mid"
    interim: bool = False
    g: F = F(0)
    retry: bool = True
    signals: bool = True
    alphabet: int = 2
    listener: bool = True
    c_l: F = F(1, 10)
    late_open: bool = True  # owner opening packet at L2 after a late commitment
    early_open: bool = True  # owner opening packets after the protected commitment
    after_p: int = 1  # owner activations between P and the listener's first one
    omission_charged: bool = True  # a never-sent binding is a charged omission

    def alpha(self) -> F:
        return 1 - (1 - self.lam) ** self.k

    def a_known(self) -> F:
        al = self.alpha()
        return al + (1 - al) * self.lam

    def deferral_pays(self) -> bool:
        return rf.Cfg(r=self.r, d=self.d, c=self.c, q=self.q).deferral_pays()


def own_label(e) -> str:
    act, kind, x = e
    return f"{act}:{kind}" + ("" if x is None else str(x))


def hist_str(hist) -> str:
    return ";".join(f"{o}/{a}" if a else o for o, a in hist) or "start"


class TimedBuilder:
    """Per-type trees in the node format of runtime_features_late_leak:
    ("S", key, {a: child}), ("L", key, {a: child}), ("C", [(p, child)]),
    ("T", label, u_sender, u_listener). An emission is (activation, kind, x)
    with kind in commit / sig / open; its serial is its index."""

    def __init__(self, cfg: Timed):
        self.cfg = cfg
        self.w = cfg.q / (1 - cfg.q)

    def trees(self) -> dict:
        return {t: self.root(t) for t in TYPES}

    def sig_actions(self):
        return [f"sig{x}" for x in range(self.cfg.alphabet)] if self.cfg.signals else []

    def root(self, t):
        acts = {"commit": self.after_p(t, (("P", "commit", None),), 1),
                "wait": self.l1(t, ())}
        for x, a in enumerate(self.sig_actions()):
            acts[a] = self.l1(t, (("P", "sig", x),))
        return ("S", ("P",), acts)

    # ---- protected path: owner activations, then the listener's, then L2

    def after_p(self, t, em, i):
        cfg = self.cfg
        if i > cfg.after_p:
            return self.mid(t, em, 1, (), False, ())
        acts = {"wait": self.after_p(t, em, i + 1)}
        for x, a in enumerate(self.sig_actions()):
            acts[a] = self.after_p(t, em + ((f"AP{i}", "sig", x),), i + 1)
        if cfg.early_open and not any(k == "open" for _, k, _ in em):
            acts["open"] = self.after_p(t, em + ((f"AP{i}", "open", t[0]),), i + 1)
        return ("S", (f"AP{i}", tuple(own_label(e) for e in em)), acts)

    # ---- deferral path

    def l1(self, t, em):
        acts = {"commit": self.mid(t, em + (("L1", "commit", None),), 1, (), False, ()),
                "wait": self.mid(t, em, 1, (), False, ())}
        for x, a in enumerate(self.sig_actions()):
            acts[a] = self.mid(t, em + (("L1", "sig", x),), 1, (), False, ())
        return ("S", ("L1", tuple(own_label(e) for e in em)), acts)

    @staticmethod
    def ledger(em):
        """Serial of the protected commitment, if any (included at clock 0)."""
        for i, (act, kind, _) in enumerate(em):
            if act == "P" and kind == "commit":
                return i
        return None

    def mid(self, t, em, i, hist, seen, lpk):
        """Observe-only activation i of the listener (1 <= i <= k)."""
        cfg = self.cfg
        if i > cfg.k:
            return self.l2(t, {"em": em, "hist": hist, "seen": seen, "lpk": lpk})
        led = self.ledger(em)
        pending_commit = led is None and any(k == "commit" for _, k, _ in em)
        new_raw = ([own_label(e) for e in em if e[1] != "commit"] if i == 1 else [])
        opened = any(k == "open" for _, k, _ in em)

        def after(saw):
            label = f"open{t[0]}" if cfg.recover == "mid" else "bind"
            obs = ",".join(new_raw + ([label] if saw else [])) or "-"
            seen2 = seen or saw
            key = f"mid{i}|{hist_str(hist)}|{obs}"
            if led is not None:
                key += f"|led={led}"
            if opened and led is not None:  # an opening of a ledger commitment is verifiable
                key += f"|v={t[0]}"
            acts = []
            if cfg.interim and i == 1:
                acts = ["y0", "y1"]
            if cfg.listener:
                acts = [f"{y}+{p}" for y in acts for p in ("quiet", "pkt")] if acts else ["quiet", "pkt"]
            if not acts:
                return self.mid(t, em, i + 1, hist + ((obs, None),), seen2, lpk)
            return ("L", key, {a: self.mid(t, em, i + 1, hist + ((obs, a),), seen2, lpk + (a,))
                               for a in acts})

        if pending_commit and not seen:
            if cfg.lam == 1:
                return after(True)
            return ("C", [(cfg.lam, after(True)), (1 - cfg.lam, after(False))])
        return after(False)

    def l2(self, t, st):
        cfg = self.cfg
        em = st["em"]
        led = self.ledger(em)
        committed = any(k == "commit" for _, k, _ in em)
        opened = any(k == "open" for _, k, _ in em)
        # the sender sees the listener's packets, not its interim action
        seen_lp = tuple("pkt" if a.endswith("pkt") else "quiet" for a in st["lpk"]) if cfg.listener else None
        key = ("L2", tuple(own_label(e) for e in em), seen_lp)
        acts = {"wait": self.end(t, st)}
        if not committed:
            acts["commit"] = self.end(t, dict(st, em=em + (("L2", "commit", None),)))
        elif led is None and cfg.retry:
            acts["retry"] = self.end(t, dict(st, em=em + (("L2", "commit", None),)))
        for x, a in enumerate(self.sig_actions()):
            acts[a] = self.end(t, dict(st, em=em + (("L2", "sig", x),)))
        if committed and not opened and (cfg.late_open if led is None else cfg.early_open):
            acts["open"] = self.end(t, dict(st, em=em + (("L2", "open", t[0]),)))
        return ("S", key, acts)

    def end(self, t, st):
        """The one late inclusion step: Luce law over the fresh commitments;
        a protected commitment is already on the ledger."""
        em = st["em"]
        led = self.ledger(em)
        if led is not None:
            return self.answer(t, st, led)
        fresh = [i for i, (_, k, _) in enumerate(em) if k == "commit"]
        if not fresh:
            return self.answer(t, st, None)
        tot = 1 + len(fresh) * self.w
        out = [(self.w / tot, self.answer(t, st, i)) for i in fresh]
        out.append((1 / tot, self.answer(t, st, None)))
        return ("C", out)

    def charge(self, em, inc) -> F:
        cfg = self.cfg
        items = []
        for i, (_, kind, _) in enumerate(em):
            if kind == "sig":
                items.append(cfg.c)
            elif kind == "open":
                items.append(cfg.c_open if cfg.escrow == "per-packet" else cfg.c)
            elif kind == "commit" and i != inc:
                items.append(cfg.c)
        if not any(k == "commit" for _, k, _ in em) and cfg.omission_charged:
            items.append(cfg.c)
        if cfg.escrow == "capped":
            return cfg.c if items else F(0)
        total = sum(items, F(0))
        return total if cfg.deposit is None else min(total, cfg.deposit)

    def answer(self, t, st, inc):
        cfg = self.cfg
        v = t[0]
        em = st["em"]
        success = inc is not None
        dropped = [i for i, (_, k, _) in enumerate(em) if k == "commit" and i != inc]
        pen = self.charge(em, inc) + (F(0) if success else cfg.d)
        late_raw = [own_label(e) for e in em if e[1] != "commit" and e[0] == "L2"]
        opened = any(k == "open" for _, k, _ in em)
        # pending commitments the listener has not seen: each seen with probability lam now
        fresh_view = [i for i in dropped if not (em[i][0] == "L1" and st["seen"])]
        res = f"ok:{inc}" if success else "fail"
        lpen = cfg.c_l if any(a.endswith("pkt") for a in st["lpk"]) else F(0)
        y1 = any(a.startswith("y1") for a in st["lpk"])
        intended = (self.ledger(em) is not None and all(k == "commit" for _, k, _ in em)
                    and not y1)

        def node(seen_now):
            seen_any = st["seen"] or bool(seen_now)
            known = success or (cfg.recover is not None and seen_any) or (opened and seen_any)
            parts = [f"h={hist_str(st['hist'])}", f"res={res}"]
            if seen_now:
                parts.append("late=" + ",".join(map(str, seen_now)))
            if late_raw:
                parts.append("sig=" + ",".join(late_raw))
            if known:
                parts.append(f"v={v}")
            elif opened:
                parts.append(f"claim={v}")
            menu = SUCCESS if success else FAILURE
            label = "P" if intended else "dev"
            return ("L", "ans|" + "|".join(parts),
                    {a: ("T", (label, a), rf.sender_base(a, t, cfg.r) - pen + (cfg.g if y1 else 0),
                          rf.listener_u(a, t) - lpen + (int(y1 == (v == 1)) if cfg.interim else 0))
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
    """The engine interface of runtime_features_late_leak.Game."""

    def __init__(self, cfg: Timed, trees=None):
        self.cfg = cfg
        self.trees = trees or TimedBuilder(cfg).trees()
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


# ------------------------------------------- cross-check with the mechanized game


def canon(node, ren):
    """Structure of a tree with keys, actions and labels renamed by `ren`."""
    k = node[0]
    if k == "T":
        return ("T", node[2], node[3])
    if k == "C":
        return ("C", tuple((p, canon(ch, ren)) for p, ch in node[1]))
    key = ren(node[1]) if isinstance(node[1], str) else tuple(
        ren(x) if isinstance(x, str) else tuple(ren(y) for y in x) if isinstance(x, tuple) else x
        for x in node[1])
    return (k, key, tuple(sorted((ren(a), canon(ch, ren)) for a, ch in node[2].items())))


def rlc_rename(s: str) -> str:
    return s.replace("L1:open", "L1:commit").replace("L2:open", "L2:commit") if s != "open" else "commit"


def deferral_subtrees_match_combined(cfg: Timed) -> int:
    """With recovery at the mid activation, no owner opening packet and the
    uncharged never of runtime_leak_combined, the subtrees after a silent or
    signalling deferral coincide with the combined game's (same keys up to
    commit/open, same chance laws, same payoffs). The protected path differs:
    there the listener's activations are observe-only until the release."""
    mine = TimedBuilder(replace(cfg, recover="mid", late_open=False, early_open=False,
                                omission_charged=False)).trees()
    theirs = rlc.ComboBuilder(rlc.Combo(r=cfg.r, d=cfg.d, c=cfg.c, q=cfg.q, lam=cfg.lam, k=cfg.k,
                                        retry=cfg.retry, signals=cfg.signals,
                                        alphabet=cfg.alphabet, listener=cfg.listener,
                                        c_l=cfg.c_l)).trees()
    n = 0
    for t in TYPES:
        for a in ("wait", "sig0", "sig1"):
            if a in mine[t][2]:
                assert canon(mine[t][2][a], lambda s: s) == canon(theirs[t][2][a], rlc_rename), (t, a)
                n += 1
    return n


# ----------------------------------------------------------- the certificate
# Port of runtime_leak_combined's five premises to the commitment game.


def core_rule(name):
    """Core plans: commit at P, at L1, at L2, or never."""
    def rule(key):
        if key[0] == "P":
            return "commit" if name == "P" else "wait"
        if key[0] == "L1":
            return "commit" if name == "L1" else "wait"
        if key[0] == "L2":
            committed = any(x.endswith(":commit") for x in key[1])
            return "commit" if (name == "L2" and not committed) else "wait"
        return "wait"
    return rule


def continuation_rule(key):
    if key[0] == "L2":
        return "wait" if any(x.endswith(":commit") for x in key[1]) else "commit"
    raise AssertionError(key)


def silent_sender_isets(game):
    out = {}
    for iset, mem in game.members.items():
        if iset[0] != "S":
            continue
        key = iset[2]
        if key[0] == "L1" and key[1] == ():
            out[iset] = mem
        if key[0] == "L2" and key[1] in ((), ("L1:commit",)):
            out[iset] = mem
    return out


def p1_extras_dominated(game) -> list:
    pinned = rf.pinned_answers(game)
    fails = []
    for iset, mem in silent_sender_isets(game).items():
        key = iset[2]
        for a in game.actions[iset]:
            if a in ("commit", "wait"):
                continue
            ok = False
            for b in ("commit", "wait"):
                if b not in game.actions[iset]:
                    continue
                if all(rf.ub(node[2][a], pinned) < rlc.lb_rule(node[2][b], continuation_rule, pinned)
                       for _, _, node in mem):
                    ok = True
                    break
                if key[0] == "L2" and all(rlc.exact_affine_margin(node[2][b], node[2][a], pinned) > 0
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
                assert rf.ub(node[2]["wait"], pinned) < rlc.lb_rule(node[2]["commit"], continuation_rule, pinned)
                n += 1
    assert n > 0


def p3_gap_identity(game) -> int:
    """L1 minus L2 as a polynomial identity in the listener's whole
    behaviour: d-direction plus kappa times e-direction with
    kappa_1 = K(1 - theta), kappa_0 = K theta, K = (1-q) alpha (1-lam) R."""
    cfg = game.cfg
    pinned = rf.pinned_answers(game)
    big_k = (1 - cfg.q) * cfg.alpha() * (1 - cfg.lam) * cfg.r
    thetas, gaps = [], {}
    for t in TYPES:
        root = game.trees[t]
        l1 = rlc.plan_poly(root, core_rule("L1"), pinned)
        l2 = rlc.plan_poly(root, core_rule("L2"), pinned)
        gaps[t] = rlc.mp_add(l1, rlc.mp_scale(l2, -1))
        thetas.append(rlc.mp_scale(rlc.f1_weight_poly(root, core_rule("L2"), pinned),
                                   1 / ((1 - cfg.q) * (1 - cfg.lam))))
    theta = thetas[0]
    assert all(th == theta for th in thetas)
    one = rlc.mp((1, ()))
    for v in (0, 1):
        ga, gb, gc = (gaps[(v, s)] for s in S_LABELS)
        assert rlc.mp_add(gc, rlc.mp_scale(rlc.mp_add(ga, gb), F(1, 2))) == {}
        kappa = rlc.mp_scale(rlc.mp_add(ga, rlc.mp_scale(gb, -1)), F(1, 2) if v == 1 else F(-1, 2))
        want = rlc.mp_scale(rlc.mp_add(one, rlc.mp_scale(theta, -1)), big_k) if v == 1 else rlc.mp_scale(theta, big_k)
        assert kappa == want, v
    assert big_k > 0
    return sum(len(g) for g in gaps.values())


def site_families(game):
    """S1s(v): success sites of the L1 plan where the commitment was seen at
    a mid activation; Sm(v): success sites of the L2 plan."""
    s1s, sm = {}, {}
    seen_labels = ("bind", "open0", "open1")
    for v in (0, 1):
        t = (v, "A")
        l1 = rlc.reach_sites(game.trees[t], core_rule("L1"), set())
        l2 = rlc.reach_sites(game.trees[t], core_rule("L2"), set())
        succ1 = {k for k in l1 if "res=ok" in k}
        s1s[v] = {k for k in succ1 if any(x in k.split("|res=")[0] for x in seen_labels)}
        sm[v] = {k for k in l2 if "res=ok" in k}
        assert s1s[v] and sm[v] and not (s1s[v] & sm[v])
        assert succ1 - s1s[v] <= sm[v], "an unseen L1 success shares the L2 site"
        for s in S_LABELS:
            assert rlc.reach_sites(game.trees[(v, s)], core_rule("L1"), set()) == l1
            assert rlc.reach_sites(game.trees[(v, s)], core_rule("L2"), set()) == l2
    return s1s, sm


def p4_structure(game, s1s, sm) -> bool:
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
            if node[1] in targets and (p_act, l1_act) != ("wait", "commit"):
                ok = False
            for ch in node[2].values():
                go(ch, p_act, l1_act)
            return
        key = node[1]
        for a, ch in node[2].items():
            if key == ("P",):
                go(ch, a, l1_act)
            elif key[0] == "L1":
                go(ch, p_act, a)
            else:
                go(ch, p_act, l1_act)

    for t in TYPES:
        go(game.trees[t], None, None)
    for iset, mem in game.members.items():
        if iset[0] == "L" and iset[1].startswith("ans|h="):
            assert all(m[2][1] == iset[1] for m in mem)
    return ok


def deviation_values(game, s1s, sm):
    pinned = rf.pinned_answers(game)
    out = {}
    for v in (0, 1):
        better = (v, "A") if v == 1 else (v, "B")
        f1 = {k: list(GUESSES) for k in s1s[v]}
        out[("S1s", v)] = rlc.lb_rule(game.trees[better], core_rule("L1"), pinned, f1)
        fm = {k: list(GUESSES) for k in sm[v]}
        out[("Sm", v)] = rlc.lb_rule(game.trees[(v, "A")], core_rule("L2"), pinned, fm)
    return out


def dev_formula(cfg: Timed, w: F) -> F:
    return rlc.dev_formula(rlc.Combo(r=cfg.r, d=cfg.d, c=cfg.c, q=cfg.q, lam=cfg.lam, k=cfg.k), w)


def escape_weight(cfg: Timed) -> F:
    combo = rlc.Combo(r=cfg.r, d=cfg.d, c=cfg.c, q=cfg.q, lam=cfg.lam, k=cfg.k)
    rlc.escape_weight_check(combo)
    return rlc.escape_weight(combo)


def certificate(cfg: Timed, game=None) -> dict:
    """`no_se` is True iff the extended argument applies: no SE of the
    recoverable commitment game has the intended outcome."""
    assert cfg.recover in ("answer", "mid")
    game = game or TreeGame(cfg)
    out = {"deferral_pays": cfg.deferral_pays(), "p1_fails": p1_extras_dominated(game)}
    p2_send_beats_never(game)
    out["p3_terms"] = p3_gap_identity(game) if cfg.lam < 1 else None
    s1s, sm = site_families(game)
    out["p4"] = p4_structure(game, s1s, sm)
    dev = deviation_values(game, s1s, sm)
    half = cfg.r / 2
    for v in (0, 1):
        assert dev[("S1s", v)] == dev_formula(cfg, cfg.a_known())
        assert dev[("Sm", v)] > half
    out["escape_value"] = dev_formula(cfg, escape_weight(cfg))
    out["no_se"] = (out["deferral_pays"] and not out["p1_fails"] and out["p4"]
                    and cfg.lam < 1 and out["escape_value"] > half)
    return out


# --------------------------------------------------------- constructions


def pref(iset, acts):
    order = SENDER_PREF if iset[0] == "S" else LISTENER_PREF
    return sorted(acts, key=order.index)


def is_raw(a: str) -> bool:
    return a.startswith("sig") or a == "open"


def prune(node, drop: set, path=()):
    """The tree without the sender actions in `drop` (pairs path, action)."""
    k = node[0]
    if k == "T":
        return node
    if k == "C":
        return ("C", [(p, prune(ch, drop, path + (i,))) for i, (p, ch) in enumerate(node[1])])
    acts = {a: prune(ch, drop, path + (a,)) for a, ch in node[2].items()
            if not (k == "S" and (path, a) in drop)}
    return (k, node[1], acts)


def first_raw_actions(game) -> dict:
    """type -> {(path, action)}: raw packets (junk signals, owner openings)
    at nodes where the sender has emitted no forbidden packet yet."""
    out = {}
    for t, root in game.trees.items():
        for path, node in rf.iter_nodes(root):
            if node[0] == "S" and not any(isinstance(a, str) and is_raw(a) for a in path):
                for a in node[2]:
                    if is_raw(a):
                        out.setdefault(t, set()).add((path, a))
    return out


def uniform_se(cfg: Timed, game=None, rounds=200, pruning=True):
    """Best-reply iteration from the L1 plan with type-independent trembles;
    a result is check_se-verified (None proves nothing).

    With `pruning`, the sender's first raw packets (junk signals, owner
    openings sent before any charge) are removed first; each removed action
    is then checked to be weakly dominated at its node: the best value of
    its subtree over every listener behaviour (information sets relaxed) is
    at most the verified SE's value of the node. An action that fails the
    check is put back, for every type, and the game re-solved. A raw packet
    is seen at the listener's next activation, so its subtree's listener
    sites are reached only through it; an SE of that subtree game (which
    exists, the subtree being a finite game with the sender's type drawn from
    the prior) glued under a type-independent entry tremble gives an SE of
    the full game with the same path, the pruned action being no better than
    the node's SE value. Under the capped escrow the charge is sunk inside
    these subtrees, so later packets are free talk there and the pure
    best-reply iteration need not settle; nothing on the path depends on
    them."""
    game = game or TreeGame(cfg)
    beh = rf.solve(game, pref, rounds=rounds)
    if beh is not None or not pruning:
        return beh, game
    drop = first_raw_actions(game)
    pinned = rf.pinned_answers(game)
    for _ in range(8):
        pruned = TreeGame(cfg, {t: prune(root, drop.get(t, set())) for t, root in game.trees.items()})
        beh = rf.solve(pruned, pref, rounds=rounds)
        if beh is None:
            return None, game
        vals = rf.values(pruned, beh)
        kept = set()  # an action is put back for every type at once
        for t, pairs in drop.items():
            for path, a in pairs:
                child = game.trees[t]
                for step in path:
                    child = child[2][step] if child[0] in ("S", "L") else child[1][step][1]
                if not rf.ub(child[2][a], pinned) <= vals[(t, path)][0]:
                    kept.add((path, a))
        if not kept:
            return beh, game
        drop = {t: pairs - kept for t, pairs in drop.items()}
    return None, game


def rejected(fn) -> bool:
    try:
        fn()
    except AssertionError:
        return True
    return False


# ------------------------------------------------------ schedule bookkeeping


def schedule_bookkeeping(t: F, big_t: F, tau0: F, tau1: F, beta: F, delta_a: F,
                         mid: F, horizon_f: F, failure_at_release: bool) -> dict:
    """Which reading of the material a schedule produces. tau0: protected
    turn; tau1: first late turn; beta: binding deadline (the late inclusion
    step); delta_a: the listener's answer deadline after readiness; mid: the
    listener's observe-only activation; horizon_f: end of the failure
    continuation after a fail-fast failure; t: privacy delay (an adversary
    recovers nothing before first transmission + t); T >= t: recovery bound
    (the service's forced opening finishes within T of inclusion). The
    release lands at beta + T; the failure answer at beta + T + delta_a if
    the reveal fails at the release position, else within [beta, horizon_f]."""
    assert t <= big_t and tau0 < tau1 < mid < beta <= horizon_f
    release = beta + big_t
    out = {"release": release}
    # success branch: decisions whose source counterpart precedes the reveal
    # (the mid activation) must come before the earliest material + t
    out["interim_sealed"] = mid < tau0 + t
    # failure branch: a late commitment first transmitted at tau1
    last_failure_decision = release + delta_a if failure_at_release else horizon_f
    out["recover"] = (None if last_failure_decision < tau1 + t
                      else "mid" if mid >= tau1 + t else "answer")
    return out


# ------------------------------------------------------------------ driver


def interim_necessity(cfg: Timed) -> bool:
    """If the cheapest verifiable early opening costs less than g, no SE has
    the intended outcome: on path the interim belief is the prior (y0
    strictly best), after a verifiable opening of the protected commitment
    y = v is forced, every final answer gives (1, A) at least R/2, and
    (1, A) keeps its path value otherwise. Capped escrow: the opening is the
    one charge c. Per-packet: min(c', deposit)."""
    on_path = {t: rf.prior(t) for t in TYPES}
    y_vals = {y: sum(w * int(y == f"y{t[0]}") for t, w in on_path.items()) for y in ("y0", "y1")}
    assert y_vals["y0"] > y_vals["y1"]
    assert all(rf.sender_base(x, (1, "A"), cfg.r) >= cfg.r / 2 for x in SUCCESS)
    cheapest = cfg.c if cfg.escrow == "capped" else (
        cfg.c_open if cfg.deposit is None else min(cfg.c_open, cfg.deposit))
    return cfg.g - cheapest > 0


def disclosure_window(cfg: Timed) -> dict:
    """Capped escrow, late opening after an L1 commitment: the charge is
    sunk when the commitment is dropped, so the opening's expected charge is
    q c against a failure gain of at most (1 - q) a R (the failure answer's
    swing R times the probability a that the listener saw the commitment).
    Deferral itself pays only above q_defer = (D + c + R/2)/(D + c + R). The
    uninformative failure answer theta can keep both (1, A) and (0, B) from
    disclosing iff q c / ((1 - q) a R) >= 1/2."""
    r, d, c, q, a = cfg.r, cfg.d, cfg.c, cfg.q, cfg.a_known()
    q_defer = (d + c + r / 2) / (d + c + r)
    # at q_defer the pure deferral q R - (1 - q)(D + c) is exactly R/2
    assert q_defer * r - (1 - q_defer) * (d + c) == r / 2
    gain_a = (1 - q) * a * r  # (1, A) under f0 at the seen failures
    return {"q_defer": q_defer, "discloses": gain_a > q * c,
            "theta_escape": q * c / ((1 - q) * a * r) >= F(1, 2),
            "window": (q > q_defer) and gain_a > q * c and q * c / ((1 - q) * a * r) < F(1, 2),
            "capped_safe_for_every_builder": c * (d + c + r / 2) >= r * r / 4}


def main() -> None:
    base = Timed()
    half = base.r / 2
    n = deferral_subtrees_match_combined(base)
    assert n == 18
    print("Cross-check: with recovery at the mid activation, the subtrees after a deferral are "
          "those of the combined (mechanized) game, commit for open (18 subtrees per feature set)")

    # ---- part 0: schedule bookkeeping (P3, P4)
    print("Part 0 (schedule): tau0=0 (P), tau1=1 (L1), mid=3/2, beta=2 (late inclusion), "
          "answer deadline 1, failure continuation ends at 3")
    sched = dict(tau0=F(0), tau1=F(1), beta=F(2), delta_a=F(1), mid=F(3, 2), horizon_f=F(3))
    for t, big_t, at_release in ((F(5), F(5), True), (F(50), F(50), True), (F(5), F(50), True),
                                 (F(5), F(5), False), (F(5), F(50), False), (F(2), F(50), False),
                                 (F(1, 4), F(50), False), (F(1), F(1), False)):
        res = schedule_bookkeeping(t, big_t, failure_at_release=at_release, **sched)
        print(f"  t={t} T={big_t} failure {'at release' if at_release else 'fail-fast'}: "
              f"release at {res['release']}, interim {'sealed' if res['interim_sealed'] else 'EXPOSED'}, "
              f"dropped material {res['recover'] or 'sealed'}")
        if at_release:
            assert res["recover"] is not None  # no constant seals a failure resolved at the release
        else:
            assert (res["recover"] is None) == (t > F(2))  # horizon_f - tau1
    assert schedule_bookkeeping(F(1, 2), F(1), failure_at_release=False, **sched)["recover"] == "mid"
    assert schedule_bookkeeping(F(1), F(1), failure_at_release=False, **sched)["recover"] == "answer"

    # ---- part 1: recoverable readings (P1): the obstruction returns
    print("Part 1 (recoverable dropped material, G* margins R=2, D=6, c=3, q=99/100, lam=1/2, k=1):")
    for recover in ("answer", "mid"):
        for escrow in ("capped", "per-packet"):
            cfg = replace(base, recover=recover, escrow=escrow)
            game = TreeGame(cfg)
            res = certificate(cfg, game)
            assert res["no_se"] and not res["p1_fails"] and res["p4"], (recover, escrow, res)
            beh, _ = uniform_se(cfg, game)
            assert beh is None  # negative control: the sealed construction does not survive
            print(f"  recover at {recover:6} {escrow:10}: no preserving SE "
                  f"(escape value {res['escape_value']} > R/2); best-reply iteration finds none")
    # fixed margins, builder afterwards: q -> 1 for every D > R, c > R/2
    print("  margins first, builder afterwards (lam = 1/2, k = 1, recover at answer):")
    for d, c in ((F(3), F(11, 10)), (F(6), F(3)), (F(60), F(30)), (F(21, 10), F(1001, 1000))):
        found = None
        for nn in range(1, 6):
            q = 1 - F(1, 10 ** nn)
            cfg = replace(base, d=d, c=c, q=q, recover="answer")
            if not cfg.deferral_pays():
                continue
            res = certificate(cfg)
            if res["no_se"]:
                found = q
                break
        assert found is not None, (d, c)
        print(f"    D={d} c={c}: no preserving SE at q={found}")

    # ---- part 2: sealed material, both escrows, the builder family
    print("Part 2 (sealed material: verified preserving SE, type-independent trembles):")
    print("  escrow      D    c      q          lam   k  result")
    for escrow in ("capped", "per-packet"):
        for d, c in ((F(6), F(3)), (F(3), F(11, 10)), (F(6), F(1)), (F(60), F(30)), (F(6), F(1, 10))):
            for q, lam, k in ((F(1, 2), F(1, 2), 1), (F(9, 10), F(1, 2), 1), (F(99, 100), F(1, 2), 1),
                              (F(999, 1000), F(1, 2), 1), (F(99, 100), F(1, 20), 1),
                              (F(99, 100), F(1, 2), 2), (F(999, 1000), F(1, 20), 2)):
                cfg = replace(base, escrow=escrow, d=d, c=c, q=q, lam=lam, k=k)
                beh, _ = uniform_se(cfg)
                assert beh is not None, (escrow, d, c, q, lam, k)
                print(f"  {escrow:10} {str(d):4} {str(c):6} {str(q):10} {str(lam):5} {k}  SE")
    # the late opening after a dropped commitment: capped versus per-packet at every point above
    print("  (the owner's late opening packet and the junk signals are available at every point)")

    # ---- part 3: P2, the interim extension with a junk signal before the early opening
    print("Part 3 (interim decision at the listener's first activation, sender gets g[y = 1]; "
          "two owner activations after P: junk then opening):")
    for g in (base.r / 4, base.r / 2, base.r):
        for escrow in ("capped", "per-packet"):
            if escrow == "capped":
                points = [("c", replace(base, interim=True, g=g, after_p=2, c=g)),
                          ("c", replace(base, interim=True, g=g, after_p=2, c=g - F(1, 100)))]
            else:
                points = [("c'", replace(base, interim=True, g=g, after_p=2, escrow=escrow, c=F(3), c_open=g)),
                          ("c'", replace(base, interim=True, g=g, after_p=2, escrow=escrow, c=F(3),
                                         c_open=g - F(1, 100))),
                          ("deposit", replace(base, interim=True, g=g, after_p=2, escrow=escrow, c=F(3),
                                              c_open=F(3), deposit=g)),
                          ("deposit", replace(base, interim=True, g=g, after_p=2, escrow=escrow, c=F(3),
                                              c_open=F(3), deposit=g - F(1, 100)))]
            for name, cfg in points:
                need = interim_necessity(cfg)
                beh, _ = uniform_se(cfg, pruning=not need)
                assert (beh is not None) == (not need), (g, escrow, name)
                val = {"c": cfg.c, "c'": cfg.c_open, "deposit": cfg.deposit}[name]
                print(f"  g={g} {escrow:10} {name}={val}: "
                      f"{'SE' if beh else 'no SE (opening cheaper than g)'}")

    # ---- part 4: the capped escrow's sunk charge after a drop (late opening at L2)
    print("Part 4 (capped escrow, late opening after an L1 commitment, charge sunk by the drop):")
    for d, c in ((F(6), F(3)), (F(6), F(1)), (F(6), F(1, 5)), (F(6), F(1, 10))):
        cfg = replace(base, d=d, c=c)
        win = disclosure_window(replace(cfg, q=F(22, 25)))
        safe = win["capped_safe_for_every_builder"]
        print(f"  D={d} c={c}: q_defer={win['q_defer']}, "
              f"{'no builder of the family opens the window' if safe else 'window open for some builder'}"
              f" (c(D + c + R/2) {'>=' if safe else '<'} R^2/4)")
        for q in (F(22, 25), F(9, 10), F(99, 100)):
            w = disclosure_window(replace(cfg, q=q))
            beh, _ = uniform_se(replace(cfg, q=q), pruning=not w["window"])
            print(f"    q={q}: discloses under f0 {w['discloses']}, theta escape {w['theta_escape']}, "
                  f"window {w['window']}; uniform construction {'SE' if beh else 'fails'}")
            if not w["window"]:
                assert beh is not None or not w["discloses"]
            else:
                assert beh is None
    print("verdict: sealed timed release has a preserving SE at every tested builder under both "
          "escrows; dropped material recoverable before the failure answer is the mechanized "
          "obstruction (no constant helps once the failure is resolved at the release position); "
          "the early opening is deterred iff its cheapest charge is at least the interim gain; "
          "the capped escrow's drop-sunk late opening needs c(D + c + R/2) >= R^2/4")


if __name__ == "__main__":
    main()
