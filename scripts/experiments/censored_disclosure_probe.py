#!/usr/bin/env python3
"""Exact finite probe of risk (b): value-selective censorship of late openings.

Source game S. Chance draws Alice's private type v in {0, 1, 2} with prior
`prior`. Alice commits to v, then resolves: TRUE discloses v publicly, FALSE
(withholding, a legal source move) publishes failure. Bob then picks an action
b knowing the public result. Payoffs: after TRUE v, Alice gets reveal[v][b],
Bob gets bob[v][b]; after FALSE, Alice gets fail[v][b], Bob gets bob[v][b].
Bob's payoff depends only on the true type and his action.

Native game N (one admissible configuration). Alice may open in the protected
window ("now", always included on time, public TRUE v), or wait. After waiting
she gets exactly one post-window opportunity: "late" (send the opening) or
"silent". The builder draws c uniform on {0, ..., K-1}, hidden from Alice at
both of her decisions, and includes a late opening iff v != c. An included late
opening publishes TRUE v; a censored late opening and silence both end in
resolution expiry, i.e. source FALSE, and Bob cannot tell them apart (the
observation rule leaks no pending packet to him). Bob then learns c and acts.
Silence is uncharged; a censored late opening is a forbidden packet, charged
with audit probability rho times deposit D, modelled as the expected charge
rhoD subtracted from Alice's payoff. Bob's information sets are
(on-time TRUE v, c), (late TRUE v, c) and (silent expiry, c).

Consistency. For any fully mixed native profile, the weight of type v at
(silent expiry, c) is prior[v] * P(wait | v) * (P(silent | v, wait) +
[v = c] P(late | v, wait)) / K: Alice's choices are made without c, the builder
is not strategic, and c is independent of everything Alice does. Write a_v and
b_v for the two products. The belief mu_a at every (silent, c) with c >= 3 is
the limit of a, common to all those c; the belief mu_c at c in {0, 1, 2} is
the limit of a + b_c e_c. Hence (Lemma) if type v strictly prefers "late" at its
post-wait set (so b_v / a_v -> infinity in any consistent sequence) and
mu_a(v) > 0, then mu_v = e_v; if it strictly prefers "silent", mu_v = mu_a;
in the remaining cases mu_v lies on the segment from mu_a to e_v. Tremble
rates may depend on type and timing arbitrarily; the lemma uses only these
ratios, not monomial rates.

Preservation. The source equilibrium has every type disclose; its joint law has
no FALSE result and no charge. Any native profile in which some type waits with
positive probability produces FALSE (silence, or the censored 1/K branch of a
late opening) with positive probability, so a preserving native SE has every
type open now with probability one; then Bob's responses at the silent sets are
off path and must deter every whole waiting continuation of every type.

Games. G2 is the counterexample candidate (three Bob actions). G1 is a
two-action variant of the plan's shape in which the source belief cannot be
reproduced at every c, yet a preserving native SE exists with c-dependent
beliefs; it shows that the plan's belief argument alone is not a
counterexample. Everything is exact rational arithmetic; every claim is an
assertion. Run: python scripts/experiments/censored_disclosure_probe.py
"""

from __future__ import annotations

import random
from dataclasses import dataclass
from fractions import Fraction as F

TYPES = (0, 1, 2)


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


def leading(p: dict[int, F]) -> tuple[int, F]:
    assert p, "a fully mixed mass is never identically zero"
    e = min(p)
    assert p[e] > 0, "a mass is positive for small eps"
    return e, p[e]


def limit_belief(masses: list[dict[int, F]]) -> tuple[F, ...]:
    """Exact limit of the normalized masses as eps -> 0."""
    leads = [leading(m) for m in masses]
    e = min(x for x, _ in leads)
    weights = [c if x == e else F(0) for x, c in leads]
    total = sum(weights)
    return tuple(w / total for w in weights)


def probability_pair(chosen_first: bool, coef: F, exp: int) -> tuple[dict[int, F], dict[int, F]]:
    """A fully mixed binary choice whose limit is pure: the unchosen action has
    probability coef * eps^exp (exp > 0) and the chosen one the rest."""
    assert exp > 0 and coef > 0
    small = poly((coef, exp))
    big = poly((1, 0), (-coef, exp))
    return (big, small) if chosen_first else (small, big)


# ---------------------------------------------------------------------- games


@dataclass(frozen=True)
class Game:
    name: str
    prior: tuple[F, F, F]
    actions: tuple[str, ...]
    bob: dict[int, dict[str, F]]
    reveal: dict[int, dict[str, F]]
    fail: dict[int, dict[str, F]]

    def bob_value(self, mu: tuple[F, ...], b: str) -> F:
        return sum(mu[v] * self.bob[v][b] for v in TYPES)

    def best_responses(self, mu: tuple[F, ...]) -> set[str]:
        best = max(self.bob_value(mu, b) for b in self.actions)
        return {b for b in self.actions if self.bob_value(mu, b) == best}

    def unique_br(self, v: int) -> str:
        e = tuple(F(int(u == v)) for u in TYPES)
        brs = self.best_responses(e)
        assert len(brs) == 1, (self.name, v, brs)
        return next(iter(brs))

    def disclose_payoff(self, v: int) -> F:
        return self.reveal[v][self.unique_br(v)]

    def fail_payoff(self, v: int, beta: dict[str, F]) -> F:
        return sum(beta[b] * self.fail[v][b] for b in self.actions)

    def payoff_range(self) -> F:
        """Range of Alice's base (pre-charge) payoff over all native histories."""
        values = [t[v][b] for t in (self.reveal, self.fail) for v in TYPES for b in self.actions]
        return max(values) - min(values)


def mixed(game: Game, **weights: F) -> dict[str, F]:
    beta = {b: F(weights.get(b, 0)) for b in game.actions}
    assert all(p >= 0 for p in beta.values()) and sum(beta.values()) == 1
    return beta


def supports_br(game: Game, mu: tuple[F, ...], beta: dict[str, F]) -> bool:
    brs = game.best_responses(mu)
    return all(p == 0 or b in brs for b, p in beta.items())


THIRD = F(1, 3)

# G2: Bob's actions x, y, z. Bob: x wins against type 0 relative to y, y wins
# against types 1 and 2; z is Bob's best reply when he is sure of type 0.
# Failure payoffs make types 1 and 2 jointly pin the deterring reply to
# exactly (x: 1/2, y: 1/2, z: 0); type 0 is strictly deterred by everything.
G2 = Game(
    name="G2",
    prior=(THIRD, THIRD, THIRD),
    actions=("x", "y", "z"),
    bob={0: {"x": F(2), "y": F(0), "z": F(3)},
         1: {"x": F(0), "y": F(1), "z": F(-10)},
         2: {"x": F(0), "y": F(1), "z": F(-10)}},
    reveal={v: {b: F(0) for b in ("x", "y", "z")} for v in TYPES},
    fail={0: {"x": F(-1), "y": F(-1), "z": F(-1)},
          1: {"x": F(-1), "y": F(1), "z": F(1)},
          2: {"x": F(1), "y": F(-1), "z": F(1)}},
)

# G1: the two-action shape. x wins against type 0, y against types 1 and 2.
# Types 1 and 2 pin the deterring reply to x with probability 1/11.
G1 = Game(
    name="G1",
    prior=(THIRD, THIRD, THIRD),
    actions=("x", "y"),
    bob={0: {"x": F(1), "y": F(0)},
         1: {"x": F(0), "y": F(1)},
         2: {"x": F(0), "y": F(1)}},
    reveal={v: {b: F(0) for b in ("x", "y")} for v in TYPES},
    fail={0: {"x": F(-10), "y": F(-10)},
          1: {"x": F(-10), "y": F(1)},
          2: {"x": F(10), "y": F(-1)}},
)


# ------------------------------------------------------------- source checks


def check_source_se(game: Game, withhold_trembles: tuple[F, F, F], beta: dict[str, F]) -> tuple[F, ...]:
    """Every type discloses; Bob plays the unique best reply after TRUE v and
    `beta` after FALSE. Withholding trembles coef_v * eps (type-specific; any
    ratio is allowed since each type is its own information set) give Bob's
    belief at FALSE. Checks consistency, Bob's rationality, every type's
    rationality, and returns the belief."""
    masses = [pmul(poly((game.prior[v], 0)), poly((withhold_trembles[v], 1))) for v in TYPES]
    mu = limit_belief(masses)
    assert supports_br(game, mu, beta), (game.name, mu, beta)
    for v in TYPES:
        assert game.fail_payoff(v, beta) <= game.disclose_payoff(v), (game.name, v)
    return mu


# ------------------------------------------------------------- native checks


@dataclass(frozen=True)
class AliceTrembles:
    """Fully mixed Alice behaviour at type v whose limit is: open now; after a
    wait, play `postwait` ('late' or 'silent'). wait = wait_coef * eps^wait_exp,
    the unchosen post-wait action = off_coef * eps^off_exp."""
    wait_coef: F
    wait_exp: int
    postwait: str
    off_coef: F
    off_exp: int


def native_silent_beliefs(game: Game, k: int, trembles: dict[int, AliceTrembles]) -> list[tuple[F, ...]]:
    out = []
    for c in range(k):
        masses = []
        for v in TYPES:
            t = trembles[v]
            wait = poly((t.wait_coef, t.wait_exp))
            late, silent = probability_pair(t.postwait == "late", t.off_coef, t.off_exp)
            reach = silent if v != c else padd(silent, late)
            masses.append(pmul(pmul(poly((game.prior[v] / k, 0)), wait), reach))
        out.append(limit_belief(masses))
    return out


def waiting_values(game: Game, k: int, rho_d: F, silent_beta: list[dict[str, F]]) -> dict[int, tuple[F, F]]:
    """(silent, late) continuation values of every type after waiting. An
    included late opening (prob (k-1)/k) is answered by Bob's unique best reply
    to the revealed type; a censored one (c = v) ends in FALSE at (silent, v)
    and pays the expected charge rhoD."""
    out = {}
    for v in TYPES:
        silent = sum(game.fail_payoff(v, silent_beta[c]) for c in range(k)) / k
        late = (F(k - 1, k) * game.disclose_payoff(v)
                + F(1, k) * (game.fail_payoff(v, silent_beta[v]) - rho_d))
        out[v] = (silent, late)
    return out


def check_preserving_native_se(game: Game, k: int, rho_d: F, trembles: dict[int, AliceTrembles],
                               silent_beta: list[dict[str, F]]) -> list[tuple[F, ...]]:
    """Check one native assessment in which every type opens now: consistency
    (beliefs are exact limits of the given fully mixed family; Bob's own
    trembles do not affect his beliefs since he moves once), Bob's sequential
    rationality at every (silent, c) set, Alice's rationality at the post-wait
    sets and at the first decision against every whole waiting continuation.
    Bob's replies after TRUE (on time or late) are his unique best replies to
    the revealed type. Returns the beliefs at (silent, c)."""
    beliefs = native_silent_beliefs(game, k, trembles)
    for c in range(k):
        assert supports_br(game, beliefs[c], silent_beta[c]), (game.name, c, beliefs[c], silent_beta[c])
    values = waiting_values(game, k, rho_d, silent_beta)
    for v in TYPES:
        silent, late = values[v]
        chosen = trembles[v].postwait
        assert (late >= silent) if chosen == "late" else (silent >= late), (game.name, v, values[v])
        assert max(silent, late) <= game.disclose_payoff(v), (game.name, v, values[v])
    return beliefs


# --------------------------------------------- G2: impossibility certificate


def g2_impossibility(k: int, rho_d: F) -> None:
    """Every native SE of G2 (K = k, expected charge rho_d) changes the source
    law, when k >= 3 and rho_d < k - 1. Each step is checked exactly.

    Suppose a native SE preserves the law, so every type opens now and every
    whole waiting continuation is deterred. Let beta_c be Bob's reply at
    (silent, c) and bar = (1/k) sum_c beta_c."""
    g = G2
    assert k >= 3 and rho_d < k - 1
    # Step 1. Waiting and staying silent is deterred for types 1 and 2:
    # fail_v(bar) <= 0. The sum of the two constraint rows is 2 * bar_z, and
    # the difference fixes bar_x = bar_y; hence bar = (1/2, 1/2, 0).
    row1 = {b: g.fail[1][b] - g.disclose_payoff(1) for b in g.actions}
    row2 = {b: g.fail[2][b] - g.disclose_payoff(2) for b in g.actions}
    assert {b: row1[b] + row2[b] for b in g.actions} == {"x": 0, "y": 0, "z": 2}
    # rows are 0 on the simplex only at x = y (row1 = -x + y + z, row2 = x - y + z)
    assert row1 == {"x": -1, "y": 1, "z": 1} and row2 == {"x": 1, "y": -1, "z": 1}
    # So row1 + row2 = 2 bar_z <= 0 forces bar_z = 0, and then
    # row1 = bar_y - bar_x <= 0, row2 = bar_x - bar_y <= 0 force bar_x = bar_y = 1/2.
    bar = mixed(g, x=F(1, 2), y=F(1, 2))
    assert g.fail_payoff(1, bar) <= 0 and g.fail_payoff(2, bar) <= 0
    # Consequently beta_c(z) = 0 at every c (bar_z is an average of nonnegatives).
    # Step 2. x is a best reply only at beliefs with mu(0) >= 1/3:
    # E[x] - E[y] = 2 mu0 - (mu1 + mu2) = 3 mu0 - 1.
    for b in g.actions:
        assert g.bob[1][b] == g.bob[2][b]
    assert g.bob[0]["x"] - g.bob[0]["y"] == 2 and g.bob[1]["x"] - g.bob[1]["y"] == -1
    # Step 3. If mu_a(0) = 0 then mu_c(0) = 0 for every c != 0 (the belief at
    # c >= 3 is mu_a; at c in {1, 2} the extra mass b_c sits on type c != 0), so
    # x is played only at c = 0 and bar_x <= 1/k < 1/2. Hence mu_a(0) > 0.
    assert F(1, k) < F(1, 2)
    # Step 4. Type 0's post-wait choice: silent is worth fail_0 = -1 whatever Bob
    # does; late is worth ((k-1)/k) * 0 + (1/k) * (-1 - rho_d). Late is strictly
    # better iff rho_d < k - 1, so in every consistent sequence
    # P(late | 0, wait) / P(silent | 0, wait) -> infinity.
    assert len(set(g.fail[0].values())) == 1
    silent0 = g.fail[0]["x"]
    late0 = F(k - 1, k) * g.disclose_payoff(0) + F(1, k) * (silent0 - rho_d)
    assert late0 > silent0
    # Step 5 (Lemma). With mu_a(0) > 0 and b_0 / a_0 -> infinity, mu_0 = e_0:
    # mass(other types)/mass(type 0) at c = 0 equals
    # [(a_1 + a_2) / a_0] * [a_0 / (a_0 + b_0)] -> ((1 - mu_a0)/mu_a0) * 0 = 0.
    # Step 6. Bob's unique best reply at e_0 is z, so beta_0(z) = 1, contradicting
    # step 1. (Exhaustive over Bob's replies: z strictly beats x and y at e_0.)
    e0 = (F(1), F(0), F(0))
    assert g.best_responses(e0) == {"z"}


def lemma_spot_check(seed: int = 7, trials: int = 4000) -> int:
    """Exact check of the lemma over random type- and timing-tilted families:
    whenever type 0's limit post-wait play is late and mu_a(0) > 0, the belief
    at (silent, 0) is e_0; whenever type v's post-wait play is silent, the
    belief at (silent, v) equals mu_a."""
    rng = random.Random(seed)
    hits = 0
    for _ in range(trials):
        trembles = {
            v: AliceTrembles(F(rng.randint(1, 9), rng.randint(1, 9)), rng.randint(1, 4),
                             rng.choice(("late", "silent")),
                             F(rng.randint(1, 9), rng.randint(1, 9)), rng.randint(1, 4))
            for v in TYPES}
        beliefs = native_silent_beliefs(G2, 10, trembles)
        mu_a = beliefs[3]
        assert all(beliefs[c] == mu_a for c in range(3, 10))
        for v in TYPES:
            ev = tuple(F(int(u == v)) for u in TYPES)
            if trembles[v].postwait == "late" and mu_a[v] > 0:
                assert beliefs[v] == ev
                hits += 1
            if trembles[v].postwait == "silent":
                assert beliefs[v] == mu_a
            # in general mu_v lies on the segment [mu_a, e_v]
            t = beliefs[v]
            if t != ev:
                scale = (1 - t[v]) / (1 - mu_a[v]) if mu_a[v] != 1 else F(1)
                assert all(t[u] == scale * mu_a[u] for u in TYPES if u != v)
    return hits


# ---------------------------------------------------------------------- main


def main() -> None:
    k = 10

    # ---- G2 source SE
    beta_star = mixed(G2, x=F(1, 2), y=F(1, 2))
    mu_star = check_source_se(G2, (F(1), F(1), F(1)), beta_star)
    assert mu_star == (THIRD, THIRD, THIRD)
    assert G2.best_responses(mu_star) == {"x", "y"}
    assert [G2.unique_br(v) for v in TYPES] == ["z", "y", "y"]
    margins = [G2.disclose_payoff(v) - G2.fail_payoff(v, beta_star) for v in TYPES]
    assert margins == [1, 0, 0]
    # The deterring set of Bob replies at FALSE is the single point beta_star
    # (step 1 of the certificate), and it needs mu(0) >= 1/3 > 0.
    rng = G2.payoff_range()
    assert rng == 2
    print(f"G2 source SE: all disclose; Bob at FALSE belief {tuple(map(str, mu_star))}, "
          f"reply {{x: 1/2, y: 1/2}}; deterrence margins {list(map(str, margins))}; "
          f"Alice payoff range {rng}")

    # ---- G2 native: no preserving SE for rhoD < k - 1, including the repo's
    # asyncAuditDeposit (rho * D = payoff range = 2).
    for rho_d in (F(0), F(1), rng, F(5), F(89, 10)):
        g2_impossibility(k, rho_d)
    for kk in range(3, 31):
        g2_impossibility(kk, F(kk - 2))
    hits = lemma_spot_check()
    assert hits > 500
    print(f"G2 native, K={k}: no preserving SE for every rhoD < {k - 1} "
          f"(checked rhoD in 0, 1, 2 = range, 5, 8.9; and K in 3..30 at rhoD = K-2); "
          f"lemma spot-checked on {hits} late-type instances")

    # ---- G2 at rhoD >= k - 1: the threshold is sharp. Type 0 weakly prefers
    # silence, so it can stay silent, mu_0 = mu_a = mu_star, and Bob plays
    # beta_star everywhere.
    for rho_d in (F(k - 1), F(k), F(100)):
        trembles = {v: AliceTrembles(F(1), 1, "silent", F(1), 1) for v in TYPES}
        beliefs = check_preserving_native_se(G2, k, rho_d, trembles, [beta_star] * k)
        assert all(b == mu_star for b in beliefs)
    # Negative controls: the checker rejects the natural replicas below the
    # threshold (type 0 silent is not rational; type 0 late moves mu_0 to e_0),
    # and the certificate's strict step fails at the threshold.
    for postwait0 in ("silent", "late"):
        trembles = {v: AliceTrembles(F(1), 1, "silent", F(1), 1) for v in TYPES}
        trembles[0] = AliceTrembles(F(1), 1, postwait0, F(1), 1)
        try:
            check_preserving_native_se(G2, k, rng, trembles, [beta_star] * k)
        except AssertionError:
            pass
        else:
            raise AssertionError(f"replica with type 0 {postwait0} wrongly accepted")
    try:
        g2_impossibility(k, F(k - 1))
    except AssertionError:
        pass
    else:
        raise AssertionError("certificate wrongly accepted at the threshold")
    print(f"G2 native, K={k}: preserving SE exists for rhoD >= {k - 1} "
          f"(Bob replays the source reply at every c)")

    # ---- G1 (two actions): the source belief cannot be reproduced at every c,
    # but a preserving native SE with c-dependent beliefs exists.
    q = F(1, 11)
    beta1 = mixed(G1, x=q, y=1 - q)
    mu1 = check_source_se(G1, (F(3, 2), F(3, 4), F(3, 4)), beta1)
    assert mu1 == (F(1, 2), F(1, 4), F(1, 4)) and G1.best_responses(mu1) == {"x", "y"}
    assert [G1.disclose_payoff(v) - G1.fail_payoff(v, beta1) for v in TYPES] == [10, 0, 0]
    rho_d1 = G1.payoff_range()
    assert rho_d1 == 20
    # With beta1 at every c, type 0 strictly prefers late, so if mu_a(0) > 0
    # then mu_0 = e_0 and Bob must play x there. Instead put mu_a on type 1:
    # Bob plays y at every c != 0 and x with probability 10/11 at c = 0, where
    # the type-0 late mass and the type-1 silent mass are of the same order.
    trembles1 = {
        0: AliceTrembles(F(1), 1, "late", F(1), 2),    # a_0 ~ eps^3, b_0 ~ eps
        1: AliceTrembles(F(1), 1, "silent", F(1), 1),  # a_1 ~ eps,   b_1 ~ eps^2
        2: AliceTrembles(F(1), 2, "silent", F(1), 1),  # a_2 ~ eps^2
    }
    silent_beta1 = [mixed(G1, x=F(10, 11), y=F(1, 11))] + [mixed(G1, y=F(1))] * (k - 1)
    beliefs1 = check_preserving_native_se(G1, k, rho_d1, trembles1, silent_beta1)
    assert beliefs1[0] == (F(1, 2), F(1, 2), F(0)) and beliefs1[3] == (F(0), F(1), F(0))
    assert all(G1.fail_payoff(v, mixed(G1, x=sum(b["x"] for b in silent_beta1) / k,
                                       y=sum(b["y"] for b in silent_beta1) / k)) <= 0 for v in TYPES)
    print(f"G1: preserving native SE at rhoD = range = {rho_d1}: beliefs at (silent, c) "
          f"{tuple(map(str, beliefs1[0]))} for c=0, {tuple(map(str, beliefs1[3]))} otherwise; "
          f"Bob x w.p. 10/11 at c=0, y elsewhere")
    print("verdict: G2 meets the standard (given the configuration's admissibility); "
          "G1 shows the belief argument alone is not enough")


if __name__ == "__main__":
    main()
