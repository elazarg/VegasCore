# Open problem: sequential equilibria with late sends and leaked openings

Status: variants 1 and 2 are false (counterexample below, mechanized in Lean
as `Vegas.Paper.late_leak_intended_outcome_not_preserved`, and for every
margin `D > R`, `c >= 0` as
`Vegas.Paper.late_leak_not_preserved_for_every_margin`); corrected positive
versions are stated after it. This note states the question
self-containedly so that it can be worked on independently of the rest of the
project.

## Background in one paragraph

A game program is compiled to a ledger. Players commit to hidden values and
later open them. A *builder* (block producer) orders and includes signed
packets. A packet sent in an owner's *protected* window is included before its
deadline; a packet sent later (*late*) is included only if the builder chooses
to. Pending packets may be observed by other players before inclusion (a
*leak*), so a pending opening reveals the committed value. Withholding an
opening is deterred by a *forfeit* `D` charged to the owner of a failed reveal,
and a dropped late opening is also charged an expected amount `c` by an audit.
The intended game has none of this: commitments hold values and reveals open.
The project has proved Nash-equilibrium preservation from the intended game to
the ledger for every builder that respects protected inclusion. Sequential
equilibrium (SE) preservation is proved for a fixed-calendar builder and open
for arbitrary builders; this note isolates why.

## The concrete question

**Family of games.** Fix rationals `R > 0`, `D >= 3R`, `c > R`, and
`q in (0, 1)`.

- Sender B has a private type `t = (v, s)` drawn from a known prior with full
  support (independent coordinates are enough to be interesting; the probes use
  `P(v = 1) = P(s = 1) = 9/20`). B has committed to `v`.
- B's opening of `v` can be sent at a protected turn `P` (always included on
  time) or, if B waits, at one of the late turns `L1, ..., Lk` (`k >= 2`). A
  late opening is included before the deadline with probability `q`,
  independently of its content and of everything else (the builder is
  content-blind). If nothing is included, the reveal fails.
- Listener A is activated between consecutive late turns and observes every
  pending opening at that moment (so an opening sent at `L1` and still pending
  when A is activated reveals `v` to A). A's other observations: the ledger
  (whether and when B's opening was included and its value) and nothing else.
- After the reveal resolves, A chooses an answer `a` from a finite set.
- Payoffs:
  - B: a base utility `b_B(t, a, outcome) in [0, R]`, minus `D` if the reveal
    failed, minus `c` if a late opening was sent and dropped.
  - A: a utility depending on `t`, `a`, and whether the reveal succeeded.
- The *intended game* is the same game with only the protected turn (B always
  opens at `P`); fix a sequential equilibrium `sigma` of it. On path, B opens at
  `P` and A plays its intended answers.

**Question.** For every such game (any finite type set, any `k >= 2`, any
finite answer sets, possibly several listeners activated at different times),
does the full game have a sequential equilibrium (Kreps-Wilson: consistent
assessment, sequentially rational at every information set) whose outcome
distribution equals that of `sigma`? Equivalently: one in which every type opens
at `P` and A plays `sigma`'s answers on path.

Variants of interest, in order of usefulness:
1. the question as stated, under `D >= 3R`, `c > R`;
2. the same with a weaker margin (e.g. `D > R`), stating the exact condition;
3. the abstract version below.

## What is known

**Margins and their factors.** Write `U - F` for B's value after a successful
reveal minus after a failed one; it lies in `[D - R, D + R]` (the forfeit, plus
or minus one `R` of base-utility spread). The value to B of any reaction of A to
a late inclusion lies in `[-R, R]`. Deliberate lateness (waiting past `P`, then
sending late) gains at most `qR - (1 - q)(D - R + c)`.

**Obstruction for fixed trembles (exact).** Suppose two types `t1, t0` strictly
prefer opposite late turns (`t1` prefers `L1`, `t0` prefers `L2`), sending at the
other turn only with vanishing probability. For any ratio `r` of their
probabilities of reaching the late turns (the ratio of their deferral trembles
at `P`), A's belief after an inclusion at `L1` has `t1 : t0` ratio of order
`r / e1` and after an inclusion at `L2` of order `r * e2` (`e1, e2 -> 0`). So one
of the two beliefs is a point mass. If A's intended answer is a best reply only
at interior beliefs, it cannot be played at both inclusion sites. Opposite
strict preferences between late turns arise because a leak at `L1` changes what
A knows after a dropped opening.

**How preserving equilibria escape (exact, small games).** In every design
checked (two types per value of `v`, two late turns, `q` up to `999/1000`,
`D in {3R, 4R}`, `c in {2R, R + 1/2}`), a preserving SE exists:
- every type opens at `P`;
- after an inclusion at `L1`, A mixes its intended answer with a small reward to
  the minority type, with probability `(1 - q) / (q * gap)` (e.g. `1/99`), which
  makes that type indifferent between `L1` and `L2`, so both types send at `L1`;
- the deferral trembles at `P` are tilted with a specific coefficient (not only
  an order; `22/27` in one design) so that A's belief at that site sits exactly
  at A's indifference point;
- the reward stays inside the deterrence slack, because the leak-driven gap is
  at most `(1 - q)R` and `R < D - R + c`.

With equal tremble rates for all types, or with A playing the intended answer at
both inclusion sites, every assessment checked is rejected.

**Why the obvious constructions fail.**
- *Complete the off-path part by any rational choice:* some rational completions
  are bad (a point-mass belief makes A reward a type fully, and that type then
  defers deliberately when `q` is near 1).
- *Perfect equilibrium with free timing:* for `q` near 1 there are
  self-consistent perturbed equilibria with on-path deliberate lateness, whatever
  the margins (the margins bound the cost of lateness, not `q`).
- *Choose the tilts by an extra fictitious player:* nothing forces deviation
  gains to be nonpositive at its fixed points.
- *Restrict A's off-path answers to a small ball around the intended answer:*
  deterrence holds, but the restriction must not bind in the limit, which needs
  tilts and mixtures that put every post-inclusion belief where the intended (or
  near-intended) answer is a best reply. That is a system with one condition per
  inclusion site (late turns, values of `v`, failure sets, downstream listeners)
  and one unknown per tilt ratio and per indifferent type's mixture. Whether it
  is always solvable is the crux.

**Counterexample to variant 1 (verified twice, independently).** Game `G*`:
types `t = (v, s)`, `v in {0, 1}` with `P(v = 1) = 9/20`, `s in {A, B, C}` uniform
and independent; `R = 2`, `D = 6 = 3R`, `c = 3 > R`, `q = 99/100`, `k = 2`; one
listener activated between `L1` and `L2`, who learns `v` from a pending opening.
After a success the listener plays the safe answer `m` (worth `2/5` to it) or a
guess of `s` (worth 1 if correct); the sender gets `R/2` under `m`, and under any
guess types `A, B` get `R` and type `C` gets `0`. After a failure the listener
gets `[a = v]` and the sender gets `(R, 0, 0)` under `f1` and `(0, R, 0)` under
`f0`, over `(A, B, C)`. The intended SE is unique (the listener plays `m`). In
every SE of the full game the outcome differs:
1. every success answer acts on the sender along the single direction
   `(1, 1, -1)`;
2. whatever the listener does at the no-leak failure set, the leak splits `A`
   from `B` in some class `v`, so two of its types strictly prefer opposite late
   turns;
3. the cross ratio of the beliefs at the two inclusion sites tends to `0`, so one
   site has a belief on a face of the simplex, for every tremble tilt;
4. on a face the largest belief is at least `1/2 > 2/5`, the listener guesses,
   and type `(v, A)` gains `qR - (1 - q)(D + c) = 189/100 > 1 = R/2` by
   deferring.

The intended outcome remains a Nash and weak-PBE outcome of `G*`; only
Kreps-Wilson consistency excludes it. Two types per class always escape (one
reward direction lines them up), and richer designs whose rewards do not lie on
one line also escape (three types, three late turns, two listeners). The same
game refutes every margin `D > R`, `c >= 0` once `q` is close enough to `1`.

**Positive results (proved on paper, not mechanized).**
- If `q(D - R) <= (1 - q)c` (with `D >= 2R`), deferring never pays and a
  preserving SE exists, leaks or not.
- If pending late openings are never observed, a preserving SE exists for every
  `k`, `D >= 2R`, `c >= 0`.
- With leaks and one listener, a reward-richness condition on the listener's
  answers suffices.

Lean proof: [the late-turn example](../Vegas/Examples/LateLeak/Game.lean)
defines the game and its intended game as finite information models for
arbitrary parameters `R`, `D`, `c` and `q in (0, 1)`, with the prior and the
listener's payoffs of `G*`. With standard axioms,
`Vegas.Paper.late_leak_not_preserved_when_deferral_pays` proves that the
intended game has a sequential equilibrium, that all its sequential equilibria
have the intended outcome law, and that no sequential equilibrium of the full
game has it, whenever `R > 0`, `q(D - R) > (1 - q)c` and
`qR - (1 - q)(D + c) > R/2`. No other condition on the parameters is used,
and each step uses only part of it: the single reward direction
(`lateLeak_sender_success_value`) holds for all parameters; sending at `L2`
beats never (`lateLeak_send_beats_withhold`) uses `q(D - R) > (1 - q)c` and
`R >= 0`; the opposite strict preferences for every listener mixture
(`lateLeak_opposite_preferences`) use `R > 0` and `q < 1`; the face of the
simplex (`lateLeak_consistent_face`) holds for every `q in (0, 1)`; the
listener's guess on a face (`lateLeak_rational_guesses`) depends only on the
listener's payoffs; and the profitable deferral (`lateLeak_defer_first`,
`lateLeak_defer_second`) uses `qR - (1 - q)(D + c) > R/2` and `R >= 0`.
`Vegas.Paper.late_leak_not_preserved_for_every_margin` derives the variant-2
statement: for every `R > 0`, `D > R` and `c >= 0` the threshold
`max(c / (D - R + c), (D + c + R/2) / (D + c + R))` is below 1, and both
conditions hold for every `q` above it. The bound `c >= 0` is used only for
this explicit threshold. `Vegas.Paper.late_leak_intended_outcome_not_preserved`
is the instance `R = 2`, `D = 6`, `c = 3`, `q = 99/100`.

Checkers: [`g_star_verification.py`](../scripts/experiments/g_star_verification.py),
[`three_type_counterexample.py`](../scripts/experiments/three_type_counterexample.py),
[`late_turn_search.py`](../scripts/experiments/late_turn_search.py).

## Timed release

A *timed-release* reveal is an ideal construct that timed commitments
(Boneh-Naor) can implement. The commitment carries validated recovery material.
A service transition publishes the value no later than a fixed delay after the
commitment, and the delay is chosen so that this never happens before the
reveal is ready. The reveal cannot fail, and the runtime gives the owner no
opening action. The test keeps the types, prior, payoffs and listener of `G*`
(`R = 2`, `D = 6`, `c = 3`, `q = 99/100`, the leak rule, a content-blind
builder) and places the reveal in this mode. Consistency is Kreps-Wilson with
arbitrary type- and node-dependent trembles, and all arithmetic is exact.

**Without owner opening the reveal obstruction disappears. It returns at the
commitment if the commitment can be sent late and its leaked material can be
recovered.**
- *Commitment given, as in `G*`:* the sender has no decision. The listener's
  only information sets are on path with the prior belief, where the safe
  answer `m` is the unique best reply. The intended outcome is the unique SE
  outcome.
- *Protected commitment that the sender may omit* (forfeit `D`, nothing
  learned): omission is strictly dominated whenever `D > R/2`, so the intended
  outcome is again the unique SE outcome.
- *Commitment with a protected turn and two late turns* under the inclusion and
  leak rules of `G*`, where a dropped binding costs `D + c`:
  - If the listener can recover `v` from a pending commitment it saw before it
    answers, the game is `G*` with "commit" in place of "open". The sender's
    plan values coincide with the independent encoding of `G*`. Whenever
    `q(D - R) > (1 - q)c` and `qR - (1 - q)(D + c) > R/2`, the mechanized
    theorem therefore applies and no SE has the intended outcome. At `G*`'s
    parameters this is the verdict. Recovery by any holder of the material is
    what a timed commitment provides.
  - If the dropped material cannot be recovered before the listener answers,
    and the listener only sees that a binding was pending, a preserving SE
    exists. In it the listener plays `m` after every success and `f0` after
    every failure, and trembles are type-independent. The sender's payoffs then
    do not depend on `v`. This construction needs all types to agree on sending
    versus never at a late turn: `q(D - R/2) >= (1 - q)c` or
    `q(D + R/2) < (1 - q)c`.

So timed release removes the obstruction exactly when no strategic timing
remains before the value becomes recoverable. That holds when commitments are
protected, or when leaked material stays sealed until after every dependent
decision.

**Early opening by the owner is harmless in `G*` and deterred by a charge above
`R`.** In this variant the owner may also send an early opening as a raw
network packet. It can go at a protected early turn, before the listener's
activation (where it leaks), or after it. The audit sees every signed envelope
and charges `c'` for an early opening at settlement, whether or not it was
included.
- With `c' > R` (the spread of the sender's base utility), every early opening
  is strictly dominated whatever the listener does. The intended outcome is
  then the unique SE outcome, and the bound is strict: `c' = R` does not give
  domination.
- As a control, with `c' = 0` a preserving SE still exists, because the value
  is published anyway and the listener of `G*` acts only afterwards. The early
  opening is then a pure timing signal, and type-independent trembles keep the
  prior belief at every opening site. Some consistent completions fail (a tilt
  that puts a point mass after an early inclusion makes the listener guess, and
  `(1, A)` then opens), so the existence is a real choice of assessment.
- The answer changes when a decision comes between the opening and the release.
  As a control, the listener takes an interim action at activation (listener
  gets `[y = v]`, sender gets `g[y = 1]`). The intended outcome is then an SE
  outcome if and only if `g <= c'`. With `c' = 0` and `g > 0` no SE has it,
  because the opening makes `v = 1` public and `(1, A)` gains `g - c'`.

**Parameters.** The grid had `R = 2`, `D in {3, 6, 12}`, `c in {0, 1, 3, 6}`
and `q in {1/2, 9/10, 99/100, 999/1000, 9999/10000}`, 60 points in all.
- The given and protected-commitment verdicts hold at every point.
- With recoverable late commitments, 41 points satisfy the theorem's hypothesis
  and have no preserving SE. These include every point with `q >= 99/100`.
  At 17 points the structured search finds an exactly verified preserving SE;
  these are all points with `q = 1/2` and those with `q = 9/10, D = 12` or
  `q = 9/10, D = c = 6`. Two points are undecided:
  `(D, c, q) = (3, 6, 9/10)` and `(6, 3, 9/10)`.
- With opaque late commitments, the construction applies at 58 points. It does
  not apply at `(3, 3, 1/2)` and `(6, 6, 1/2)`, which are undecided there.
- The early-opening verdicts hold at every point. With `c' = 0` and with
  `c' = R + 1/100` the intended outcome survives. In the interim control
  (`g in {R/4, R}`) it survives at `c' = g` and fails at `c' = 0` and at
  `c' = g - 1/100`.

Checker: [`timed_release_probe.py`](../scripts/experiments/timed_release_probe.py).

## Abstract version (a candidate formulation, possibly too strong)

Let `Gamma` be a finite extensive-form game with perfect recall, `Gamma°` the
game obtained by deleting some actions ("extra" actions), and `(sigma°, mu°)` an
SE of `Gamma°`. Suppose payoffs split as `u_i = b_i - p_i` with `b_i in [0, R]`
and penalties `p_i >= 0` that depend only on `i`'s own extra actions and nature,
and that every extra action of `i` costs `i` an expected penalty of at least
`s` while changing what others learn only in a way whose effect on `i`'s
continuation value is bounded by `g < s`. Is there an SE of `Gamma` with the
outcome distribution of `sigma°`?

The concrete family has `s = (1 - q)(D - R + c)` and `g` at most `(1 - q)R`, but the reward others can give after a deviation can be as large as
`R`, which exceeds `s` for `q` near 1. A correct abstract statement must
therefore bound what deviations reveal, not what others can do; finding the
right formulation is part of the problem.

## What counts as an answer

- **Proof:** for the concrete family (variant 1), or for a correct abstract
  version that covers it, an argument constructing a consistent assessment and
  verifying sequential rationality at every information set.
- **Counterexample:** one game in the family, one intended SE, and a proof that
  every SE of the full game has a different outcome distribution. Consistency
  must be taken in the Kreps-Wilson sense (limits of fully mixed profiles, with
  arbitrary type- and turn-dependent tremble rates). Exact rational arithmetic
  is expected for any computational component.

Exact checkers for the small designs above are in
[`scripts/experiments/late_turn_leak_probe.py`](../scripts/experiments/late_turn_leak_probe.py)
and
[`scripts/experiments/late_turn_alignment_probe.py`](../scripts/experiments/late_turn_alignment_probe.py).
