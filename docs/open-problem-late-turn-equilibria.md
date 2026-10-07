# Open problem: sequential equilibria with late sends and leaked openings

Status: open. This note states the question self-containedly so that it can be
worked on independently of the rest of the project. Answers are welcome in
either direction: a proof, or a counterexample meeting the standard in the last
section.

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
