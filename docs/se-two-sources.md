# Two sources and the forfeit pass

Status: proposal for discussion. Nothing here is a checklist box until the
project owner approves it; see the [checklist](se-async-checklist.md) for the
fixed obligations.

## The question

The [arbitrary-builder target](se-async-checklist.md#target) preserves every
sequential equilibrium of the source game. The source exposes withholding at a
reveal as a legal move whose outcome the program prices through its failure
branch, because the runtime cannot prevent an owner from staying silent. A
designer usually means a different game: one in which commitments hold values
and reveals open. The question this note frames is whether a compiler
implements *that* game: if the intended game has a sequential equilibrium, does
the runtime, where withholding is possible, have one with the same joint law?

## How the runtime meets a deviation

Every deviation the runtime admits falls into one of three classes.

1. **Prevented.** The contract rejects it: a wrong sender, a missing readiness
   token, a late packet. No source models it.
2. **Attributable.** It cannot be prevented, but the public record names the
   player responsible, so a deposit charge can deter it. Forbidden signed
   content and a missed binding are handled this way today; the source does not
   model them, and the compiler is already incentive-aware for them.
3. **Not attributable.** Timing, waiting, off-chain and covert-channel talk.
   These must be source mechanics or stated limitations.

Withholding at a reveal is attributable: a resolution expiry is public and the
reveal has one owner. The source exposes it by choice, not by necessity. That
choice is useful in its own right, since some games price withholding as an
intended option (reveal or lose a bond), but it is not forced.

## Two sources

- **Mechanics exposed, `S_exp`.** The current source language. Withholding is a
  move, priced by the program's failure branch. The target theorem compiles
  `S_exp` to the runtime without changing incentives for exposed moves.
- **Mechanics hidden, `S_int`.** The intended game: every owned reveal opens and
  every commitment holds a value. A profile of `S_int` is a source profile in
  the classes `ValueBinding` and `Disclosing` (together `Honest`).
- **The forfeit pass, `S_int → S_exp`.** It rewrites each failure branch caused
  by an owner's withholding so that the owner forfeits `D`, with `D` above the
  range of payoffs. Opening then beats withholding at every reveal, whatever
  the beliefs.

The proposed theorem H: every sequential equilibrium of a program in `S_int`
is a sequential equilibrium of its rewriting in `S_exp`, with the same joint
law of initial parameters, public results and payoffs, because honest play
never reaches a rewritten branch. Composed with the target theorem for
`S_exp`, it says the runtime implements every equilibrium of the intended game
under a deposit.

`exists_disclosing_expect_le` is the existing conditional form: under
`DisclosesProfitably` a player loses nothing by being held to `Disclosing`. The
forfeit pass is what discharges that premise for every program instead of
assuming it.

This also places the runtime semantics. Resolution silence is uncharged
withholding in the runtime (semantics A); the forfeit is a source payoff that
the compiled contract executes from the public expiry. The money flow equals a
runtime charge on silence, but it sits where the source semantics accounts for
it.

## Open points

1. **Honest guard failure (resolved).** A guard reads only public data,
   existing publications and its author's own commitments (`SourceGuardRead`),
   all known to the author at the commit. A program of `S_int` is well formed
   only if, at every reachable commit, the guard is satisfiable given those
   inputs; this is a hypothesis of H, discharged outside VegasCore. Honest play
   binds accepted values, so an honest run never fails a guard
   (`runFrom_successful` under `GuardsAcceptFrom`, which well-formedness
   discharges). Every failed reveal is then its owner's own deviation, by
   withholding or by a rejected value, and the forfeit pass forfeits the owner
   of every failed reveal. No second failure kind is needed.
2. **Information sets `S_int` lacks.** After another player withholds, `S_exp`
   has continuations with no counterpart in `S_int`. They need a consistent
   assessment chosen by rational completion, as the risk menu does in the
   runtime. Routine, but it must be proved.
3. **Deposit size.** `D` above the payoff range needs bounded utilities; the
   runtime deposit already assumes them. Whether one deposit can serve both the
   forfeit and the audit charge is a design choice.
4. **Bindings.** Binding an unopenable candidate is also attributable and is
   already charged by the runtime. For symmetry, `S_int` could hide it too and
   the forfeit pass would cover it.
5. **Scope of "honest".** `Honest` constrains only a player's own moves. The
   equilibrium concept for `S_int` is the ordinary one on its game tree, whose
   information sets are those of `S_exp` minus every history containing a
   withholding.

6. **Concurrent reveals (now a target, checklist box C3).** Reveals are ordered because a later
   owner's withholding choice may depend on earlier opened values. In `S_int`
   there is no such choice, and under the forfeit withholding is strictly
   dominated at every information set whatever the owner knows, so the
   information available to it does not matter. A compiler for `S_int` could
   then run a block of consecutive reveals concurrently, even though the
   runtime lets the last revealer read the earlier openings while they are
   still pending. The licence is game-theoretic, not a program equivalence: in
   `S_exp`, with priced withholding, reordering changes the withholder's
   information and is not faithful. Bindings are concurrent because their
   values are hidden; reveals would be concurrent because their alternative is
   deterred. Limits: a guard that reads an earlier publication, and any
   decision between two reveals that observes the first, keep their order.
   Not part of the current design.

## Proposed box

**H. Intended-game preservation.** For every program of `S_int` and every
sequential equilibrium of it, the forfeit-pass rewriting has a sequential
equilibrium in `S_exp` with the same joint law and no forfeit on its paths;
composed with S8, the runtime has one too. Pinned with standard axioms.
