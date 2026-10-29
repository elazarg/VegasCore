/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Expr.Simple
import Vegas.Source.Semantics
import Vegas.Pending.ExclusionApplication

/-! # A withheld opening followed by a successful opening

The source evaluator permits an owner to resume disclosure after a failure.
The exact laws below separate that behavior from permanent withholding. The
runtime trigger lemmas distinguish accepted opaque bindings from expiry.
-/

noncomputable section

namespace VegasTests

open Vegas Vegas.SourceProgram Vegas.EventGraphRuntime
  GameTheory.Math.Probability

private inductive Owner where
  | alice
  deriving DecidableEq

private abbrev initialContext : SourceCtx Owner simpleExpr :=
  [(1, .commitment .alice .bool), (0, .commitment .alice .bool)]

private def twoOpenings : SourceProgram Owner simpleExpr initialContext {0, 1} :=
  .reveal 2 .alice 0 (by decide) (.there .here) (by decide) <|
  .reveal 3 .alice 1 (by decide) (.there .here) (by decide) <|
  .ret []

private def initial : State simpleExpr initialContext :=
  Env.cons (.success true) (Env.cons (.success true) (Env.empty (CellVal simpleExpr)))

private def withholdingThen (openSecond : Bool) : BehavioralProfile twoOpenings :=
  fun _ => (fun _ _ => PMF.pure false,
    (fun _ _ => PMF.pure openSecond, PUnit.unit))

private def publications (state : State simpleExpr twoOpenings.terminalCtx) :
    PublicationResult Bool × PublicationResult Bool :=
  (state.get (.there .here), state.get .here)

private def final (openSecond : Bool) : State simpleExpr twoOpenings.terminalCtx :=
  Env.cons (if openSecond then .success true else .failure)
    (Env.cons .failure initial)

private theorem run_twoOpenings (openSecond : Bool) :
    twoOpenings.run (withholdingThen openSecond) initial = PMF.pure (final openSecond) := by
  simp only [SourceProgram.run, twoOpenings, withholdingThen, runFrom,
    revealKernel, afterReveal, PMF.pure_bind]
  cases openSecond <;> rfl

/-- The source evaluator admits successful disclosure after the same owner's
earlier withheld disclosure. -/
theorem source_can_open_after_withholding :
    (twoOpenings.run (withholdingThen true) initial).map publications =
      PMF.pure (.failure, .success true) := by
  rw [run_twoOpenings, PMF.pure_map]
  rfl

/-- Permanent withholding changes an observable source law. -/
theorem source_permanent_withholding_changes_law :
    (twoOpenings.run (withholdingThen true) initial).map publications ≠
      (twoOpenings.run (withholdingThen false) initial).map publications := by
  rw [source_can_open_after_withholding]
  have silent : (twoOpenings.run (withholdingThen false) initial).map publications =
      PMF.pure (.failure, .failure) := by
    rw [run_twoOpenings, PMF.pure_map]
    rfl
  rw [silent]
  intro same
  have mass := congrArg (fun law : PMF (PublicationResult Bool × PublicationResult Bool) =>
    law (.failure, .success true)) same
  simp [PMF.pure_apply] at mass

section RuntimeTriggers

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Accepting a commitment does not itself exclude its owner, independently
of the hidden binding result. -/
theorem accepted_binding_does_not_exclude (state : RecoveryState graph)
    (event : graph.EventId) (handle : Handle graph) (native : State graph) :
    (state.inclusionResult (.commitment event handle) native).excluded = state.excluded := rfl

/-- Completing an owned expiry publicly excludes that owner. -/
theorem completed_expiry_excludes_owner (state : RecoveryState graph)
    (event : graph.EventId) (native : State graph) (owner : Player)
    (unfinished : event ∉ state.native.config.cut.completed)
    (completed : event ∈ native.config.cut.completed) (owned : graph.actor? event = some owner) :
    (state.environmentResult (.expire event) native).excluded = insert owner state.excluded := by
  simp only [RecoveryState.environmentResult, unfinished, not_false_eq_true, completed,
    and_self, ↓reduceIte, RecoveryState.excludeEvent, owned]

end RuntimeTriggers

end VegasTests
