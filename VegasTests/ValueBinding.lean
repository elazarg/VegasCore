/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.BindingNormalization
import Vegas.Expr.Simple

/-! # Regression for the value-binding translation

One player binds a cell and opens it, under a guard that accepts everything, so
the payoff separates a published value from a failure. A policy that binds an
unopenable candidate and opens it is worth nothing; the translation binds a real
value instead and must therefore refuse to open it, or the published value would
change the payoff.

The translation must refuse at exactly the cells it replaced, preserving the
public outcome and complete public default history.
-/

namespace VegasTests.ValueBinding

open Vegas Vegas.SourceProgram GameTheory.Math.Probability

noncomputable section

private abbrev bid : VarId := 0
private abbrev bidOut : VarId := 1

/-- A guard that accepts every opening. -/
private def openGuard : SourceGuard (Player := Unit) simpleExpr [] () bid .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by decide
  code := .constBool true
  reads := fun h => nomatch h

/-- Bind a Boolean, open it, and be paid only for a published value. -/
private def program : SourceProgram Unit simpleExpr [] ∅ :=
  .commit bid () (by decide) openGuard <|
  .reveal bidOut () bid (by decide) .here (by decide) <|
  .ret [((), .ite (.isFailure (.var bidOut .here)) (.constInt 0) (.constInt 1))]

/-- Bind an unopenable candidate, then try to open it. -/
private def failingPolicy : PurePolicy (who := ()) program :=
  (fun _ _ _ => some .failure, (fun _ _ _ => true, PUnit.unit))

private def profileOf (policy : PurePolicy (who := ()) program) :
    program.BehavioralProfile :=
  fun _ => PurePolicy.toBehavioral program policy

/-- Binding failure and opening it publishes failure, which pays nothing. -/
example :
    (program.run (profileOf failingPolicy) (Env.empty (CellVal simpleExpr))).map
      (fun final => program.evaluatePayoffs final.state) = PMF.pure [((), 0)] := by
  unfold SourceProgram.run program
  rw [SourceProgram.runFrom]
  change ((PMF.pure _).bind _).map _ = _
  rw [PMF.pure_bind, SourceProgram.runFrom]
  change ((PMF.pure _).bind _).map _ = _
  rw [PMF.pure_bind]
  change (PMF.pure _).map _ = _
  rw [PMF.pure_map]
  rfl

/-- The translation binds a real value, so it must refuse to open it. Were it to
open, the publication would carry that value and pay one. -/
example :
    (program.run (profileOf (PurePolicy.bindValues program failingPolicy))
        (Env.empty (CellVal simpleExpr))).map
      (fun final => program.evaluatePayoffs final.state) = PMF.pure [((), 0)] := by
  unfold SourceProgram.run program
  rw [SourceProgram.runFrom]
  change ((PMF.pure _).bind _).map _ = _
  rw [PMF.pure_bind, SourceProgram.runFrom]
  change ((PMF.pure _).bind _).map _ = _
  rw [PMF.pure_bind]
  change (PMF.pure _).map _ = _
  rw [PMF.pure_map]
  rfl

/-- The canonical Boolean is `false`, so a policy that genuinely binds `false`
and opens it is the case the translation must *not* touch: it looks exactly like
a replaced binding. Publishing the value pays one. -/
private def genuinePolicy : PurePolicy (who := ()) program :=
  (fun _ _ _ => some (.success false), (fun _ _ _ => true, PUnit.unit))

example :
    (program.run (profileOf genuinePolicy) (Env.empty (CellVal simpleExpr))).map
      (fun final => program.evaluatePayoffs final.state) = PMF.pure [((), 1)] := by
  unfold SourceProgram.run program
  rw [SourceProgram.runFrom]
  change ((PMF.pure _).bind _).map _ = _
  rw [PMF.pure_bind, SourceProgram.runFrom]
  change ((PMF.pure _).bind _).map _ = _
  rw [PMF.pure_bind]
  change (PMF.pure _).map _ = _
  rw [PMF.pure_map]
  rfl

/-- And the translation leaves it alone, so it still pays one. A translation
that refused wherever it saw the canonical value would pay nothing here. -/
example :
    (program.run (profileOf (PurePolicy.bindValues program genuinePolicy))
        (Env.empty (CellVal simpleExpr))).map
      (fun final => program.evaluatePayoffs final.state) = PMF.pure [((), 1)] := by
  unfold SourceProgram.run program
  rw [SourceProgram.runFrom]
  change ((PMF.pure _).bind _).map _ = _
  rw [PMF.pure_bind, SourceProgram.runFrom]
  change ((PMF.pure _).bind _).map _ = _
  rw [PMF.pure_bind]
  change (PMF.pure _).map _ = _
  rw [PMF.pure_map]
  rfl

/-- The class is not vacuous: the policy the translation has to repair is
outside it, and its translation is inside. -/
example : ¬ ValueBinding program (PurePolicy.toBehavioral program failingPolicy) := by
  intro h
  let view := (Config.initial (Env.empty (CellVal (Player := Unit) simpleExpr))).view ()
  have active : () ∉ view.defaulted := by simp [view]
  exact h.1 rfl view active (by simp [program, PurePolicy.toBehavioral, failingPolicy])

example :
    ValueBinding program
      (PurePolicy.toBehavioral program (PurePolicy.bindValues program failingPolicy)) :=
  valueBinding_bindValues program failingPolicy

end

end VegasTests.ValueBinding
