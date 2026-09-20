/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Disclosure
import Vegas.Expr.Simple

/-! # Regression for forcing disclosure

Two programs with the same shape and opposite payoffs. In the first, opening is
what pays, so forcing the owner to open turns nothing into something and the
premise of `forceDisclose_expect_le` is what makes that an improvement. In the
second, refusing is what pays, so forcing the owner to open destroys the payoff
-- which is the point of carrying the premise rather than claiming the class is
preserved outright.
-/

namespace VegasTests.Disclosure

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

/-- Bind a Boolean and open it; a published value pays, failure does not. -/
private def openPays : SourceProgram Unit simpleExpr [] ∅ :=
  .commit bid () (by decide) openGuard <|
  .reveal bidOut () bid (by decide) .here (by decide) <|
  .ret [((), .ite (.isFailure (.var bidOut .here)) (.constInt 0) (.constInt 1))]

/-- The same program with the payoff reversed: refusing is what pays. -/
private def refusalPays : SourceProgram Unit simpleExpr [] ∅ :=
  .commit bid () (by decide) openGuard <|
  .reveal bidOut () bid (by decide) .here (by decide) <|
  .ret [((), .ite (.isFailure (.var bidOut .here)) (.constInt 1) (.constInt 0))]

/-- Bind a value and then refuse to open it. -/
private def withholdOpen : BehavioralPolicy (who := ()) openPays :=
  (fun _ _ => FinDist.pure (.success false), fun _ _ => FinDist.pure false, PUnit.unit)

private def withholdRefusal : BehavioralPolicy (who := ()) refusalPays :=
  (fun _ _ => FinDist.pure (.success false), fun _ _ => FinDist.pure false, PUnit.unit)

/-- Refusing to open is outside the disclosing class. -/
example : ¬ Disclosing openPays withholdOpen := by
  intro h
  exact h.1 rfl
    (sourceObserve () (Env.cons (Val := CellVal simpleExpr) (x := bid)
      (τ := .privateData () .bool) (.success false) (Env.empty (CellVal simpleExpr))), [])
    (by simp [withholdOpen])

example : Disclosing openPays (BehavioralPolicy.forceDisclose openPays withholdOpen) :=
  disclosing_forceDisclose openPays withholdOpen

private def payoffLaw {p : SourceProgram Unit simpleExpr [] ∅}
    (policy : BehavioralPolicy (who := ()) p) : FinDist (List (Unit × Int)) :=
  (p.run (fun _ => policy) (Env.empty (CellVal simpleExpr))).map p.evaluatePayoffs

/-- Withholding where opening pays is worth nothing. -/
example : payoffLaw withholdOpen = FinDist.pure [((), 0)] := by
  simp only [payoffLaw, SourceProgram.run, openPays, withholdOpen, SourceProgram.runWith,
    SourceProgram.commitKernel, SourceProgram.revealKernel, SourceProgram.afterCommit,
    FinDist.pure_bind, FinDist.map_pure]
  rfl

/-- Forcing the owner to open collects the payoff it was refusing. -/
example :
    payoffLaw (BehavioralPolicy.forceDisclose openPays withholdOpen) = FinDist.pure [((), 1)] := by
  simp only [payoffLaw, SourceProgram.run, openPays, withholdOpen,
    BehavioralPolicy.forceDisclose, SourceProgram.runWith, SourceProgram.commitKernel,
    SourceProgram.revealKernel, SourceProgram.afterCommit, FinDist.pure_bind, FinDist.map_pure]
  rfl

/-- Where refusing is what pays, the same forcing destroys the payoff, so the
premise cannot hold there. -/
example : payoffLaw withholdRefusal = FinDist.pure [((), 1)] := by
  simp only [payoffLaw, SourceProgram.run, refusalPays, withholdRefusal, SourceProgram.runWith,
    SourceProgram.commitKernel, SourceProgram.revealKernel, SourceProgram.afterCommit,
    FinDist.pure_bind, FinDist.map_pure]
  rfl

example :
    payoffLaw (BehavioralPolicy.forceDisclose refusalPays withholdRefusal) =
      FinDist.pure [((), 0)] := by
  simp only [payoffLaw, SourceProgram.run, refusalPays, withholdRefusal,
    BehavioralPolicy.forceDisclose, SourceProgram.runWith, SourceProgram.commitKernel,
    SourceProgram.revealKernel, SourceProgram.afterCommit, FinDist.pure_bind, FinDist.map_pure]
  rfl

end

end VegasTests.Disclosure
