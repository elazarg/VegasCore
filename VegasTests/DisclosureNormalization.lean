/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.DisclosureBehavioral
import Vegas.Expr.Simple

/-! # Guard-aware source disclosure normalization

An authentic binding whose guard rejects is withheld by the compiled policy.
The source step keeps the same values and public default record; its owner's
private intention distinguishes the attempted opening from withholding.
-/

namespace VegasTests.DisclosureNormalization

open Vegas Vegas.SourceProgram GameTheory.Math.Probability

noncomputable section

private def rejectGuard : SourceGuard (Player := Unit) simpleExpr [] () 0 .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by decide
  code := .constBool false
  reads := fun h => nomatch h

private def rejectedOpening : SourceProgram Unit simpleExpr [] ∅ :=
  .commit 0 () (by decide) rejectGuard <|
  .reveal 1 () 0 (by decide) .here (by decide) <|
  .ret []

private def rejectedPolicy : BehavioralPolicy (who := ()) rejectedOpening :=
  (fun _ _ _ => PMF.pure (some (.success true)), fun _ _ _ => PMF.pure true, PUnit.unit)

private def bound : Config Unit simpleExpr [(0, .commitment () .bool)] :=
  commitSuccessor 0 rejectGuard (Config.initial (Env.empty (CellVal simpleExpr)))
    (some (.success true))

private theorem bound_active : () ∉ bound.defaulted := by
  simp [bound, commitSuccessor, Config.initial, Config.defaulted, DefaultHistory.defaulted,
    DefaultHistory.record]

example : ((rejectedPolicy.normalizeDisclosures rejectedOpening).2.1 rfl
    (bound.view ()) bound_active) =
    PMF.pure false := by
  change (PMF.pure true).map (fun disclose =>
    effectiveDisclosureView 1 (name := 0) .here bound.registry bound.revelations
      (bound.view ()) disclose) = PMF.pure false
  rw [PMF.pure_map, effectiveDisclosureView_observe]
  rfl

example :
    let attempted := revealSuccessor 1 (name := 0) .here bound true
    let withheld := revealSuccessor 1 (name := 0) .here bound false
    (attempted.state, attempted.defaults) = (withheld.state, withheld.defaults) := by
  rfl

example :
    (revealSuccessor 1 (name := 0) .here bound true).history () ≠
      (revealSuccessor 1 (name := 0) .here bound false).history () := by
  simp [revealSuccessor, bound, commitSuccessor, Config.initial, Config.defaulted,
    DefaultHistory.defaulted, DefaultHistory.record]

end
end VegasTests.DisclosureNormalization
