/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphAssembly
import Vegas.EventGraph.BarrierInformation
import VegasTests.SourceSemantics

/-! # Source-to-event compilation regressions

Compiler-generated dependencies permit distinct players' bindings to complete
in either order while retaining source public-observation barriers. A mixed
source program checks heterogeneous results, initial secrets and public chance.
-/

namespace VegasTests.EventCompilation

open Vegas
open SourceProgram.EventLowering
open GameTheory.Math.Probability

noncomputable section

private def unrestricted {Γ : SourceCtx Bool simpleExpr} (owner : Bool) (name : VarId) :
    SourceGuard simpleExpr Γ owner name .bool where
  schema := []
  schemaNames := by simp
  subjectFresh := by simp
  code := .constBool true
  reads := fun source => nomatch source

private def pairSource : SourceProgram Bool simpleExpr [] ∅ :=
  .commit 0 false (by decide) (unrestricted false 0) <|
  .commit 1 true (by decide) (unrestricted true 1) <|
  .reveal 2 false 0 (by decide) (.there .here) (by decide) <|
  .reveal 3 true 1 (by decide) (.there .here) (by decide) <|
  .ret []

private abbrev pairOrder := Vegas.EventGraph.barrierOrder (outputLayout pairSource)

private def pairGraph := toEventGraph pairSource (by decide)

private def pairConfig : pairGraph.Config := .initial (fun input => nomatch input)

private abbrev first : pairGraph.EventId := ⟨0, by decide⟩
private abbrev second : pairGraph.EventId := ⟨1, by decide⟩

private theorem first_ready : pairConfig.cut.Ready first := by decide

private theorem second_ready : pairConfig.cut.Ready second := by decide

/-- These are the compiler's actual certified nodes, not a hand-built graph. -/
example : pairGraph.InformationDiscipline pairGraph.prefixSchema :=
  toEventGraph_informationDiscipline pairSource (by decide)

private def completedSecond : pairGraph.Config :=
  pairConfig.complete second second_ready (.success true) (.success true)

/-- A real semantic step accepts the second source commitment first. -/
private theorem step_second :
    pairConfig.step second second_ready (.success true) = FinDist.pure completedSecond := by
  change (FinDist.pure (PublicationResult.success true)).map _ = _
  rw [FinDist.map_pure]
  rfl

example : completedSecond.history.map Vegas.EventGraph.Completion.event = [second] := rfl

example : completedSecond.cut.Ready first :=
  first_ready.after_complete second_ready (by decide)

example : completedSecond ∈ (pairConfig.step second second_ready (.success true)).support := by
  rw [step_second]
  exact FinDist.mem_support_pure.mpr rfl

example : eventCount pairSource = 4 := rfl

/-- Compilation creates two initially enabled bindings, not a global cursor. -/
example : (EventOrder.Cut.empty pairOrder).enabled =
    {⟨0, by decide⟩, ⟨1, by decide⟩} := by decide

private def secondBound : pairOrder.Cut :=
  (EventOrder.Cut.empty pairOrder).complete ⟨1, by decide⟩ (by decide)

example : ⟨1, by decide⟩ ∈ secondBound.completed ∧
    ⟨0, by decide⟩ ∉ secondBound.completed := by decide

/-- Neither public result is enabled until both earlier bindings are complete. -/
example : ¬ secondBound.Ready ⟨2, by decide⟩ ∧
    ¬ secondBound.Ready ⟨3, by decide⟩ := by decide

example : (secondBound.complete ⟨0, by decide⟩ (by decide)).Ready ⟨2, by decide⟩ := by decide

example : ¬ (secondBound.complete ⟨0, by decide⟩ (by decide)).Ready ⟨3, by decide⟩ := by decide

/-- The typed catalog retains the original optional payload separately from
the failure-aware publication result. -/
example : outputLayout SourceSemantics.mixedProgram ⟨0, by decide⟩ =
    .binding SourceSemantics.Player.alice (.option .bool) := rfl

example : outputLayout SourceSemantics.mixedProgram ⟨1, by decide⟩ =
    .publication (.option .bool) := rfl

example : outputLayout SourceSemantics.mixedProgram ⟨2, by decide⟩ = .publication .bool := rfl

example : outputLayout SourceSemantics.mixedProgram ⟨3, by decide⟩ = .publicData .bool := rfl

/-- The complete mixed source compiles with its initial private input and
deferred guard; no sample-free or homogeneous-payload restriction is needed. -/
example : SourceSemantics.mixedInitial.eventGraph.InformationDiscipline
    SourceSemantics.mixedInitial.eventGraph.prefixSchema :=
  toEventGraph_informationDiscipline SourceSemantics.mixedInitial.program
    SourceSemantics.mixedInitial.namesNodup

example : SourceSemantics.mixedInitial.eventGraph.order.eventCount = 4 := rfl

/-- Private initial values are graph inputs rather than another player move. -/
example : inputLayout SourceSemantics.mixedInitial.context ⟨0, by decide⟩ =
    .binding SourceSemantics.Player.alice .bool := rfl

example : encodeInputs SourceSemantics.mixedInitial.state ⟨0, by decide⟩ =
    PublicationResult.success true := rfl

private def rejectingGraph := toEventGraph SourceSemantics.falseGuardProgram (by decide)

private abbrev rejectingBind : rejectingGraph.EventId := ⟨0, by decide⟩
private abbrev rejectingReveal : rejectingGraph.EventId := ⟨1, by decide⟩

private def rejectingInitial : rejectingGraph.Config :=
  .initial (fun input => nomatch input)

private def rejectingBound : rejectingGraph.Config :=
  rejectingInitial.complete rejectingBind (by decide)
    (PublicationResult.success true) (PublicationResult.success true)

/-- An unsatisfiable guard compiles, and its reveal computes failure. It is not
silently replaced by an unrestricted commitment or a valid in-domain value. -/
example : (rejectingGraph.nodes rejectingReveal).eval? true rejectingBound.store =
    some (FinDist.pure (PublicationResult.failure : PublicationResult Bool)) := rfl

end

end VegasTests.EventCompilation
