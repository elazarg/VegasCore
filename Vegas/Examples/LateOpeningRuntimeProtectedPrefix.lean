/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeProtectedRecall
import Vegas.Examples.LateOpeningRuntimeBindingPrefix

/-! # Protected transmissions have zero clean-information prefix mass

The actual behavioral prefix law includes every raw protected response.
A Bob information class retaining an empty-receipt observation at positive
clock assigns exactly zero prefix mass to protected Alice transmissions.
No strategy restriction or lower bound on the observation's mass is used.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeProtectedPrefix

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService
  LateOpeningRuntimeProtectedRecall LateOpeningRuntimeBindingPrefix

/-- A raw transmission remembered at the clock-zero Alice callback. -/
def ProtectedSubmission : app.ProtocolState → Prop
  | none => False
  | some control => ∃ entry ∈ control.execution.recall alice,
      entry.beforeView.application.publicView.clock = 0 ∧ entry.action.transmission.isSome

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1) (control : app.Control)
  (current : representative.1.state = some control) (active : control.actor = some bob)
  (remembered : app.PlayerEntry) (member : remembered ∈ control.execution.recall bob)
  (later : 0 < remembered.beforeView.application.publicView.clock)
  (empty : remembered.beforeView.receipts = [])

include current active member later empty in
/-- Protected transmissions contribute exactly zero to this actual full
information event, even along arbitrary fully mixed approximation profiles. -/
theorem protected_submission_event_zero
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who) :
    (bindingPrefix weight nonnegative profile).toOuterMeasure
      {state | app.observe bob state = site.1 ∧ ProtectedSubmission state} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro state supported selected
  rw [← binding_prefix_law weight nonnegative profile, PMF.support_map] at supported
  obtain ⟨history, _running, rfl⟩ := supported
  rcases selected with ⟨observed, transmitted⟩
  have information : (LateOpeningRuntimeNash.model weight nonnegative).infoOf bob history.trace =
      site.1 := (rawMenu.info initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) bob history.trace).trans observed
  let actual : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1 :=
    ⟨history, information⟩
  obtain ⟨compatible, stateEq, silence⟩ := information_histories_protected_silent weight nonnegative
    site representative control current active remembered member later empty actual
  change history.state = some compatible at stateEq
  rw [stateEq] at transmitted
  obtain ⟨entry, recalled, clockZero, issued⟩ := transmitted
  rw [silence entry recalled clockZero] at issued
  cases issued

end Vegas.Examples.LateOpeningRuntimeProtectedPrefix
