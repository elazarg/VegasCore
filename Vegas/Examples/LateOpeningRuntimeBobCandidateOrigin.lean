/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobFreshBinding

/-! # Actual owner responses account for consumed prepared handles

An occupied receiver slot at a reachable native state has an actual earlier
receiver response naming that slot. This is obtained from the existing candidate
recall invariant, including after arbitrary malformed responses.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobCandidateOrigin

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService

/-- No foreign response or environmental inclusion can consume a fresh Bob
prepared handle without an earlier Bob response naming its serial. -/
theorem consumed_slot_has_response (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (serial : Nat)
    (consumed : control.execution.application.candidates.lookup
      (bob, .prepared serial) ≠ .fresh) :
    ∃ entry ∈ control.execution.recall bob,
      LateOpeningRuntimeService.runtime.responseCandidateSlot leaks entry.action = some serial := by
  classical
  have initialEq : (setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph)) = initial := by
    exact (PMF.map_comp _ _ _).trans rfl
  have inputTrace : (app.protocol
      ((setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := nativeGraph)))
      LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control) := by
    exact initialEq.symm ▸ trace
  have valid := LateOpeningRuntimeService.runtime.candidateRecall_history leaks
    (setup.initialLaw.map setup.eventInputs) LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) inputTrace
  change LateOpeningRuntimeService.runtime.CandidateRecall leaks control.execution at valid
  have named : serial ∈ LateOpeningRuntimeService.runtime.submittedCandidateSlots leaks
      (control.execution.recall bob) := by
    by_contra absent
    exact consumed (valid bob serial absent)
  unfold submittedCandidateSlots at named
  obtain ⟨response, present, selected⟩ := List.mem_filterMap.mp named
  obtain ⟨entry, member, same⟩ := List.mem_map.mp present
  refine ⟨entry, member, ?_⟩
  rw [same]
  exact selected

end Vegas.Examples.LateOpeningRuntimeBobCandidateOrigin
