/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalBindingAcceptance
import Vegas.Examples.CommitSeedBroadcastHelperOriginalObservation
import Vegas.Examples.CommitSeedBroadcastProperPolicy

/-! # Original admission completion in the actual pre-expiry observation -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

/-- Before the first original expiry, retirement of the original attempt is
equivalent to all three actual accepting receipts. Raw actions and hidden
preparations are unrestricted. No terminal-survival converse is assumed. -/
theorem original_retired_iff_all_binding_accepted (seed : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seed)).Trace (some current))
    (early : current.execution.environmentRecall.length < 28) :
    current.execution.application.attempt ≠ originalAttempt ↔
      ∀ owner, PhaseService.BindingAccepted runtime leaks (originalCoordinate owner)
        owner current.execution := by
  constructor
  · intro retired owner
    by_contra missing
    have request := original_request_of_unaccepted_before_expiry seed current trace owner
      missing early
    exact retired request.1.symm
  · intro admitted original
    have phases := original_phases (family seed) current trace original
    have live := (raw_phase_geometry (family seed) current trace).2.1
    have unfinished := live commitmentPhase (by rw [phases]; rfl)
    apply unfinished
    intro event member
    have inside := (RuntimePhase.mem_events commitmentPhase event).mp member
    have bound : event.val < 3 := inside.2
    let owner : Player := ⟨event.val, bound⟩
    have named : bindingEvent owner = event := by apply Fin.ext; rfl
    have compiled := trace
    rw [initial_eq_compiled] at compiled
    have resolved := PhaseService.bindingAccepted_resolved runtime leaks plan
      (setup.initialLaw.map encodeInputs) horizon (family seed) compiled
      (originalCoordinate owner) owner (admitted owner)
    rcases resolved with generation | phase | ⟨_same, completed⟩
    · have impossible := generation
      rw [original] at impossible
      exact (Nat.lt_irrefl _ impossible).elim
    · have impossible := phase
      rw [original] at impossible
      exact (Nat.lt_irrefl _ impossible).elim
    · exact named ▸ completed

/-- At the end of the late inclusions, the original helper channel records
all-original admission by its retirement branch. Later publication data stay
outside that channel; this equivalence uses only the actual pre-expiry prefix. -/
theorem original_helper_observation_none_iff_admitted (seed : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seed)).Trace (some current))
    (early : current.execution.environmentRecall.length < 28) (hidden : Player) :
    originalHelperObservation hidden current.execution = none ↔
      ∀ owner, PhaseService.BindingAccepted runtime leaks (originalCoordinate owner)
        owner current.execution := by
  have retired := original_retired_iff_all_binding_accepted seed current trace early
  by_cases original : current.execution.application.attempt = originalAttempt
  · simp only [originalHelperObservation, original, ite_true, reduceCtorEq]
    exact (iff_false_intro (fun admitted => (retired.mpr admitted) original)).symm
  · simp only [originalHelperObservation, original, ite_false]
    exact (iff_true_intro (retired.mp original)).symm

end Vegas.Examples.CommitSeedBroadcast
