/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastFailedPreparation
import Vegas.Examples.CommitSeedBroadcastOriginalReceipts
import Vegas.Pending.PhaseNativeFailureExit
import Vegas.Pending.PhaseBindingReceiptResolution
import Vegas.Pending.PhaseAttemptCheckpoint

/-! # Final original admissions preclude every original commitment exclusion -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- All original receipts at a later actual history imply clearance at every
retained original prefix. Later publication exclusions remain unrestricted. -/
theorem original_prefix_clear_of_all_final_receipts
    (selected : app.Scheduler) (current final : app.Control)
    (trace : (countedMenu.protocol initial horizon selected).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt)
    (finalTrace : (countedMenu.protocol initial horizon selected).Trace (some final))
    (retained : TracePrefix trace finalTrace)
    (admitted : ∀ owner, PhaseService.BindingAccepted runtime leaks
      (originalCoordinate owner) owner final.execution) :
    current.execution.application.current.excluded = ∅ := by
  classical
  by_contra failed
  have first := PhaseNativeProjection.exists_first_exclusion_transition runtime leaks plan bounds
    (setup.initialLaw.map encodeInputs) horizon selected (state := some current)
  rw [← initial_eq_compiled] at first
  obtain ⟨before, after, prior, joint, legal, moved, clear, excluded, throughCurrent⟩ :=
    first trace ⟨current, rfl, Finset.nonempty_iff_ne_empty.mpr failed⟩
  have priorToCurrent : TracePrefix prior trace :=
    (TracePrefix.extend .refl joint legal moved).trans throughCurrent
  let rawBefore := countedMenu.toRawTrace initial horizon selected prior
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state member
    rw [initial_eq_compiled, PMF.support_map] at member
    obtain ⟨inputs, _supported, rfl⟩ := member
    exact PhaseRuntimeState.initial_ordered plan inputs
  have beforeOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
    selected initialized rawBefore
  have progress := phase_attempt_progress_of_prefix runtime leaks countedMenu initial initialized
    horizon selected before current prior trace priorToCurrent beforeOrdered
  have beforeOriginal : before.execution.application.attempt = originalAttempt := by
    have generations := progress.1
    have phases := progress.2.1
    change before.execution.application.attempt.generation ≤
      current.execution.application.attempt.generation at generations
    change before.execution.application.attempt.phase ≤
      current.execution.application.attempt.phase at phases
    rw [original] at generations phases
    cases address : before.execution.application.attempt with
    | mk phase generation =>
      simp only [address, originalAttempt] at generations phases ⊢
      congr 1 <;> omega
  have phases := original_phases selected before rawBefore beforeOriginal
  have installed : commitmentPhase ∈ before.execution.application.phases.head? := by
    rw [phases]
    rfl
  obtain ⟨owner, ownerExcluded⟩ := excluded
  have active : owner ∉ before.execution.application.current.excluded := by
    rw [clear]
    exact Finset.notMem_empty owner
  have globalPrefix := throughCurrent.trans retained
  have mapPrefix : ∀ {first second}
      (firstTrace : (countedMenu.protocol initial horizon selected).Trace first)
      (secondTrace : (countedMenu.protocol initial horizon selected).Trace second),
      TracePrefix firstTrace secondTrace → TracePrefix
        (countedMenu.toRawTrace initial horizon selected firstTrace)
        (countedMenu.toRawTrace initial horizon selected secondTrace) := by
    intro first second firstTrace secondTrace kept
    induction kept with
    | refl => exact .refl
    | extend kept actions allowed actual ih =>
      exact TracePrefix.extend ih actions
        (countedMenu.legal_raw initial horizon selected allowed) actual
  have rawPrefix := mapPrefix _ _ globalPrefix
  change TracePrefix (rawBefore.extend joint
      (countedMenu.legal_raw initial horizon selected legal) moved)
        (countedMenu.toRawTrace initial horizon selected finalTrace) at rawPrefix
  have denial := PhaseService.not_bindingAccepted_after_commitment_exclusion runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon selected
  rw [← initial_eq_compiled] at denial
  obtain ⟨event, inside, request, absent⟩ := denial before after final rawBefore joint
    (countedMenu.legal_raw initial horizon selected legal) moved
      (countedMenu.toRawTrace initial horizon selected finalTrace) rawPrefix commitmentPhase
        installed rfl owner active ownerExcluded
  have eventEq : event = bindingEvent owner := by
    rcases owned_event_cases event owner request.2.2.2.1 with binding | publication
    · exact binding
    · have interval := (RuntimePhase.mem_events commitmentPhase event).mp inside
      rw [publication] at interval
      change 0 ≤ (revealEvent owner).val ∧ (revealEvent owner).val < 3 at interval
      change 0 ≤ owner.val + 3 ∧ owner.val + 3 < 3 at interval
      omega
  have missing : ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
      final.execution := by
    simpa only [beforeOriginal, eventEq, originalCoordinate] using absent
  exact missing (admitted owner)

/-- The transition that leaves the original commitment cannot itself create an
exclusion when every original receipt is retained at the later history. -/
theorem original_transition_clear_of_all_final_receipts
    (selected : app.Scheduler) (before after final : app.Control)
    (prior : (countedMenu.protocol initial horizon selected).Trace (some before))
    (original : before.execution.application.attempt = originalAttempt)
    (joint : Player → Option app.Action)
    (legal : (countedMenu.protocol initial horizon selected).Legal (some before) joint)
    (moved : some after ∈ (app.transition initial horizon selected (some before) joint).support)
    (finalTrace : (countedMenu.protocol initial horizon selected).Trace (some final))
    (retained : TracePrefix (prior.extend joint legal moved) finalTrace)
    (admitted : ∀ owner, PhaseService.BindingAccepted runtime leaks
      (originalCoordinate owner) owner final.execution) :
    after.execution.application.current.excluded = ∅ := by
  classical
  have clear := original_prefix_clear_of_all_final_receipts selected before final prior original
    finalTrace ((TracePrefix.extend .refl joint legal moved).trans retained) admitted
  by_contra failed
  obtain ⟨owner, excluded⟩ := Finset.nonempty_iff_ne_empty.mpr failed
  have phases := original_phases selected before
    (countedMenu.toRawTrace initial horizon selected prior) original
  have installed : commitmentPhase ∈ before.execution.application.phases.head? := by
    rw [phases]
    rfl
  have mapPrefix : ∀ {first second}
      (firstTrace : (countedMenu.protocol initial horizon selected).Trace first)
      (secondTrace : (countedMenu.protocol initial horizon selected).Trace second),
      TracePrefix firstTrace secondTrace → TracePrefix
        (countedMenu.toRawTrace initial horizon selected firstTrace)
        (countedMenu.toRawTrace initial horizon selected secondTrace) := by
    intro first second firstTrace secondTrace kept
    induction kept with
    | refl => exact .refl
    | extend kept actions allowed actual ih =>
      exact TracePrefix.extend ih actions
        (countedMenu.legal_raw initial horizon selected allowed) actual
  have rawPrefix := mapPrefix _ _ retained
  have denial := PhaseService.not_bindingAccepted_after_commitment_exclusion runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon selected
  rw [← initial_eq_compiled] at denial
  obtain ⟨event, inside, request, absent⟩ := denial before after final
    (countedMenu.toRawTrace initial horizon selected prior) joint
    (countedMenu.legal_raw initial horizon selected legal) moved
    (countedMenu.toRawTrace initial horizon selected finalTrace) rawPrefix commitmentPhase
    installed rfl owner (by rw [clear]; exact Finset.notMem_empty _) excluded
  have eventEq : event = bindingEvent owner := by
    rcases owned_event_cases event owner request.2.2.2.1 with binding | publication
    · exact binding
    · have interval := (RuntimePhase.mem_events commitmentPhase event).mp inside
      rw [publication] at interval
      change 0 ≤ owner.val + 3 ∧ owner.val + 3 < 3 at interval
      omega
  have missing : ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
      final.execution := by
    simpa only [original, eventEq, originalCoordinate] using absent
  exact missing (admitted owner)

end Vegas.Examples.CommitSeedBroadcast
