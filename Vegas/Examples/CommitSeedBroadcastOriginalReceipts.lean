/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastRealization
import Vegas.Examples.CommitSeedBroadcastOriginalCompletion
import Vegas.Examples.CommitSeedBroadcastProperPolicy
import Vegas.Pending.PhaseAttemptReceiptSnapshot
import Interaction.ReactiveHistory
import Interaction.ReactiveReceipts
import Interaction.ReactiveRawRoundTrace

/-! # Original binding receipts of terminal survivors -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem original_receipt_transition (selected : app.Scheduler)
    (before after : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some before))
    (joint : Player → Option app.Action)
    (reached : some after ∈ (app.transition initial horizon selected (some before) joint).support)
    (owner : Player)
    (accepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
      before.execution) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
      after.execution := by
  obtain ⟨message, member, sender, attempt, event, receipt⟩ := accepted
  have recalled := app.history_inputRecall initial horizon selected trace owner
  have ownOutput : message ∈ app.outputs (before.execution.recall owner) := by
    rw [← recalled]
    exact List.mem_filter.mpr ⟨member, by simp only [sender, decide_true]⟩
  obtain ⟨next, stateEq, retained⟩ := app.transition_recall_prefix initial horizon selected
    before (some after) joint reached
  have same : next = after := (Option.some.inj stateEq).symm
  subst next
  obtain ⟨entry, remembered, emitted⟩ := List.mem_filterMap.mp ownOutput
  have laterOutput : message ∈ app.outputs (after.execution.recall owner) :=
    List.mem_filterMap.mpr ⟨entry, (retained owner).subset remembered, emitted⟩
  have nextRecall := app.transition_inputRecall initial horizon selected (some before)
    (some after) joint (app.history_inputRecall initial horizon selected trace) reached owner
  have laterMember : message ∈ after.execution.network.inputs := by
    rw [← nextRecall] at laterOutput
    exact (List.mem_filter.mp laterOutput).1
  obtain ⟨ending, endingEq, receipts⟩ := app.transition_receipts_prefix initial horizon selected
    before (some after) joint reached
  have sameEnd : ending = after := (Option.some.inj endingEq).symm
  subst ending
  exact ⟨message, laterMember, sender, attempt, event, receipts.subset receipt⟩

/-- This forward invariant covers every raw transition. A successful
nonarchiving close and a reset use the same original completed snapshot. -/
theorem survivor_original_receipt_or_open (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current))
    (owner : Player) (survives : owner ∉ current.execution.application.current.excluded) :
    current.execution.application.attempt = originalAttempt ∨
      PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
        current.execution := by
  classical
  have invariant : ∀ {state} (_trace : (app.protocol initial horizon selected).Trace state),
      state.elim True (fun control => ∀ who,
        who ∉ control.execution.application.current.excluded →
          control.execution.application.attempt = originalAttempt ∨
            PhaseService.BindingAccepted runtime leaks (originalCoordinate who) who
              control.execution) := by
    intro state history
    induction history with
    | start => trivial
    | @extend source target prior joint _legal reached induction =>
        change target ∈ (app.transition initial horizon selected source joint).support at reached
        cases source with
        | none =>
            obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
            rw [initial] at supported
            cases (PMF.mem_support_pure_iff _ _).mp supported
            intro who _active
            exact Or.inl initialState_attempt
        | some before =>
            obtain ⟨after, rfl, _retained⟩ := app.transition_recall_prefix initial horizon selected
              before target joint reached
            intro who active
            have permanent := (phaseApplication_exclusion_monotone runtime leaks).transition
              initial horizon selected before after joint reached
            have beforeActive : who ∉ before.execution.application.current.excluded :=
              fun excluded => active (permanent excluded)
            rcases induction who beforeActive with original | accepted
            · by_cases same : after.execution.application.attempt = originalAttempt
              · exact Or.inl same
              · have phases := original_phases selected before prior original
                have installed : commitmentPhase ∈ before.execution.application.phases.head? := by
                  rw [phases]
                  rfl
                have changed : after.execution.application.attempt ≠
                    before.execution.application.attempt := by rwa [original]
                have compiledPrior := prior
                rw [initial_eq_compiled] at compiledPrior
                obtain ⟨snapshot, _idle, _normalized, finished, binding, covered, excluded,
                    receipts, _effect, _rawStamp⟩ :=
                  phase_closed_transition_receipt_snapshot runtime leaks
                  plan
                  (setup.initialLaw.map encodeInputs) horizon selected before after compiledPrior
                    joint
                    reached commitmentPhase installed changed
                have inside : bindingEvent who ∈ commitmentPhase.events := by
                  apply (RuntimePhase.mem_events commitmentPhase (bindingEvent who)).mpr
                  fin_cases who <;> decide
                have present : (commitmentPhase.drain snapshot).native.accepted
                    (.inr (bindingEvent who)) ≠ none := by
                  intro missing
                  have missed := ((commitmentPhase.drain snapshot).native.publicView_missedBinding
                    (bindingEvent who) who .bool (bindingEvent_layout who)).mpr
                      ⟨finished inside, missing⟩
                  have acting : graph.actor? (bindingEvent who) = some who := by
                    fin_cases who <;> rfl
                  exact active (excluded ▸ covered.covered (bindingEvent who) who acting
                    (Or.inl missed))
                obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp present
                obtain ⟨_payload, typed⟩ := binding.accepted_typed (.inr (bindingEvent who))
                  candidate accepted
                have owned : candidate.1 = who :=
                  (EventField.binding.inj (typed.symm.trans (bindingEvent_layout who))).1
                have lower : before.execution.application.attempt.phase ≤
                    (bindingEvent who).val := by
                  rw [original]
                  fin_cases who <;> decide
                have receipted := receipts (bindingEvent who) candidate lower accepted
                exact Or.inr (by
                  simpa only [original, owned, originalCoordinate] using receipted)
            · exact Or.inr (original_receipt_transition selected before after prior joint
                reached who accepted)
  exact invariant trace owner survives

/-- A surviving owner at a genuine late raw history has a true receipt in the
original namespace, regardless of later retries or newly excluded opponents. -/
theorem surviving_original_binding_accepted (current : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some current))
    (late : 30 ≤ current.execution.environmentRecall.length) (owner : Player)
    (survives : owner ∉ current.execution.application.current.excluded) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
      current.execution := by
  obtain ⟨seeds, _supported, fixed⟩ := raw_trace_fixed_seed current trace
  have closed := original_attempt_retired seeds current fixed.some late
  exact (survivor_original_receipt_or_open scheduler current trace owner survives).resolve_left
    closed

/-- The actual initialized horizon law inherits the raw-history readback.
No local coverage condition is imposed on any continuation policy. -/
theorem initialized_survivor_original_binding_accepted (players : Player → app.Policy)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds scheduler players horizon initialExecution).support)
    (owner : Player) (survives : owner ∉ final.application.current.excluded) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final := by
  have rounds : final ∈ (app.roundsFrom initial scheduler players horizon).support := by
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind,
      initialExecution] using reached
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom initial horizon scheduler players horizon le_rfl
    final rounds
  have trace : (app.protocol initial horizon scheduler).Trace (some ⟨0, none, final⟩) := by
    simpa only [Nat.sub_self] using trace
  have length := app.runRounds_environmentRecall_length scheduler players horizon initialExecution
    final reached
  have late : 30 ≤ final.environmentRecall.length := by
    change final.environmentRecall.length = 0 + 128 at length
    omega
  exact surviving_original_binding_accepted ⟨0, none, final⟩ trace late owner survives

/-- A terminal original binding miss has permanently excluded its owner.
This conclusion does not replace the separate failed-publication readback. -/
theorem initialized_missing_original_binding_excluded (players : Player → app.Policy)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds scheduler players horizon initialExecution).support)
    (owner : Player)
    (missing : ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
      final) :
    owner ∈ final.application.current.excluded := by
  classical
  by_contra active
  exact missing (initialized_survivor_original_binding_accepted players final reached owner active)

end Vegas.Examples.CommitSeedBroadcast
