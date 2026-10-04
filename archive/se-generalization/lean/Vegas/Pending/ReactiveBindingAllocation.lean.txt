/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveUnusableBinding

/-! # Public allocation of canonical commitment handles

At a clean protected prefix, the next prepared serial is the number of this
owner's completed bindings. Both valid and unusable private material consume
exactly one serial. The auditor reads the public completion list; it does not
inspect a private candidate catalog.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def PublicView.bindingCount (view : PublicView graph) (who : Player) : Nat :=
  view.observation.completionOrder.countP fun event =>
    match graph.outputLayout event with
    | .binding owner _ => decide (owner = who)
    | .publicData _ | .privateInput _ _ | .publication _ => false

def State.PreparedPrefix (state : State graph) (who : Player) : Prop :=
  ∀ serial, state.candidates.lookup (who, .prepared serial) = .fresh ↔
    state.publicView.bindingCount who ≤ serial

theorem State.preparedPrefix_initial (inputs : graph.Inputs) (who : Player) :
    (State.initial inputs).PreparedPrefix who := by
  intro serial
  rw [State.initial_candidate]
  simp [PublicView.bindingCount, State.publicView, State.initial,
    EventGraph.publicObserve, EventGraph.Config.initial]

theorem State.PreparedPrefix.freshSlot {state : State graph} {who : Player}
    (prefixFresh : state.PreparedPrefix who)
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    reactiveFreshSlot ((runtime.reactiveApplication leaks).observePlayer state who) =
      some (state.publicView.bindingCount who) := by
  classical
  have existsFresh : ∃ serial, state.candidates.lookup (who, .prepared serial) = .fresh :=
    ⟨state.publicView.bindingCount who, (prefixFresh _).mpr (Nat.le_refl _)⟩
  unfold reactiveFreshSlot
  change (if fresh : ∃ serial,
      state.candidates.lookup (who, .prepared serial) = .fresh then
    some (Nat.find fresh) else none) = _
  rw [dite_eq_left existsFresh]
  apply congrArg some
  apply Nat.le_antisymm
  · exact Nat.find_min' existsFresh ((prefixFresh _).mpr (Nat.le_refl _))
  · exact (prefixFresh _).mp (Nat.find_spec existsFresh)

theorem State.bindingCount_complete (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) (owner who : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload) :
    (state.complete event ready action value).publicView.bindingCount who =
      state.publicView.bindingCount who + if owner = who then 1 else 0 := by
  simp [PublicView.bindingCount, State.publicView, State.complete, EventGraph.publicObserve,
    binding]

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem submitted_binding_fresh_iff
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (event : graph.EventId) (serial : Nat) (opening : Option (Raw L))
    (query : CandidateSlot graph) :
    let response : (runtime.reactiveApplication leaks).Action :=
      ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩
    let submitted := execution.respond (runtime.reactiveApplication leaks) who response
    submitted.application.candidates.lookup (who, query) = .fresh ↔
      query ≠ .prepared serial ∧
        execution.application.candidates.lookup (who, query) = .fresh := by
  let material : Submission graph := ⟨.commitment event (who, .prepared serial), opening⟩
  change (submitStep (material.register execution.application who) who
    material.packet).candidates.lookup (who, query) = .fresh ↔ _
  rw [material.candidateAfter_eq]
  by_cases selected : query = .prepared serial
  · subst query
    cases fixed : execution.application.candidates.lookup (who, .prepared serial) <;>
      cases opening <;> simp [material, Submission.candidateAfter, fixed]
  · simp [material, Submission.candidateAfter, selected]

/-- Actual submission and reserved inclusion advance the public allocation
counter exactly once, independently of whether the private material is usable.
The invariant is only asserted at these completed protected prefixes. -/
theorem rawBinding_reserved_preparedPrefix
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (opening : Option (Raw L))
    (prefixFresh : execution.application.PreparedPrefix who)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (vacant : execution.application.accepted (.inr event) = none)
    (unused : execution.application.HandleUnused
      (who, .prepared (execution.application.publicView.bindingCount who)))
    (serials : execution.network.SerialsBeforeNext)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : runtime.NetworkPolicy leaks)
    (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈
      (runtime.interactionStep leaks players scheduler (.includeLatest event who)
        (execution.respond (runtime.reactiveApplication leaks) who
          ⟨some ⟨⟨.commitment event
            (who, .prepared (execution.application.publicView.bindingCount who)), opening⟩,
              .none⟩⟩)).support) :
    final.application.PreparedPrefix who := by
  let app := runtime.reactiveApplication leaks
  let serial := execution.application.publicView.bindingCount who
  let material : WitnessedSubmission graph :=
    ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩
  let submitted := execution.respond app who ⟨some material⟩
  let id := (who, execution.network.nextSerial who)
  have fresh : execution.application.candidates.lookup (who, .prepared serial) = .fresh :=
    (prefixFresh serial).mpr (Nat.le_refl _)
  have resultLaw := runtime.rawBinding_reserved_config leaks execution who event payload
    outputEq codeEq node serial opening ready timely fresh vacant unused serials players scheduler
  have mapped : (final.application.config, final.receipts) ∈
      ((runtime.interactionStep leaks players scheduler (.includeLatest event who)
        submitted).map fun next => (next.application.config, next.receipts)).support :=
    PMF.support_map .. ▸ ⟨final, reached, rfl⟩
  rw [resultLaw, PMF.mem_support_pure_iff _ _] at mapped
  have configEq := congrArg Prod.fst mapped
  dsimp only [Prod.fst] at configEq
  have selected : runtime.interactionStep leaks players scheduler (.includeLatest event who)
      submitted = submitted.environmentStep app (.include id) := by
    have chosen := runtime.reactiveLatest_after_submit leaks who event execution serials
      material rfl
    unfold interactionStep
    rw [interactionInstruction, chosen, PMF.pure_bind]
    simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
    exact PMF.bind_pure _
  have found := respond_submit_lookup runtime leaks execution who material.call serials
  have fixed : submitted.application.candidates.lookup (who, .prepared serial) ≠ .fresh :=
    submitStep_commitment_fixed _ who event (.prepared serial)
  have unchanged := runtime.reactive_include_fixed_binding_candidates leaks submitted id event
    (who, .prepared serial) none found fixed
  have candidates : final.application.candidates = submitted.application.candidates := by
    change final ∈ (runtime.interactionStep leaks players scheduler
      (.includeLatest event who) submitted).support at reached
    rw [selected] at reached
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.mem_support_pure_iff _ _] at reached
    rw [reached]
    exact unchanged
  have count : final.application.publicView.bindingCount who = serial + 1 := by
    change (graph.publicObserve final.application.config).completionOrder.countP _ = _
    rw [configEq]
    simp [EventGraph.publicObserve, outputEq, serial, PublicView.bindingCount, State.publicView]
  intro query
  have slotLaw := runtime.submitted_binding_fresh_iff leaks execution who event serial
    opening (.prepared query)
  change submitted.application.candidates.lookup (who, .prepared query) = .fresh ↔ _ at slotLaw
  rw [candidates, slotLaw, count, prefixFresh query]
  change Slot.prepared query ≠ Slot.prepared serial ∧ serial ≤ query ↔ serial + 1 ≤ query
  simp only [ne_eq, Slot.prepared.injEq]
  omega

end Vegas.EventGraphRuntime
