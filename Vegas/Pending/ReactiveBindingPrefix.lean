/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingAllocation

/-! # Canonical handle allocation through clean service constructors

Protected binding inclusion advances exactly its owner's public allocation
counter. Every other owner's catalog and counter remain unchanged. Public
completions allocate no private handle. These are operational induction steps
for the clean service prefix, including privately unusable canonical bindings.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem State.PreparedPrefix.complete_public {state : State graph} {who : Player}
    (allocated : state.PreparedPrefix who) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value)
    (publicOutput : (graph.outputLayout event).IsPublic) :
    (state.complete event ready action value).PreparedPrefix who := by
  have count : (state.complete event ready action value).publicView.bindingCount who =
      state.publicView.bindingCount who := by
    simp only [PublicView.bindingCount, State.publicView, State.complete, publicObserve,
      Config.complete_history, List.map_append, List.map_cons, List.map_nil,
      List.countP_append, List.countP_cons, List.countP_nil]
    cases outputEq : graph.outputLayout event <;> simp_all [EventField.IsPublic]
  intro serial
  rw [count]
  exact allocated serial

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Every player's public allocation invariant survives the real binding
submission and reserved inclusion, regardless of hidden raw material. -/
theorem rawBinding_reserved_all_preparedPrefix
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (opening : Option (Raw L))
    (allocated : ∀ who, execution.application.PreparedPrefix who)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (vacant : execution.application.accepted (.inr event) = none)
    (unused : execution.application.HandleUnused
      (owner, .prepared (execution.application.publicView.bindingCount owner)))
    (serials : execution.network.SerialsBeforeNext)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : runtime.NetworkPolicy leaks)
    (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈
      (runtime.interactionStep leaks players scheduler (.includeLatest event owner)
        (execution.respond (runtime.reactiveApplication leaks) owner
          ⟨some (.submit ⟨⟨.commitment event
            (owner, .prepared (execution.application.publicView.bindingCount owner)), opening⟩,
              .none⟩)⟩)).support) :
    ∀ who, final.application.PreparedPrefix who := by
  intro who
  by_cases acting : who = owner
  · subst who
    exact runtime.rawBinding_reserved_preparedPrefix leaks execution owner event payload
      outputEq codeEq node opening (allocated owner) ready timely vacant unused serials
        players scheduler final reached
  let app := runtime.reactiveApplication leaks
  let serial := execution.application.publicView.bindingCount owner
  let material : WitnessedSubmission graph :=
    ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩
  let submitted := execution.respond app owner ⟨some (.submit material)⟩
  let id := (owner, execution.network.nextSerial owner)
  have fresh : execution.application.candidates.lookup (owner, .prepared serial) = .fresh :=
    (allocated owner serial).mpr (Nat.le_refl _)
  have resultLaw := runtime.rawBinding_reserved_config leaks execution owner event payload
    outputEq codeEq node serial opening ready timely fresh vacant unused serials players scheduler
  have mapped : (final.application.config, final.receipts) ∈
      ((runtime.interactionStep leaks players scheduler (.includeLatest event owner)
        submitted).map fun next => (next.application.config, next.receipts)).support :=
    PMF.support_map .. ▸ ⟨final, reached, rfl⟩
  rw [resultLaw, PMF.mem_support_pure_iff _ _] at mapped
  have configEq := congrArg Prod.fst mapped
  dsimp only [Prod.fst] at configEq
  have selected : runtime.interactionStep leaks players scheduler (.includeLatest event owner)
      submitted = submitted.environmentStep app (.include id) := by
    have chosen := runtime.reactiveLatest_after_submit leaks owner event execution serials
      material rfl
    unfold interactionStep
    rw [interactionInstruction, chosen, PMF.pure_bind]
    simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
    exact PMF.bind_pure _
  have found : submitted.network.lookup id =
      some ⟨id, ⟨.commitment event (owner, .prepared serial), none⟩⟩ :=
    serials.lookup_submit owner ⟨.commitment event (owner, .prepared serial), none⟩
  have fixed : submitted.application.candidates.lookup (owner, .prepared serial) ≠ .fresh :=
    submitStep_commitment_fixed _ owner event (.prepared serial)
  have unchanged := runtime.reactive_include_fixed_binding_candidates leaks submitted id event
    (owner, .prepared serial) none found fixed
  have candidates : final.application.candidates = submitted.application.candidates := by
    change final ∈ (runtime.interactionStep leaks players scheduler
      (.includeLatest event owner) submitted).support at reached
    rw [selected] at reached
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.mem_support_pure_iff _ _] at reached
    rw [reached]
    exact unchanged
  have count : final.application.publicView.bindingCount who =
      execution.application.publicView.bindingCount who := by
    change (graph.publicObserve final.application.config).completionOrder.countP _ = _
    rw [configEq]
    simp [EventGraph.publicObserve, outputEq, PublicView.bindingCount, State.publicView,
      Ne.symm acting]
  have foreign (query : CandidateSlot graph) :
      submitted.application.candidates.lookup (who, query) =
        execution.application.candidates.lookup (who, query) := by
    change (submitStep (material.call.register execution.application owner) owner
      material.call.packet).candidates.lookup (who, query) = _
    rw [submitStep_lookup_other _ owner who acting]
    exact congrFun (congrArg PlayerView.candidates
      (material.call.register_other execution.application owner who acting)) query
  intro query
  rw [candidates, foreign, count]
  exact allocated who query

end Vegas.EventGraphRuntime
