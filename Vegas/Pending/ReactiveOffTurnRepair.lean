/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingAuditStep

/-! # Off-turn transmissions in the stopped private repair

The ordinary public checker permits a fresh envelope only from the actor of
a ready event. An idle player, with no ready event of its own, still has its
complete raw response interface. Known replays and silence preserve the paired executions;
every fresh submission supplies an attributed forbidden traffic record.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)

/-- A fresh envelope from an idle sender is rejected. Already published replay
IDs are deliberately excluded here. -/
theorem permittedServiceEnvelope_off_turn (view : PublicView graph)
    (ledger : List (Message Player (WitnessedPacket graph)))
    (message : Message Player (WitnessedPacket graph))
    (unpublished : message.id ∉ ledger.map Message.id)
    (idle : view.Idle message.sender) :
    runtime.permittedServiceEnvelope view ledger message = false := by
  apply Bool.eq_false_iff.mpr
  intro permitted
  have fresh := (runtime.permittedServiceEnvelope_unpublished_iff view ledger message
    unpublished).mp permitted |>.2
  obtain ⟨event, _, ready, actor⟩ := runtime.freshServiceEnvelope_owned view message fresh
  exact idle event ready actor

variable [Fintype Player]
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- All effective responses remain available. Off-turn submission is publicly
attributable, while every supported replay keeps the ordinary known-packet API. -/
theorem off_turn_audit_response_cases (bounds : MessageBounds graph)
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (remaining : Nat) (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (serials : execution.network.SerialsBeforeNext)
    (idle : execution.application.publicView.Idle owner)
    (response : (runtime.reactiveApplication leaks).Action)
    (available : response ∈ (bounds.menu runtime leaks).actions owner (execution.recall owner)
      (execution.observe (runtime.reactiveApplication leaks) owner)) :
    let app := runtime.reactiveApplication leaks
    response ∈ (app.replayPolicy (execution.recall owner) (execution.observe app owner)).support ∨
      ∃ record, app.trafficStep (some ⟨remaining, some owner, execution⟩)
          (some ⟨remaining, none, execution.respond app owner response⟩) = [record] ∧
        record.input.envelope.sender = owner ∧
        runtime.permittedServiceEnvelope record.observation record.ledger
          record.input.envelope = false := by
  classical
  let app := runtime.reactiveApplication leaks
  have member := (bounds.menu_mem runtime leaks owner _ _ response).mp available
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      exact Or.inl (app.replayPolicy_support _ _ none (Finset.mem_insert_self _ _))
  | some transmission =>
      cases transmission with
      | replay id =>
          obtain ⟨message, present, same⟩ :=
            (ReactiveApplication.SubmissionNormalization.replayKnown_iff execution owner
              recalled id).mp member.1
          apply Or.inl
          apply app.replayPolicy_support _ _ (some id)
          apply Finset.mem_insert_of_mem
          apply Finset.mem_image.mpr
          refine ⟨id, ?_, rfl⟩
          apply List.mem_toFinset.mpr
          apply List.mem_map.mpr
          rw [app.known_from_recall execution owner recalled] at present
          exact ⟨message, present, same⟩
      | submit submission =>
          let record : app.TrafficRecord :=
            ⟨execution.application.publicView, execution.network.ledger,
              ⟨owner, ⟨(owner, execution.network.nextSerial owner), submission.emit
                (app.submit execution.application owner submission) owner
                  (execution.network.known owner)⟩⟩⟩
          refine Or.inr ⟨record, app.trafficStep_submit execution remaining owner submission,
            rfl, ?_⟩
          exact runtime.permittedServiceEnvelope_off_turn _ _ _
            (serials.next_unpublished owner) idle

namespace BindingMemory.Frame

variable {runtime leaks} {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- A complete mixed off-turn response uses the same fixed legal private
implementation. Only a supported fresh submission can break the joint frame. -/
theorem off_turn_stopped_response_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph) (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (serials : original.network.SerialsBeforeNext) (remaining : Nat)
    (idle : original.application.publicView.Idle owner)
    (coverage : ∀ response ∈ ((runtime.reactiveApplication leaks).replayPolicy
      (repaired.recall owner) (repaired.observe (runtime.reactiveApplication leaks) owner)).support,
        response ∈ menu.actions owner (repaired.recall owner)
          (repaired.observe (runtime.reactiveApplication leaks) owner))
    (available : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
        response ∈ (bounds.menu runtime leaks).actions owner (original.recall owner)
          (original.observe (runtime.reactiveApplication leaks) owner)) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.invoke players owner original ∧
      coupling.map Prod.snd = strategy.resume owner players (some owner) repaired memory ∧
      ∀ next ∈ coupling.support,
        (∃ record, app.trafficStep (some ⟨remaining, some owner, original⟩)
            (some ⟨remaining, none, next.1⟩) = [record] ∧
          record.input.envelope.sender = owner ∧
          runtime.permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
        (Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length ∧
          next.2.2.shadow = memory.shadow ∧
          next.2.1.application.playerView owner = repaired.application.playerView owner) := by
  classical
  intro app strategy
  let law := players owner (original.recall owner) (original.observe app owner)
  let proposed (response : app.Action) :=
    let changed := memory.repairResponse runtime leaks owner (repaired.observe app owner) response
    (changed.1, (⟨changed.2, memory.responses ++
      [(memory.shadow.inputView runtime leaks (repaired.observe app owner), response)]⟩ :
        BindingMemory runtime leaks))
  let adjusted (response : app.Action) :=
    (if (proposed response).1 ∈ menu.actions owner (repaired.recall owner)
        (repaired.observe app owner) then (proposed response).1
      else (menu.nonempty owner (repaired.recall owner) (repaired.observe app owner)).choose,
      (proposed response).2)
  let coupling := law.map fun response =>
    (original.respond app owner response, repaired.respond app owner (adjusted response).1,
      (adjusted response).2)
  have responseLaw : strategy.respond memory (repaired.recall owner,
      repaired.observe app owner) = law.map adjusted := by
    change ((implementation runtime leaks owner reference (players owner)).respond memory
      (repaired.recall owner, repaired.observe app owner)).map _ = _
    rw [implementation_respond runtime leaks owner reference (players owner) memory
      (repaired.recall owner) (repaired.observe app owner) started, frame.past, frame.observed,
        PMF.map_comp]
    simp only [law, adjusted, proposed, frame.observed, app, Function.comp_def]
  refine ⟨coupling, ?_, ?_, ?_⟩
  · rw [PMF.map_comp]
    rfl
  · rw [PMF.map_comp]
    simp only [ReactiveApplication.Implementation.resume, ↓reduceIte]
    change law.map _ = (strategy.respond memory
      (repaired.recall owner, repaired.observe app owner)).map _
    rw [responseLaw, PMF.map_comp]
    rfl
  · intro next supported
    obtain ⟨response, chosen, rfl⟩ := PMF.support_map .. ▸ supported
    rcases runtime.off_turn_audit_response_cases leaks bounds original owner remaining
        leftRecall serials idle response (available response chosen) with replay | forbidden
    · have unchanged : memory.repairResponse runtime leaks owner
          (repaired.observe app owner) response = (response, memory.shadow) := by
        rcases app.replayPolicy_cases _ _ response replay with rfl | ⟨id, rfl⟩ <;> rfl
      have legal : (proposed response).1 ∈ menu.actions owner (repaired.recall owner)
          (repaired.observe app owner) := by
        dsimp only [proposed]
        rw [unchanged]
        apply coverage
        rw [← app.replayPolicy_eq_of_network_eq original repaired owner leftRecall rightRecall
          frame.network]
        exact replay
      right
      dsimp only [adjusted]
      rw [ite_eq_left legal]
      dsimp only [proposed]
      rw [unchanged]
      refine ⟨frame.transport_response response ?_, ?_, rfl, ?_⟩
      · intro submission
        rcases app.replayPolicy_cases _ _ response replay with rfl | ⟨id, rfl⟩ <;> simp
      · rw [app.respond_recall_length]
        omega
      · rcases app.replayPolicy_cases _ _ response replay with rfl | ⟨id, rfl⟩ <;> rfl
    · exact Or.inl forbidden

end BindingMemory.Frame

end Vegas.EventGraphRuntime
