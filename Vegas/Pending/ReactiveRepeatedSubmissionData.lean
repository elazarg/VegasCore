/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRepeatedSubmissionWindow
import Vegas.Pending.ReactiveBindingForeignData
import Vegas.Pending.ReactiveServiceTraffic

/-! # Pending binding data on branches without a repeated-submission alarm

The owner may be activated repeatedly. If the final actual transcript contains
no rejected owner record, all those later owner responses were transport, so
the original candidate and its reserved envelope survive. Foreign traffic and
passive reads remain arbitrary.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

omit [Fintype Player] in
private theorem response_owner_data
    (execution : (runtime.reactiveApplication leaks).Execution) (owner actor : Player)
    (safe : Message Player (WitnessedPacket graph) → Prop)
    (foreign : ∀ message, message.sender ≠ owner → safe message)
    (packets : execution.network.Satisfies safe)
    (response : (runtime.reactiveApplication leaks).Action)
    (transport : actor = owner → ∀ material, response.transmission ≠ some (.submit material)) :
    let next := execution.respond (runtime.reactiveApplication leaks) actor response
    next.application.playerView owner = execution.application.playerView owner ∧
      next.network.ledger = execution.network.ledger ∧ next.receipts = execution.receipts ∧
      next.network.Satisfies safe ∧ execution.network.pending ⊆ next.network.pending ∧
      next.network.nextSerial owner = execution.network.nextSerial owner := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact ⟨rfl, rfl, rfl, packets, List.Subset.refl _, rfl⟩
  | some transmission =>
      cases transmission with
      | submit material =>
          have different : actor ≠ owner := fun same => transport same material rfl
          refine ⟨?_, rfl, rfl, packets.submit actor _ (foreign _ different), ?_, ?_⟩
          · exact (submitStep_playerView_other (material.call.register execution.application actor)
              actor owner different.symm material.call.packet).trans
                (material.call.register_other execution.application actor owner different.symm)
          · exact fun _ member => List.mem_append_left _ member
          · simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit,
              Ne.symm different, ↓reduceIte]
      | replay id =>
          refine ⟨rfl, ?_, rfl, packets.replay actor id, ?_, ?_⟩
          · change (execution.network.replay actor id).2.ledger = execution.network.ledger
            unfold MessageNetwork.replay
            split <;> rfl
          · change execution.network.pending ⊆ (execution.network.replay actor id).2.pending
            unfold MessageNetwork.replay
            split
            · exact List.Subset.refl _
            · exact fun _ member => List.mem_append_left _ member
          · change (execution.network.replay actor id).2.nextSerial owner = _
            unfold MessageNetwork.replay
            split <;> rfl

private theorem activation_clean_data
    (bounds : MessageBounds graph)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (execution next : (runtime.reactiveApplication leaks).Execution) (owner actor : Player)
    (safe : Message Player (WitnessedPacket graph) → Prop)
    (foreign : ∀ message, message.sender ≠ owner → safe message)
    (packets : execution.network.Satisfies safe)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (serials : execution.network.SerialsBeforeNext)
    (repeated : execution.network.nextSerial owner ≠
      execution.network.ledger.countP (fun message => message.sender = owner))
    (available : ∀ past view response, response ∈ (players owner past view).support →
      response ∈ (bounds.menu runtime leaks).actions owner past view)
    (reached : next ∈ ((runtime.reactiveApplication leaks).dispatch players (.activate actor)
      execution).support)
    (clean : ∀ record ∈ (runtime.reactiveApplication leaks).executionTraffic next,
      record.input.envelope.sender = owner →
        runtime.permittedServiceEnvelope record.observation record.ledger
          record.input.envelope = true) :
    next.application.playerView owner = execution.application.playerView owner ∧
      next.network.ledger = execution.network.ledger ∧ next.receipts = execution.receipts ∧
      next.network.Satisfies safe ∧ execution.network.pending ⊆ next.network.pending ∧
      next.network.nextSerial owner = execution.network.nextSerial owner ∧
      next.InputRecall (runtime.reactiveApplication leaks) ∧ next.network.SerialsBeforeNext := by
  let app := runtime.reactiveApplication leaks
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  obtain ⟨response, chosen, rfl⟩ := FinDist.support_map .. ▸ resumed
  have activated := moved
  rw [ReactiveApplication.Execution.activation_samples] at activated
  obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ activated
  let middle := execution.sampledActivation app actor selected
  have middleRecall : middle.InputRecall app := recalled
  have middleSerials : middle.network.SerialsBeforeNext := serials.learn actor selected
  have transport : actor = owner → ∀ material,
      response.transmission ≠ some (.submit material) := by
    intro same
    subst actor
    rcases runtime.repeated_submission_response_cases leaks bounds middle owner 0 middleRecall
        middleSerials repeated response (available _ _ response chosen) with replay | bad
    · intro material
      rcases app.replayPolicy_cases _ _ response replay with rfl | ⟨id, rfl⟩ <;> simp
    · obtain ⟨record, step, authored, rejected⟩ := bad
      have present : record ∈ app.executionTraffic (middle.respond app owner response) := by
        rw [app.executionTraffic_activated_response execution middle owner response 0 moved]
        apply List.mem_append_right
        change record ∈ app.trafficStep (some ⟨0, some owner, middle⟩)
          (some ⟨0, none, middle.respond app owner response⟩)
        rw [step]
        exact List.mem_singleton_self _
      have accepted := clean record present authored
      rw [rejected] at accepted
      cases accepted
  have data := runtime.response_owner_data leaks middle owner actor safe foreign
    (packets.learn actor selected) response transport
  exact ⟨data.1, data.2.1, data.2.2.1, data.2.2.2.1, data.2.2.2.2.1,
    data.2.2.2.2.2, app.respond_inputRecall middle actor response middleRecall,
    (app.serialsBeforeNextInvariant (fun _ _ => FinDist.pure .wait)).respond
      middle actor response middleSerials⟩

/-- Conditional on the actual final transcript being clean for this author,
the whole arbitrary roster preserves the binding candidate and its pending
envelope constraints. This is proved from raw responses, not assumed as a
conforming-opponent premise. -/
theorem repeated_window_clean_data
    (bounds : MessageBounds graph)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (owner : Player)
    (safe : Message Player (WitnessedPacket graph) → Prop)
    (foreign : ∀ message, message.sender ≠ owner → safe message)
    (visits : List Player) (initial final : (runtime.reactiveApplication leaks).Execution)
    (packets : initial.network.Satisfies safe)
    (recalled : initial.InputRecall (runtime.reactiveApplication leaks))
    (serials : initial.network.SerialsBeforeNext)
    (repeated : initial.network.nextSerial owner ≠
      initial.network.ledger.countP (fun message => message.sender = owner))
    (available : ∀ past view response, response ∈ (players owner past view).support →
      response ∈ (bounds.menu runtime leaks).actions owner past view)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support)
    (clean : ∀ record ∈ (runtime.reactiveApplication leaks).executionTraffic final,
      record.input.envelope.sender = owner →
        runtime.permittedServiceEnvelope record.observation record.ledger
          record.input.envelope = true) :
    final.application.playerView owner = initial.application.playerView owner ∧
      final.network.ledger = initial.network.ledger ∧ final.receipts = initial.receipts ∧
      final.network.Satisfies safe ∧ initial.network.pending ⊆ final.network.pending ∧
      final.network.nextSerial owner = initial.network.nextSerial owner := by
  let app := runtime.reactiveApplication leaks
  induction visits generalizing initial with
  | nil =>
      cases FinDist.mem_support_pure.mp reached
      exact ⟨rfl, rfl, rfl, packets, List.Subset.refl _, rfl⟩
  | cons actor rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        FinDist.pure_bind] at reached
      obtain ⟨next, moved, tail⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      have nextClean : ∀ record ∈ app.executionTraffic next,
          record.input.envelope.sender = owner →
            runtime.permittedServiceEnvelope record.observation record.ledger
              record.input.envelope = true := by
        intro record present authored
        exact clean record ((runtime.executionTraffic_runInteractionPlan leaks players network
          (rest.map ServiceInstruction.player) next final tail).subset present) authored
      obtain ⟨view, ledger, receipts, valid, pending, counter, nextRecall, nextSerials⟩ :=
        runtime.activation_clean_data leaks bounds players initial next owner actor safe foreign
          packets recalled serials repeated available moved nextClean
      have nextRepeated : next.network.nextSerial owner ≠
          next.network.ledger.countP (fun message => message.sender = owner) := by
        rwa [counter, ledger]
      obtain ⟨lastView, lastLedger, lastReceipts, lastValid, lastPending, lastCounter⟩ :=
        ih next valid nextRecall nextSerials nextRepeated tail
      exact ⟨lastView.trans view, lastLedger.trans ledger, lastReceipts.trans receipts,
        lastValid, List.Subset.trans pending lastPending, lastCounter.trans counter⟩

/-- Repeated owner opportunities cannot replace the reserved envelope on a
branch without a genuine owner alarm. Selection remains exact despite all
foreign pending traffic and arbitrary known-envelope forwarding. -/
theorem repeated_window_clean_selection
    (bounds : MessageBounds graph)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (owner : Player)
    (initial : (runtime.reactiveApplication leaks).Execution) (event : graph.EventId)
    (message : Message Player (WitnessedPacket graph))
    (authored : message.sender = owner)
    (addressed : message.payload.call.event? graph = some event)
    (packets : initial.network.Satisfies fun packet => packet.sender = owner →
      packet.id ∈ initial.network.ledger.map Message.id ∨ packet = message)
    (pending : message ∈ initial.network.pending)
    (unpublished : message.id ∉ initial.network.ledger.map Message.id)
    (recalled : initial.InputRecall (runtime.reactiveApplication leaks))
    (serials : initial.network.SerialsBeforeNext)
    (repeated : initial.network.nextSerial owner ≠
      initial.network.ledger.countP (fun packet => packet.sender = owner))
    (available : ∀ past view response, response ∈ (players owner past view).support →
      response ∈ (bounds.menu runtime leaks).actions owner past view)
    (visits : List Player) (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support)
    (clean : ∀ record ∈ (runtime.reactiveApplication leaks).executionTraffic final,
      record.input.envelope.sender = owner →
        runtime.permittedServiceEnvelope record.observation record.ledger
          record.input.envelope = true) :
    runtime.reactiveLatest leaks event owner
        (final.observeEnvironment (runtime.reactiveApplication leaks)) = .include message.id ∧
      final.network.lookup message.id = some message := by
  obtain ⟨_, ledger, _, valid, retained, _⟩ := runtime.repeated_window_clean_data leaks bounds
    players network owner _ (fun packet different same => (different same).elim) visits initial
      final packets recalled serials repeated available reached clean
  apply runtime.foreign_window_selection leaks players network owner final event message
    authored addressed ?_ (retained pending) (by rwa [ledger]) [] (by simp) final
      (FinDist.mem_support_pure.mpr rfl)
  simpa only [ledger] using valid

end Vegas.EventGraphRuntime
