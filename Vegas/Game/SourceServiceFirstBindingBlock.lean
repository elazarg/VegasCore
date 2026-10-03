/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRepeatedBlock

/-! # First opaque binding followed by the complete arbitrary roster

The actual canonical packet may carry any private material. Its one local
repair supplies the pending-candidate invariant for the whole remaining owner
and foreign roster and protected settlement. Subsequent original responses are
arbitrary effective choices, with authentic first-departure evidence retained.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem first_binding_block_coupling
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (players : Player → (application setup leaks).Policy)
    (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L))
    (memory : BindingMemory (runtime setup) leaks)
    (original repaired : (application setup leaks).Execution)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (completedMemory : memory.shadow.CompletedAt original.application.config)
    (reference : List (application setup leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (application setup leaks))
    (rightRecall : repaired.InputRecall (application setup leaks))
    (serials : original.network.SerialsBeforeNext)
    (counted : original.network.nextSerial owner =
      Message.distinctAuthoredCount original.network.ledger owner)
    (fresh : original.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (ready : original.application.config.cut.Ready event)
    (timely : original.application.WithinDeadline (runtime setup) event)
    (vacant : original.application.accepted (.inr event) = none)
    (unused : original.application.HandleUnused (owner, .prepared serial))
    (published : original.network.Satisfies fun packet => packet.sender = owner →
      packet.id ∈ original.network.ledger.map Message.id)
    (available : ∀ past view response, response ∈ (players owner past view).support →
      response ∈ (bounds.menu (runtime setup) leaks).actions owner past view)
    (before after : List (ServiceInstruction (graph setup))) (visits : List Player)
    (ticks : Nat)
    (split : rosterPlan setup rosters = before ++ visits.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]) ++ after)
    (position : original.environmentRecall.length = before.length) :
    let app := application setup leaks
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    let view := repaired.observe app owner
    let response : app.Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
    let changed := memory.repairResponse (runtime setup) leaks owner view response
    let remembered : BindingMemory (runtime setup) leaks :=
      ⟨changed.2, memory.responses ++
        [(memory.shadow.inputView (runtime setup) leaks view, response)]⟩
    let plan := visits.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network plan
        (original.respond app owner response) ∧
      coupling.map Prod.snd = strategy.runJoint owner players
        (rosterScheduler setup leaks rosters network) plan.length
          (repaired.respond app owner changed.1) remembered ∧
      ∀ next ∈ coupling.support,
        (∃ record ∈ app.executionTraffic next.1, record.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.envelope = false) ∨
        (BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 ∧
          next.2.2.shadow.CompletedAt next.1.application.config) := by
  intro app strategy view response changed remembered plan
  let left := original.respond app owner response
  let right := repaired.respond app owner changed.1
  let packet : WitnessedPacket (graph setup) :=
    ⟨.commitment event (owner, .prepared serial), none, some ⟨event⟩⟩
  let message : Message Player (WitnessedPacket (graph setup)) :=
    ⟨(owner, original.network.nextSerial owner), packet⟩
  have paired := frame.binding_submission event payload outputEq codeEq node serial opening
    fresh ready
  have data := frame.binding_submission_pending event payload outputEq codeEq node serial opening
    fresh (fun _ _ => completedMemory.ready_none event ready)
  have unchanged := (runtime setup).reactive_respond_application leaks original owner response
  have leftReady : left.application.config.cut.Ready event := by
    rw [unchanged.1]
    exact ready
  have leftTimely : left.application.WithinDeadline (runtime setup) event := by
    unfold State.WithinDeadline
    rw [show left.application.clock = original.application.clock from
      congrArg PublicView.clock unchanged.2,
      show left.application.activatedAt = original.application.activatedAt from
        congrArg PublicView.activatedAt unchanged.2]
    exact timely
  have accepted : left.application.accepted = original.application.accepted :=
    congrArg PublicView.accepted unchanged.2
  have leftVacant : left.application.accepted (.inr event) = none := by
    rw [accepted]
    exact vacant
  have leftUnused : left.application.HandleUnused (owner, .prepared serial) := by
    intro field same
    rw [accepted] at same
    exact unused field same
  have networkEq : left.network = (original.network.submit owner packet).2 := by
    simp only [left, app, response, ReactiveApplication.Execution.respond,
      reactiveApplication_packet_none, packet,
      original.application.publicView_tokenFor_of_ready
        (.commitment event (owner, .prepared serial)) event rfl ready]
  have packets : left.network.Satisfies fun candidate => candidate.sender = owner →
      candidate.id ∈ left.network.ledger.map Message.id ∨ candidate = message := by
    rw [networkEq]
    apply (published.mono (fun candidate prior same => Or.inl (prior same))).submit owner packet
    exact fun _ => Or.inr rfl
  have pending : message ∈ left.network.pending := by
    rw [networkEq]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have repeated : left.network.nextSerial owner ≠
      Message.distinctAuthoredCount left.network.ledger owner := by
    change (Function.update original.network.nextSerial owner
      (original.network.nextSerial owner + 1)) owner ≠ _
    rw [Function.update_self]
    change original.network.nextSerial owner + 1 ≠
      Message.distinctAuthoredCount original.network.ledger owner
    omega
  have recorded : (runtime setup).eventRecorded leaks (right.recall owner) event = true := by
    rw [← (runtime setup).eventRecorded_congr leaks _ _ paired.submissions event]
    exact (runtime setup).eventRecorded_respond leaks original owner response event rfl
  have nextStarted : reference.length ≤ (right.recall owner).length := by
    rw [app.respond_recall_length]
    omega
  have ownFresh : (memory.shadow.inputView (runtime setup) leaks view).application.candidates
      (.prepared serial) = .fresh := by
    rw [frame.observed]
    exact fresh
  have localFresh : view.application.candidates (.prepared serial) = .fresh :=
    (frame.slots (.prepared serial)).mp fresh
  have otherCompleted : ∀ other, other ≠ event →
      (remembered.shadow.actions other).isSome ∨
        (remembered.shadow.values (.inr other)).isSome →
          other ∈ left.application.config.cut.completed := by
    intro other different present
    rw [unchanged.1]
    apply completedMemory other
    cases decoded : opening.bind (fun raw => raw.as? payload) with
    | none =>
        simpa only [remembered, changed, BindingMemory.repairResponse, response, node,
          ownFresh, localFresh, and_self, ↓reduceIte, decoded, BindingShadow.rememberCompletion,
          BindingShadow.rememberCandidate, Function.update_of_ne different,
          Function.update_of_ne (Sum.inr_injective.ne different)] using present
    | some value =>
        simpa only [remembered, changed, BindingMemory.repairResponse, response, node,
          ownFresh, localFresh, and_self, ↓reduceIte, decoded, BindingShadow.rememberCandidate]
          using present
  exact repeated_binding_block_coupling setup leaks bounds rosters network players owner event
    payload outputEq codeEq node (.prepared serial) (original.network.nextSerial owner) remembered
      left right paired otherCompleted reference nextStarted
      (app.respond_inputRecall original owner response leftRecall)
      (app.respond_inputRecall repaired owner changed.1 rightRecall)
      (networkEq ▸ serials.submit owner packet) repeated recorded leftReady leftTimely leftVacant
      leftUnused data.1 data.2.1 data.2.2 pending
      (serials.next_unpublished owner) packets available before after visits ticks split
      (by rw [app.respond_environmentRecall]; exact position)

end Vegas
