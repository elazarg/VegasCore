/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveReplaySettlement
import Vegas.Pending.ReactiveCompiledMenu
import Vegas.Pending.ReactiveUnusableBinding

/-! # A binding may await inclusion through repeated owner visits

After the first binding, the actual retained menu permits only silence and
known-envelope replay at this grant. All passive samples and replay copies are
retained. The protected selector therefore includes the same canonical packet
with the same typed result as immediate inclusion, even for unusable private
material. This is an execution law, not a claim that unusability is detectable.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- No participant can change the application during the retained tail of a
submitted binding; the owner has stopped and other players retain transport. -/
theorem compiled_binding_tail_transport (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (bounds : MessageBounds graph)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ bounds.compiledActions runtime leaks who past view)
    (initial : (runtime.reactiveApplication leaks).Execution)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (granted : initial.application.serviceGrant = some event)
    (owned : graph.actor? event = some owner)
    (ready : initial.application.config.cut.Ready event)
    (recorded : runtime.eventRecorded leaks (initial.recall owner) event = true)
    (current : (runtime.reactiveApplication leaks).Execution)
    (same : current.application = initial.application)
    (recalled : initial.recall owner ⊆ current.recall owner)
    (who : Player) (response : (runtime.reactiveApplication leaks).Action)
    (supported : response ∈ (players who (current.recall who)
      (current.observe (runtime.reactiveApplication leaks) who)).support) :
    response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩ := by
  let app := runtime.reactiveApplication leaks
  have currentGrant : (current.observe app who).application.publicView.serviceGrant =
      some event := by change current.application.serviceGrant = _; rw [same]; exact granted
  have transport : response ∈ (app.replayPolicy (current.recall who)
      (current.observe app who)).support := by
    by_cases acting : who = owner
    · subst who
      have prior := (runtime.eventRecorded_iff leaks (initial.recall owner) event).mp recorded
      obtain ⟨entry, member, submitted⟩ := prior
      have present := (runtime.eventRecorded_iff leaks (current.recall owner) event).mpr
        ⟨entry, recalled member, submitted⟩
      have publicReady : (current.observe app owner).application.publicView.EventReady event := by
        change current.application.publicView.EventReady event
        rw [same]
        exact (initial.application.publicView_eventReady event).mpr ready
      exact bounds.ordinary_binding_recorded runtime leaks owner _ _ event payload outputEq codeEq
        node currentGrant owned publicReady present response (lawful owner _ _ response supported)
    · exact bounds.compiled_foreign_transport runtime leaks who _ _ event currentGrant
        (fun equal => acting (Option.some.inj (owned.symm.trans equal)).symm)
          response (lawful who _ _ response supported)
  exact app.replayPolicy_cases _ _ response transport

/-- Delayed protected inclusion after an arbitrary retained response roster
has exactly the same application and public records as immediate inclusion. -/
theorem rawBinding_delayed_inclusion (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (bounds : MessageBounds graph)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ bounds.compiledActions runtime leaks who past view)
    (network : runtime.NetworkPolicy leaks)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (granted : execution.application.serviceGrant = some event)
    (owned : graph.actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (published : execution.network.Satisfies fun packet =>
      packet.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (serial : Nat) (opening : Option (Raw L)) (roster : List Player) :
    let response : (runtime.reactiveApplication leaks).Action :=
      ⟨some (.submit ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩)⟩
    let submitted := execution.respond (runtime.reactiveApplication leaks) owner response
    ((runtime.runInteractionPlan leaks players network
      (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) submitted).map
        fun final => (final.application, final.network.ledger,
          final.receipts, final.network.nextSerial)) =
      (runtime.interactionStep leaks players network (.includeLatest event owner) submitted).map
        fun final => (final.application, final.network.ledger,
          final.receipts, final.network.nextSerial) := by
  dsimp only
  let app := runtime.reactiveApplication leaks
  let response : app.Action :=
    ⟨some (.submit ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩)⟩
  let submitted := execution.respond app owner response
  let packet : WitnessedPacket graph := ⟨.commitment event (owner, .prepared serial), none⟩
  let message : Message Player (WitnessedPacket graph) :=
    ⟨(owner, execution.network.nextSerial owner), packet⟩
  have same := runtime.reactive_respond_application leaks execution owner response
  have currentGrant : submitted.application.serviceGrant = some event := by
    exact (congrArg PublicView.serviceGrant same.2).trans granted
  have currentReady : submitted.application.config.cut.Ready event := by rw [same.1]; exact ready
  have recorded : runtime.eventRecorded leaks (submitted.recall owner) event = true :=
    runtime.eventRecorded_respond leaks execution owner response event rfl
  have transport := fun current who action application recalled supported =>
    runtime.compiled_binding_tail_transport leaks bounds players lawful submitted owner event
      payload outputEq codeEq node currentGrant owned currentReady recorded current application
        recalled who action supported
  have networkEq : submitted.network = (execution.network.submit owner packet).2 := rfl
  have ledger : submitted.network.ledger = execution.network.ledger := rfl
  have packets : submitted.network.Satisfies fun candidate =>
      candidate.id ∈ submitted.network.ledger.map Message.id ∨ candidate = message := by
    rw [networkEq]
    apply (published.mono (fun candidate prior => Or.inl prior)).submit owner packet
    exact Or.inr rfl
  have pending : message ∈ submitted.network.pending := by
    rw [networkEq]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have unpublished : message.id ∉ submitted.network.ledger.map Message.id :=
    serials.next_unpublished owner
  have delayed := runtime.replay_window_settlement leaks players network owner submitted
    transport event message rfl rfl packets pending unpublished roster
  have immediate := runtime.replay_window_settlement leaks players network owner submitted
    transport event message rfl rfl packets pending unpublished []
  exact delayed.trans (by
    simpa only [List.map_nil, List.nil_append, runInteractionPlan, FinDist.bind_pure]
      using immediate.symm)

/-- Every delayed retained endpoint has actual immediate-inclusion provenance
and a clean public network, even when later owner visits replay the pending
packet. This is a support statement for arbitrary retained policies. -/
theorem rawBinding_delayed_support (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (bounds : MessageBounds graph)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ bounds.compiledActions runtime leaks who past view)
    (network : runtime.NetworkPolicy leaks)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (granted : execution.application.serviceGrant = some event)
    (owned : graph.actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (published : execution.network.Satisfies fun packet =>
      packet.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (serial : Nat) (opening : Option (Raw L)) (roster : List Player)
    (final : (runtime.reactiveApplication leaks).Execution) :
    let response : (runtime.reactiveApplication leaks).Action :=
      ⟨some (.submit ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩)⟩
    let submitted := execution.respond (runtime.reactiveApplication leaks) owner response
    final ∈ (runtime.runInteractionPlan leaks players network
      (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) submitted).support →
    ∃ immediate ∈ (runtime.interactionStep leaks players network
      (.includeLatest event owner) submitted).support,
      final.application = immediate.application ∧ final.network.ledger = immediate.network.ledger ∧
      final.receipts = immediate.receipts ∧
      final.network.nextSerial = immediate.network.nextSerial ∧
      final.network.Satisfies (fun packet => packet.id ∈ final.network.ledger.map Message.id) := by
  dsimp only
  intro reached
  let app := runtime.reactiveApplication leaks
  let response : app.Action :=
    ⟨some (.submit ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩)⟩
  let submitted := execution.respond app owner response
  let readout (next : app.Execution) :=
    (next.application, next.network.ledger, next.receipts, next.network.nextSerial)
  have mapped : readout final ∈ ((runtime.runInteractionPlan leaks players network
      (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) submitted).map
        readout).support := FinDist.support_map .. ▸ ⟨final, reached, rfl⟩
  rw [runtime.rawBinding_delayed_inclusion leaks bounds players lawful network execution owner
    event payload outputEq codeEq node granted owned ready published serials serial opening roster]
    at mapped
  obtain ⟨immediate, included, same⟩ := FinDist.support_map .. ▸ mapped
  refine ⟨immediate, included, (congrArg Prod.fst same).symm,
    (congrArg (fun value => value.2.1) same).symm,
    (congrArg (fun value => value.2.2.1) same).symm,
    (congrArg (fun value => value.2.2.2) same).symm, ?_⟩
  have application := runtime.reactive_respond_application leaks execution owner response
  have currentGrant : submitted.application.serviceGrant = some event :=
    (congrArg PublicView.serviceGrant application.2).trans granted
  have currentReady : submitted.application.config.cut.Ready event := by
    rw [application.1]
    exact ready
  have recorded : runtime.eventRecorded leaks (submitted.recall owner) event = true :=
    runtime.eventRecorded_respond leaks execution owner response event rfl
  exact runtime.submission_replay_settled_published leaks players network owner execution _ event
    rfl published serials
    (fun current who action same recalled supported => runtime.compiled_binding_tail_transport
      leaks bounds players lawful submitted owner event payload outputEq codeEq node currentGrant
        owned currentReady recorded current same recalled who action supported)
    roster final reached

end Vegas.EventGraphRuntime
