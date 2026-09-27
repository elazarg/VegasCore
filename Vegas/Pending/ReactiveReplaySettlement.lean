/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePlayerWindow
import Vegas.Pending.ReactiveServiceSelection
import Interaction.MessageNetworkInvariant

/-! # Protected inclusion after an actual replay window

Silence and known-envelope replay preserve the application and the original
pending packet. Their passive observations, pending multiplicity, own recall,
and traffic records remain in the execution. If the only unpublished envelope
is a fixed canonical packet, reserved inclusion still selects that packet.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

private theorem replay_response_data (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (safe : Message Player (WitnessedPacket graph) → Prop)
    (current : (runtime.reactiveApplication leaks).Execution)
    (packets : current.network.Satisfies safe) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action)
    (transport : response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩) :
    (current.respond (runtime.reactiveApplication leaks) who response).application =
        current.application ∧
      (current.respond (runtime.reactiveApplication leaks) who response).network.ledger =
        current.network.ledger ∧
      (current.respond (runtime.reactiveApplication leaks) who response).receipts =
        current.receipts ∧
      (current.respond (runtime.reactiveApplication leaks) who response).network.nextSerial =
        current.network.nextSerial ∧
      (current.respond (runtime.reactiveApplication leaks) who response).network.Satisfies safe ∧
      current.network.pending ⊆
        (current.respond (runtime.reactiveApplication leaks) who response).network.pending := by
  rcases transport with rfl | ⟨id, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, packets, fun _ member => member⟩
  · refine ⟨rfl, ?_, rfl, ?_, packets.replay who id, ?_⟩
    · change (current.network.replay who id).2.ledger = current.network.ledger
      unfold MessageNetwork.replay
      split <;> rfl
    · change (current.network.replay who id).2.nextSerial = current.network.nextSerial
      unfold MessageNetwork.replay
      split <;> rfl
    · change current.network.pending ⊆ (current.network.replay who id).2.pending
      unfold MessageNetwork.replay
      split
      · exact fun _ member => member
      · exact fun _ member => List.mem_append_left _ member

/-- The response premise is needed only while the actual application remains
fixed and the focal player's earlier responses are retained. It can therefore
be supplied by a stopped binding menu without restricting policies elsewhere. -/
theorem replay_window_preserves (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (owner : Player)
    (initial : (runtime.reactiveApplication leaks).Execution)
    (responses : ∀ (current : (runtime.reactiveApplication leaks).Execution) who response,
      current.application = initial.application →
      initial.recall owner ⊆ current.recall owner →
      response ∈ (players who (current.recall who)
        (current.observe (runtime.reactiveApplication leaks) who)).support →
      response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩)
    (safe : Message Player (WitnessedPacket graph) → Prop)
    (packets : initial.network.Satisfies safe)
    (roster : List Player) (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (roster.map ServiceInstruction.player) initial).support) :
    final.application = initial.application ∧ final.network.ledger = initial.network.ledger ∧
      final.receipts = initial.receipts ∧ final.network.nextSerial = initial.network.nextSerial ∧
      final.network.Satisfies safe ∧ initial.network.pending ⊆ final.network.pending := by
  let app := runtime.reactiveApplication leaks
  suffices ∀ (current : (runtime.reactiveApplication leaks).Execution),
      current.application = initial.application →
      current.network.ledger = initial.network.ledger → current.receipts = initial.receipts →
      current.network.nextSerial = initial.network.nextSerial →
      initial.recall owner ⊆ current.recall owner → current.network.Satisfies safe →
      initial.network.pending ⊆ current.network.pending →
      final ∈ (runtime.runInteractionPlan leaks players network
        (roster.map ServiceInstruction.player) current).support →
      final.application = initial.application ∧ final.network.ledger = initial.network.ledger ∧
        final.receipts = initial.receipts ∧ final.network.nextSerial = initial.network.nextSerial ∧
        final.network.Satisfies safe ∧ initial.network.pending ⊆ final.network.pending from
    this initial rfl rfl rfl rfl (List.Subset.refl _) packets (List.Subset.refl _) reached
  clear reached
  induction roster with
  | nil =>
      intro current application ledger receipts counters recalled valid present supported
      cases FinDist.mem_support_pure.mp supported
      exact ⟨application, ledger, receipts, counters, valid, present⟩
  | cons who rest ih =>
      intro current application ledger receipts counters recalled valid present supported
      obtain ⟨middle, first, supported⟩ := Set.mem_iUnion₂.mp
        (FinDist.support_bind .. ▸ supported)
      simp only [interactionStep, interactionInstruction, FinDist.pure_bind] at first
      change middle ∈ ((current.environmentStep app (.activate who)).bind
        (app.invoke players who)).support at first
      rw [ReactiveApplication.Execution.activation_samples, FinDist.bind_map] at first
      obtain ⟨sample, _, first⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ first)
      obtain ⟨response, chosen, rfl⟩ := FinDist.support_map .. ▸ first
      let activated := current.sampledActivation app who sample
      have data := replay_response_data runtime leaks safe activated (valid.learn who sample) who
        response (responses activated who response application recalled chosen)
      exact ih (activated.respond app who response) (data.1.trans application)
        (data.2.1.trans ledger) (data.2.2.1.trans receipts) (data.2.2.2.1.trans counters)
        (List.Subset.trans recalled (app.respond_recall_mono activated who owner response))
        data.2.2.2.2.1 (List.Subset.trans present data.2.2.2.2.2) supported

/-- Published traffic and copies of one unspent canonical envelope cannot
redirect reserved inclusion to a different identifier. -/
theorem reactiveLatest_unique_unpublished (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (current : (runtime.reactiveApplication leaks).Execution)
    (owner : Player) (event : graph.EventId)
    (message : Message Player (WitnessedPacket graph))
    (authored : message.sender = owner)
    (addressed : message.payload.call.event? graph = some event)
    (pending : message ∈ current.network.pending)
    (unpublished : message.id ∉ current.network.ledger.map Message.id)
    (packets : ∀ packet ∈ current.network.pending,
      packet.id ∈ current.network.ledger.map Message.id ∨ packet = message) :
    runtime.reactiveLatest leaks event owner
      (current.observeEnvironment (runtime.reactiveApplication leaks)) = .include message.id := by
  unfold reactiveLatest
  split
  · rename_i absent
    have excluded := List.find?_eq_none.mp absent message (List.mem_reverse.mpr pending)
    have unspent : (current.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
        (runtime.reactiveApplication leaks) message.id := unpublished
    simp only [authored, addressed, unspent, and_self, decide_true] at excluded
    contradiction
  · rename_i selected found
    have member := List.mem_reverse.mp (List.mem_of_find?_eq_some found)
    have good : selected.sender = owner ∧ selected.payload.call.event? graph = some event ∧
        (current.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
          (runtime.reactiveApplication leaks) selected.id := by
      simpa only [decide_eq_true_eq] using List.find?_some found
    rcases packets selected member with published | same
    · exact False.elim (good.2.2 published)
    · exact congrArg ReactiveApplication.Command.include (congrArg Message.id same)

/-- The selector and its lookup after the replay window recover the original
packet, while retaining every sampled and replayed execution branch. -/
theorem replay_window_selection (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (owner : Player)
    (initial : (runtime.reactiveApplication leaks).Execution)
    (responses : ∀ (current : (runtime.reactiveApplication leaks).Execution) who response,
      current.application = initial.application →
      initial.recall owner ⊆ current.recall owner →
      response ∈ (players who (current.recall who)
        (current.observe (runtime.reactiveApplication leaks) who)).support →
      response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩)
    (event : graph.EventId) (message : Message Player (WitnessedPacket graph))
    (authored : message.sender = owner)
    (addressed : message.payload.call.event? graph = some event)
    (packets : initial.network.Satisfies fun packet =>
      packet.id ∈ initial.network.ledger.map Message.id ∨ packet = message)
    (pending : message ∈ initial.network.pending)
    (unpublished : message.id ∉ initial.network.ledger.map Message.id)
    (roster : List Player) (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (roster.map ServiceInstruction.player) initial).support) :
    runtime.reactiveLatest leaks event owner
        (final.observeEnvironment (runtime.reactiveApplication leaks)) = .include message.id ∧
      final.network.lookup message.id = some message := by
  obtain ⟨_, ledger, _, _, valid, retained⟩ := runtime.replay_window_preserves leaks players network
    owner initial responses _ packets roster final reached
  have present := retained pending
  have unspent : message.id ∉ final.network.ledger.map Message.id := by rwa [ledger]
  have safe : ∀ packet ∈ final.network.pending,
      packet.id ∈ final.network.ledger.map Message.id ∨ packet = message := by
    intro packet member
    simpa only [ledger] using valid.pending packet member
  refine ⟨runtime.reactiveLatest_unique_unpublished leaks final owner event message authored
    addressed present unspent safe, ?_⟩
  have unique (packet : Message Player (WitnessedPacket graph))
      (member : packet ∈ final.network.pending) (same : packet.id = message.id) :
      packet = message :=
    (safe packet member).resolve_left (by simpa only [same] using unspent)
  cases found : final.network.lookup message.id with
  | none =>
      have excluded := List.find?_eq_none.mp found message present
      exact False.elim (excluded (decide_eq_true_iff.mpr rfl))
  | some selected =>
      have same : selected.id = message.id := by
        simpa only [decide_eq_true_eq] using List.find?_some found
      exact congrArg some (unique selected (List.mem_of_find?_eq_some found) same)

/-- Delaying protected inclusion through such a window preserves its exact
application, ledger, receipt and allocation-counter law. The packet need not
be accepted: the receipt reports its actual handler result. -/
theorem replay_window_settlement (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (owner : Player)
    (initial : (runtime.reactiveApplication leaks).Execution)
    (responses : ∀ (current : (runtime.reactiveApplication leaks).Execution) who response,
      current.application = initial.application →
      initial.recall owner ⊆ current.recall owner →
      response ∈ (players who (current.recall who)
        (current.observe (runtime.reactiveApplication leaks) who)).support →
      response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩)
    (event : graph.EventId) (message : Message Player (WitnessedPacket graph))
    (authored : message.sender = owner)
    (addressed : message.payload.call.event? graph = some event)
    (packets : initial.network.Satisfies fun packet =>
      packet.id ∈ initial.network.ledger.map Message.id ∨ packet = message)
    (pending : message ∈ initial.network.pending)
    (unpublished : message.id ∉ initial.network.ledger.map Message.id)
    (roster : List Player) :
    ((runtime.runInteractionPlan leaks players network
      (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) initial).map
        fun final => (final.application, final.network.ledger,
          final.receipts, final.network.nextSerial)) =
      FinDist.pure
        (((runtime.reactiveApplication leaks).handle initial.application message).getD
            initial.application,
          @List.append (Message Player (WitnessedPacket graph)) initial.network.ledger [message],
          initial.receipts ++ [(message.id,
            ((runtime.reactiveApplication leaks).handle initial.application message).isSome)],
          initial.network.nextSerial) := by
  let app := runtime.reactiveApplication leaks
  apply FinDist.eq_pure_of_support_subset_singleton
  intro result mapped
  obtain ⟨final, runSupport, rfl⟩ := FinDist.support_map .. ▸ mapped
  rw [runtime.runInteractionPlan_append] at runSupport
  obtain ⟨current, prior, included⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ runSupport)
  obtain ⟨application, ledger, receipts, counters, _, _⟩ :=
    runtime.replay_window_preserves leaks players network owner initial responses _ packets
      roster current prior
  obtain ⟨selected, found⟩ := runtime.replay_window_selection leaks players network owner initial
    responses event message authored addressed packets pending unpublished roster current prior
  simp only [runInteractionPlan, FinDist.bind_pure, interactionStep, interactionInstruction,
    selected, FinDist.pure_bind] at included
  change final ∈ ((current.environmentStep app (.include message.id)).bind FinDist.pure).support
    at included
  rw [FinDist.bind_pure] at included
  simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at included
  cases FinDist.mem_support_pure.mp included
  change (_, _, _, _) = _
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    found, application, ledger, receipts, counters]
  rfl

end Vegas.EventGraphRuntime
