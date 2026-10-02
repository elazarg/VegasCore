/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePlayerWindow
import Vegas.Pending.ReactiveServiceSelection
import Interaction.MessageNetworkInvariant

/-! # Protected inclusion after a silent response window

Silent responses preserve the application and the original pending packet.
Their passive observations, own recall, and traffic records remain in the
execution. If the only unpublished envelope
is a fixed canonical packet, reserved inclusion still selects that packet.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Silent responses retain the application and public
allocation state; every existing pending envelope remains available. -/
theorem silent_response_preserves (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (safe : Message Player (WitnessedPacket graph) → Prop)
    (current : (runtime.reactiveApplication leaks).Execution)
    (packets : current.network.Satisfies safe) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action)
    (transport : response = ⟨none⟩) :
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
  subst response
  exact ⟨rfl, rfl, rfl, rfl, packets, fun _ member => member⟩

/-- The response premise is needed only while the actual application remains
fixed and the focal player's earlier responses are retained. It can therefore
be supplied by a stopped binding menu without restricting policies elsewhere. -/
theorem silent_window_preserves (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (owner : Player)
    (initial : (runtime.reactiveApplication leaks).Execution)
    (responses : ∀ (current : (runtime.reactiveApplication leaks).Execution) who response,
      current.application = initial.application →
      initial.recall owner ⊆ current.recall owner →
      response ∈ (players who (current.recall who)
        (current.observe (runtime.reactiveApplication leaks) who)).support →
      response = ⟨none⟩)
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
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact ⟨application, ledger, receipts, counters, valid, present⟩
  | cons who rest ih =>
      intro current application ledger receipts counters recalled valid present supported
      obtain ⟨middle, first, supported⟩ := Set.mem_iUnion₂.mp
        (PMF.support_bind .. ▸ supported)
      simp only [interactionStep, interactionInstruction, PMF.pure_bind] at first
      change middle ∈ ((current.environmentStep app (.activate who)).bind
        (app.invoke players who)).support at first
      rw [ReactiveApplication.Execution.activation_samples, PMF.bind_map] at first
      obtain ⟨sample, _, first⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ first)
      obtain ⟨response, chosen, rfl⟩ := PMF.support_map .. ▸ first
      let activated := current.sampledActivation app who sample
      have data := silent_response_preserves runtime leaks safe activated (valid.learn who sample)
        who response (responses activated who response application recalled chosen)
      exact ih (activated.respond app who response) (data.1.trans application)
        (data.2.1.trans ledger) (data.2.2.1.trans receipts) (data.2.2.2.1.trans counters)
        (List.Subset.trans recalled (app.respond_recall_mono activated who owner response))
        data.2.2.2.2.1 (List.Subset.trans present data.2.2.2.2.2) supported

/-- Published traffic and one unspent canonical envelope cannot
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

/-- The selector and its lookup after the silent response window recover the
original packet, while retaining every sampled execution branch. -/
theorem silent_window_selection (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (owner : Player)
    (initial : (runtime.reactiveApplication leaks).Execution)
    (responses : ∀ (current : (runtime.reactiveApplication leaks).Execution) who response,
      current.application = initial.application →
      initial.recall owner ⊆ current.recall owner →
      response ∈ (players who (current.recall who)
        (current.observe (runtime.reactiveApplication leaks) who)).support →
      response = ⟨none⟩)
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
  obtain ⟨_, ledger, _, _, valid, retained⟩ := runtime.silent_window_preserves leaks players network
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
theorem silent_window_settlement (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (owner : Player)
    (initial : (runtime.reactiveApplication leaks).Execution)
    (responses : ∀ (current : (runtime.reactiveApplication leaks).Execution) who response,
      current.application = initial.application →
      initial.recall owner ⊆ current.recall owner →
      response ∈ (players who (current.recall who)
        (current.observe (runtime.reactiveApplication leaks) who)).support →
      response = ⟨none⟩)
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
      PMF.pure
        (((runtime.reactiveApplication leaks).handle initial.application message).getD
            initial.application,
          @List.append (Message Player (WitnessedPacket graph)) initial.network.ledger [message],
          initial.receipts ++ [(message.id,
            ((runtime.reactiveApplication leaks).handle initial.application message).isSome)],
          initial.network.nextSerial) := by
  let app := runtime.reactiveApplication leaks
  apply pmf_eq_pure_of_support_subset_singleton
  intro result mapped
  obtain ⟨final, runSupport, rfl⟩ := PMF.support_map .. ▸ mapped
  rw [runtime.runInteractionPlan_append] at runSupport
  obtain ⟨current, prior, included⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ runSupport)
  obtain ⟨application, ledger, receipts, counters, _, _⟩ :=
    runtime.silent_window_preserves leaks players network owner initial responses _ packets
      roster current prior
  obtain ⟨selected, found⟩ := runtime.silent_window_selection leaks players network owner initial
    responses event message authored addressed packets pending unpublished roster current prior
  simp only [runInteractionPlan, PMF.bind_pure, interactionStep, interactionInstruction,
    selected, PMF.pure_bind] at included
  change final ∈ ((current.environmentStep app (.include message.id)).bind PMF.pure).support
    at included
  rw [PMF.bind_pure] at included
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at included
  cases (PMF.mem_support_pure_iff _ _).mp included
  change (_, _, _, _) = _
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    found, application, ledger, receipts, counters]
  rfl

/-- Protected inclusion publishes the pending envelope, including in knowledge
learned during the delay. No pending envelope or private knowledge
is erased to establish the next service boundary. -/
theorem silent_window_settled_published (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (owner : Player)
    (initial : (runtime.reactiveApplication leaks).Execution)
    (responses : ∀ (current : (runtime.reactiveApplication leaks).Execution) who response,
      current.application = initial.application →
      initial.recall owner ⊆ current.recall owner →
      response ∈ (players who (current.recall who)
        (current.observe (runtime.reactiveApplication leaks) who)).support →
      response = ⟨none⟩)
    (event : graph.EventId) (message : Message Player (WitnessedPacket graph))
    (authored : message.sender = owner)
    (addressed : message.payload.call.event? graph = some event)
    (packets : initial.network.Satisfies fun packet =>
      packet.id ∈ initial.network.ledger.map Message.id ∨ packet = message)
    (pending : message ∈ initial.network.pending)
    (unpublished : message.id ∉ initial.network.ledger.map Message.id)
    (roster : List Player) (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) initial).support) :
    final.network.Satisfies fun packet => packet.id ∈ final.network.ledger.map Message.id := by
  let app := runtime.reactiveApplication leaks
  rw [runtime.runInteractionPlan_append] at reached
  obtain ⟨current, prior, included⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨_, ledger, _, _, valid, _⟩ := runtime.silent_window_preserves leaks players network
    owner initial responses _ packets roster current prior
  obtain ⟨selected, found⟩ := runtime.silent_window_selection leaks players network owner initial
    responses event message authored addressed packets pending unpublished roster current prior
  simp only [runInteractionPlan, PMF.bind_pure, interactionStep, interactionInstruction,
    selected, PMF.pure_bind] at included
  change final ∈ ((current.environmentStep app (.include message.id)).bind PMF.pure).support
    at included
  rw [PMF.bind_pure] at included
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at included
  cases (PMF.mem_support_pure_iff _ _).mp included
  change (current.includePending app message.id).network.Satisfies _
  rw [app.includePending_network]
  apply (valid.includePending message.id).mono
  intro packet safe
  change packet.id ∈ (current.network.includePending message.id).2.ledger.map Message.id
  simp only [MessageNetwork.includePending, found, List.map_append, List.map_cons, List.map_nil]
  rcases safe with earlier | rfl
  · exact List.mem_append_left _ (ledger ▸ earlier)
  · exact List.mem_append_right _ (List.mem_singleton_self _)

/-- A fresh addressed submission followed by silent responses
and protected inclusion restores the all-published network boundary. This does
not assume the submitted call is valid or accepted. -/
theorem submission_silent_settled_published (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (owner : Player)
    (initial : (runtime.reactiveApplication leaks).Execution)
    (submission : WitnessedSubmission graph) (event : graph.EventId)
    (addressed : submission.call.packet.event? graph = some event)
    (published : initial.network.Satisfies fun packet =>
      packet.id ∈ initial.network.ledger.map Message.id)
    (serials : initial.network.SerialsBeforeNext)
    (responses : ∀ (current : (runtime.reactiveApplication leaks).Execution) who response,
      current.application = (initial.respond (runtime.reactiveApplication leaks) owner
        ⟨some submission⟩).application →
      (initial.respond (runtime.reactiveApplication leaks) owner
        ⟨some submission⟩).recall owner ⊆ current.recall owner →
      response ∈ (players who (current.recall who)
        (current.observe (runtime.reactiveApplication leaks) who)).support →
      response = ⟨none⟩)
    (roster : List Player) (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (roster.map ServiceInstruction.player ++ [.includeLatest event owner])
        (initial.respond (runtime.reactiveApplication leaks) owner
          ⟨some submission⟩)).support) :
    final.network.Satisfies fun packet => packet.id ∈ final.network.ledger.map Message.id := by
  let app := runtime.reactiveApplication leaks
  let packet := app.packet (app.submit initial.application owner submission) owner
    (initial.network.known owner) submission
  let message : Message Player (WitnessedPacket graph) :=
    ⟨(owner, initial.network.nextSerial owner), packet⟩
  let submitted := initial.respond app owner ⟨some submission⟩
  have packets : submitted.network.Satisfies fun candidate =>
      candidate.id ∈ submitted.network.ledger.map Message.id ∨ candidate = message := by
    change (initial.network.submit owner packet).2.Satisfies _
    exact (published.mono (fun _ prior => Or.inl prior)).submit owner packet (Or.inr rfl)
  have pending : message ∈ submitted.network.pending :=
    List.mem_append_right _ (List.mem_singleton_self _)
  exact runtime.silent_window_settled_published leaks players network owner submitted responses
    event message rfl addressed packets pending (serials.next_unpublished owner)
      roster final reached

end Vegas.EventGraphRuntime
