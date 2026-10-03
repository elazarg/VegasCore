/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDecisionWindow
import Vegas.Pending.ReactiveServiceRecall
import Interaction.ReactiveAllocation
import Interaction.DeferredObservation

/-! # Physical records of independently timed Boolean decisions

Both source choices create one actual addressed packet at the selected owner
visit. This proof invariant retains its serial, pending sampling and recall
through the whole public roster before reserved inclusion.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def decisionPassed {slots : Nat} (selected : Fin slots × Bool) (visits : Nat) : Bool :=
  decide (selected.1.val < visits)

theorem decisionPassed_zero {slots : Nat} (selected : Fin slots × Bool) :
    decisionPassed selected 0 = false := by simp [decisionPassed]

def decisionEnvelope (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (disclose : Bool) (initial : (runtime.reactiveApplication leaks).Execution) :
    Message Player (WitnessedPacket graph) :=
  ⟨(owner, initial.network.nextSerial owner),
    ⟨(windowDecisionMaterial event opening disclose).call.packet,
      (if disclose then opening else none).map (fun pair => ⟨pair.1, pair.2⟩),
      initial.application.publicView.tokenFor
        (windowDecisionMaterial event opening disclose).call.packet⟩⟩

theorem decisionEnvelope_addressed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (disclose : Bool) (initial : (runtime.reactiveApplication leaks).Execution) :
    (runtime.decisionEnvelope leaks owner event opening disclose initial).payload.call.event?
      graph = some event := by
  cases disclose
  · rfl
  · cases opening <;> rfl

structure DecisionWindowFrame (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (selected : Fin slots × Bool) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution) : Prop where
  application : current.application = initial.application
  ledger : current.network.ledger = initial.network.ledger
  receipts : current.receipts = initial.receipts
  count : (current.recall owner).length = offset + visits
  counters : current.network.nextSerial = fun who => initial.network.nextSerial who +
    if who = owner ∧ decisionPassed selected visits then 1 else 0
  serials : current.network.SerialsBeforeNext
  packets : current.network.Satisfies fun message =>
    message.id ∈ initial.network.ledger.map Message.id ∨
      message = runtime.decisionEnvelope leaks owner event opening selected.2 initial
  sent : decisionPassed selected visits = true →
    runtime.decisionEnvelope leaks owner event opening selected.2 initial ∈
      current.network.pending

theorem DecisionWindowFrame.initial (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    {slots : Nat} (selected : Fin slots × Bool)
    (initial : (runtime.reactiveApplication leaks).Execution)
    (serials : initial.network.SerialsBeforeNext)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id) :
    runtime.DecisionWindowFrame leaks owner event opening (initial.recall owner).length
      selected 0 initial initial where
  application := rfl
  ledger := rfl
  receipts := rfl
  count := by simp
  counters := by simp only [decisionPassed_zero, Bool.false_eq_true, and_false, ↓reduceIte,
    Nat.add_zero]
  serials := serials
  packets := published.mono fun _ member => Or.inl member
  sent := by simp only [decisionPassed_zero, Bool.false_eq_true, false_implies]

theorem DecisionWindowFrame.activate (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (selected : Fin slots × Bool) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.DecisionWindowFrame leaks owner event opening offset selected visits
      initial current) (who : Player) (sample : Finset (MessageId Player)) :
    runtime.DecisionWindowFrame leaks owner event opening offset selected visits initial
      (current.sampledActivation (runtime.reactiveApplication leaks) who sample) where
  application := frame.application
  ledger := frame.ledger
  receipts := frame.receipts
  count := frame.count
  counters := frame.counters
  serials := frame.serials.learn who sample
  packets := frame.packets.learn who sample
  sent := frame.sent

theorem DecisionWindowFrame.waiting_response (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (selected : Fin slots × Bool) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.DecisionWindowFrame leaks owner event opening offset selected visits
      initial current) (who : Player) (action : (runtime.reactiveApplication leaks).Action)
    (waiting : action = ⟨none⟩)
    (passed : decisionPassed selected (visits + if who = owner then 1 else 0) =
      decisionPassed selected visits) :
    runtime.DecisionWindowFrame leaks owner event opening offset selected
      (visits + if who = owner then 1 else 0) initial
      (current.respond (runtime.reactiveApplication leaks) who action) := by
  let app := runtime.reactiveApplication leaks
  have data :
      (current.respond app who action).application = current.application ∧
      (current.respond app who action).network.ledger = current.network.ledger ∧
      (current.respond app who action).receipts = current.receipts ∧
      (current.respond app who action).network.nextSerial = current.network.nextSerial ∧
      (current.respond app who action).network.SerialsBeforeNext ∧
      (current.respond app who action).network.Satisfies (fun message =>
        message.id ∈ initial.network.ledger.map Message.id ∨
          message = runtime.decisionEnvelope leaks owner event opening selected.2 initial) ∧
      current.network.pending ⊆ (current.respond app who action).network.pending := by
    rcases waiting with rfl
    exact ⟨rfl, rfl, rfl, rfl, frame.serials, frame.packets, fun _ member => member⟩
  refine ⟨data.1.trans frame.application, data.2.1.trans frame.ledger,
    data.2.2.1.trans frame.receipts, ?_, ?_, data.2.2.2.2.1, data.2.2.2.2.2.1, ?_⟩
  · rw [app.respond_recall_length, frame.count]
    omega
  · rw [passed, data.2.2.2.1]
    exact frame.counters
  · intro sent
    rw [passed] at sent
    exact data.2.2.2.2.2.2 (frame.sent sent)

theorem DecisionWindowFrame.decision_response (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (selected : Fin slots × Bool)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.DecisionWindowFrame leaks owner event opening offset selected
      selected.1.val initial current)
    (owned : ∀ candidate raw, opening = some (candidate, raw) → candidate.1 = owner)
    (valid : selected.2 = true → ∀ candidate raw, opening = some (candidate, raw) →
      initial.application.candidates.lookup candidate = .openable raw) :
    runtime.DecisionWindowFrame leaks owner event opening offset selected
      (selected.1.val + 1) initial
      (current.respond (runtime.reactiveApplication leaks) owner
        (runtime.windowDecision leaks event opening selected.2)) := by
  let app := runtime.reactiveApplication leaks
  let packet :=
    (runtime.decisionEnvelope leaks owner event opening selected.2 initial).payload
  have before : decisionPassed selected selected.1.val = false := by simp [decisionPassed]
  have after : decisionPassed selected (selected.1.val + 1) = true := by simp [decisionPassed]
  have serial : current.network.nextSerial owner = initial.network.nextSerial owner := by
    simpa only [before, Bool.false_eq_true, and_false, ↓reduceIte, Nat.add_zero] using
      congrFun frame.counters owner
  have prior : current.network.nextSerial = initial.network.nextSerial := by
    simpa only [before, Bool.false_eq_true, and_false, ↓reduceIte, Nat.add_zero] using
      frame.counters
  have application := runtime.windowDecision_application leaks current owner event
    opening selected.2
  have same : app.submit current.application owner
      (windowDecisionMaterial event opening selected.2) = current.application := application
  have materialized := runtime.windowDecision_packet leaks owner event opening
    current.application (current.network.known owner) selected.2 owned
      (fun chosen candidate raw material => frame.application ▸ valid chosen candidate raw material)
  have network : (current.respond app owner
      (runtime.windowDecision leaks event opening selected.2)).network =
      (current.network.submit owner packet).2 := by
    change (current.network.submit owner
      (app.packet (app.submit current.application owner
        (windowDecisionMaterial event opening selected.2)) owner (current.network.known owner)
          (windowDecisionMaterial event opening selected.2))).2 = _
    rw [same, materialized, frame.application]
    rfl
  refine ⟨application.trans frame.application, ?_, frame.receipts, ?_, ?_, ?_, ?_, ?_⟩
  · rw [network]
    exact frame.ledger
  · rw [app.respond_recall_length, frame.count]
    simp only [↓reduceIte]
    omega
  · rw [network, after]
    simp only [MessageNetwork.submit, and_true, prior]
    funext who
    split <;> simp_all
  · rw [network]
    exact frame.serials.submit owner packet
  · rw [network]
    apply frame.packets.submit owner packet
    exact Or.inr (by simp only [decisionEnvelope, serial]; rfl)
  · intro _
    rw [network]
    simp only [MessageNetwork.submit, List.mem_append, List.mem_singleton]
    exact Or.inr (by simp only [decisionEnvelope, serial]; rfl)

theorem DecisionWindowFrame.response (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (selected : Fin slots × Bool) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.DecisionWindowFrame leaks owner event opening offset selected visits
      initial current) (who : Player) (action : (runtime.reactiveApplication leaks).Action)
    (supported : action ∈ (runtime.decisionWindowPlayers leaks owner event opening offset
      selected who (current.recall who)
        (current.observe (runtime.reactiveApplication leaks) who)).support)
    (owned : ∀ candidate raw, opening = some (candidate, raw) → candidate.1 = owner)
    (valid : selected.2 = true → ∀ candidate raw, opening = some (candidate, raw) →
      initial.application.candidates.lookup candidate = .openable raw) :
    runtime.DecisionWindowFrame leaks owner event opening offset selected
      (visits + if who = owner then 1 else 0) initial
      (current.respond (runtime.reactiveApplication leaks) who action) := by
  let app := runtime.reactiveApplication leaks
  by_cases active : who = owner
  · subst who
    simp only [decisionWindowPlayers, ↓reduceIte, ReactiveApplication.scheduledPolicy,
      frame.count] at supported
    split at supported
    · rename_i chosen
      have atSlot : visits = selected.1.val := by simpa using chosen.symm
      subst visits
      cases (PMF.mem_support_pure_iff _ _).mp supported
      simpa only [↓reduceIte] using
        frame.decision_response runtime leaks owner event opening offset selected
          initial current owned valid
    · rename_i waiting
      apply frame.waiting_response runtime leaks owner event opening offset selected
        visits initial current owner action (app.silentPolicy_cases _ _ action supported)
      simp only [↓reduceIte]
      have different : selected.1.val ≠ visits := by simpa using waiting
      simp only [decisionPassed]
      by_cases earlier : selected.1.val < visits
      · have advanced : selected.1.val < visits + 1 := by omega
        simp only [earlier, advanced, decide_true]
      · have advanced : ¬ selected.1.val < visits + 1 := by omega
        simp only [earlier, advanced, decide_false]
  · simp only [decisionWindowPlayers, active, ↓reduceIte] at supported
    exact frame.waiting_response runtime leaks owner event opening offset selected
      visits initial current who action (app.silentPolicy_cases _ _ action supported)
        (by simp only [active, ↓reduceIte, Nat.add_zero])

theorem DecisionWindowFrame.run (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (selected : Fin slots × Bool) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.DecisionWindowFrame leaks owner event opening offset selected visits
      initial current) (network : runtime.NetworkPolicy leaks) (roster : List Player)
    (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks
      (runtime.decisionWindowPlayers leaks owner event opening offset selected) network
        (roster.map ServiceInstruction.player) current).support)
    (owned : ∀ candidate raw, opening = some (candidate, raw) → candidate.1 = owner)
    (valid : selected.2 = true → ∀ candidate raw, opening = some (candidate, raw) →
      initial.application.candidates.lookup candidate = .openable raw) :
    runtime.DecisionWindowFrame leaks owner event opening offset selected
      (visits + roster.count owner) initial final := by
  let app := runtime.reactiveApplication leaks
  induction roster generalizing current visits with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      simpa only [List.count_nil, Nat.add_zero] using frame
  | cons who rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map,
        PMF.bind_bind, Function.comp_def] at reached
      obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨action, supported, reached⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have activated := frame.activate runtime leaks owner event opening offset selected
        visits initial current who sample
      have responded := activated.response runtime leaks owner event opening offset selected
        visits initial (current.sampledActivation app who sample) who action supported owned valid
      have continued := ih (visits + if who = owner then 1 else 0)
        ((current.sampledActivation app who sample).respond app who action) responded reached
      convert continued using 1
      simp only [List.count_cons]
      split <;> simp_all [beq_iff_eq, Nat.add_comm, Nat.add_left_comm]

theorem DecisionWindowFrame.before_published (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (selected : Fin slots × Bool) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.DecisionWindowFrame leaks owner event opening offset selected visits
      initial current) (before : decisionPassed selected visits = false) :
    current.network.Satisfies fun message =>
      message.id ∈ current.network.ledger.map Message.id := by
  have serial : current.network.nextSerial owner = initial.network.nextSerial owner := by
    simpa only [before, Bool.false_eq_true, and_false, ↓reduceIte, Nat.add_zero] using
      congrFun frame.counters owner
  have impossible (message : Message Player (WitnessedPacket graph))
      (bound : message.id.2 < current.network.nextSerial message.id.1)
      (safe : message.id ∈ initial.network.ledger.map Message.id ∨
        message = runtime.decisionEnvelope leaks owner event opening selected.2 initial) :
      message.id ∈ current.network.ledger.map Message.id := by
    rcases safe with old | rfl
    · simpa only [frame.ledger] using old
    · change initial.network.nextSerial owner < current.network.nextSerial owner at bound
      omega
  exact ⟨fun message member => impossible message (frame.serials.pending message member)
      (frame.packets.pending message member),
    fun message member => impossible message (frame.serials.ledger message member)
      (frame.packets.ledger message member),
    fun who message member => impossible message (frame.serials.leaked who message member)
      (frame.packets.leaked who message member),
    fun input member => impossible input (frame.serials.inputs input member)
      (frame.packets.inputs input member)⟩

theorem DecisionWindowFrame.selection (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (selected : Fin slots × Bool)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.DecisionWindowFrame leaks owner event opening offset selected slots
      initial current) (serials : initial.network.SerialsBeforeNext) :
    runtime.reactiveLatest leaks event owner
      (current.observeEnvironment (runtime.reactiveApplication leaks)) =
        .include (owner, initial.network.nextSerial owner) := by
  let app := runtime.reactiveApplication leaks
  have sent : decisionPassed selected slots = true := by
    simpa only [decisionPassed, decide_eq_true_eq] using selected.1.isLt
  have pending := frame.sent sent
  have fresh : (current.observeEnvironment app).Unpublished app
      (owner, initial.network.nextSerial owner) := by
    change (owner, initial.network.nextSerial owner) ∉ current.network.ledger.map Message.id
    rw [frame.ledger]
    exact serials.next_unpublished owner
  have addressed := runtime.decisionEnvelope_addressed leaks owner event opening selected.2
    initial
  unfold reactiveLatest
  split
  · rename_i absent
    have excluded := List.find?_eq_none.mp absent
      (runtime.decisionEnvelope leaks owner event opening selected.2 initial)
        (List.mem_reverse.mpr pending)
    exact False.elim (excluded (decide_eq_true_iff.mpr ⟨rfl, addressed, fresh⟩))
  · rename_i message found
    have member := List.mem_reverse.mp (List.mem_of_find?_eq_some found)
    have good : message.sender = owner ∧ message.payload.call.event? graph = some event ∧
        (current.observeEnvironment app).Unpublished app message.id := by
      simpa only [decide_eq_true_eq] using List.find?_some found
    rcases frame.packets.pending message member with old | rfl
    · apply False.elim (good.2.2 ?_)
      change message.id ∈ current.network.ledger.map Message.id
      rw [frame.ledger]
      exact old
    · rfl

theorem DecisionWindowFrame.lookup_sent (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (selected : Fin slots × Bool) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.DecisionWindowFrame leaks owner event opening offset selected visits
      initial current) (serials : initial.network.SerialsBeforeNext)
    (sent : decisionPassed selected visits = true) :
    current.network.lookup (owner, initial.network.nextSerial owner) =
      some (runtime.decisionEnvelope leaks owner event opening selected.2 initial) := by
  have pending := frame.sent sent
  cases found : current.network.lookup (owner, initial.network.nextSerial owner) with
  | none =>
      have excluded := List.find?_eq_none.mp found
        (runtime.decisionEnvelope leaks owner event opening selected.2 initial) pending
      exact False.elim (excluded (decide_eq_true_iff.mpr rfl))
  | some message =>
      have member := List.mem_of_find?_eq_some found
      have same : message.id = (owner, initial.network.nextSerial owner) := by
        simpa only [decide_eq_true_eq] using List.find?_some found
      rcases frame.packets.pending message member with old | rfl
      · exact False.elim (serials.next_unpublished owner (same ▸ old))
      · rfl

theorem DecisionWindowFrame.include_published (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (selected : Fin slots × Bool) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.DecisionWindowFrame leaks owner event opening offset selected visits
      initial current) (serials : initial.network.SerialsBeforeNext)
    (sent : decisionPassed selected visits = true) :
    let included := current.network.includePending (owner, initial.network.nextSerial owner)
    included.2.Satisfies fun message => message.id ∈ included.2.ledger.map Message.id := by
  have found := frame.lookup_sent runtime leaks owner event opening offset selected
    visits initial current serials sent
  apply (frame.packets.includePending (owner, initial.network.nextSerial owner)).mono
  intro message safe
  simp only [MessageNetwork.includePending, found, List.map_append, List.mem_append]
  rcases safe with old | rfl
  · exact Or.inl (by simpa only [frame.ledger] using old)
  · exact Or.inr (by simp)

theorem DecisionWindowFrame.settle (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (selected : Fin slots × Bool)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.DecisionWindowFrame leaks owner event opening offset selected slots
      initial current) (serials : initial.network.SerialsBeforeNext)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.interactionStep leaks players network
      (.includeLatest event owner) current).support) :
    final.application = ((runtime.reactiveApplication leaks).handle initial.application
      (runtime.decisionEnvelope leaks owner event opening selected.2 initial)).getD
        initial.application ∧
    final.network.Satisfies (fun message => message.id ∈ final.network.ledger.map Message.id) := by
  let app := runtime.reactiveApplication leaks
  have sent : decisionPassed selected slots = true := by
    simpa only [decisionPassed, decide_eq_true_eq] using selected.1.isLt
  have selection := frame.selection runtime leaks owner event opening offset selected
    initial current serials
  have found := frame.lookup_sent runtime leaks owner event opening offset selected
    slots initial current serials sent
  have published := frame.include_published runtime leaks owner event opening offset
    selected slots initial current serials sent
  simp only [interactionStep, interactionInstruction, PMF.pure_bind, selection,
    ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
    PMF.pure_map, PMF.pure_bind, ReactiveApplication.Command.actor?,
    ReactiveApplication.resume] at reached
  cases (PMF.mem_support_pure_iff _ _).mp reached
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    found, frame.application]
  refine ⟨True.intro, ?_⟩
  simpa only [MessageNetwork.includePending, found] using published

theorem decisionWindow_settlement (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (roster : List Player) (selected : Fin (roster.count owner) × Bool)
    (initial : (runtime.reactiveApplication leaks).Execution)
    (serials : initial.network.SerialsBeforeNext)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id)
    (owned : ∀ candidate raw, opening = some (candidate, raw) → candidate.1 = owner)
    (valid : selected.2 = true → ∀ candidate raw, opening = some (candidate, raw) →
      initial.application.candidates.lookup candidate = .openable raw)
    (network : runtime.NetworkPolicy leaks)
    (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks
      (runtime.decisionWindowPlayers leaks owner event opening
        (initial.recall owner).length selected) network
      (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) initial).support) :
    final.application = ((runtime.reactiveApplication leaks).handle initial.application
      (runtime.decisionEnvelope leaks owner event opening selected.2 initial)).getD
        initial.application ∧
    final.network.Satisfies (fun message => message.id ∈ final.network.ledger.map Message.id) := by
  rw [runtime.runInteractionPlan_append] at reached
  obtain ⟨current, prior, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have frame := DecisionWindowFrame.initial runtime leaks owner event opening selected
    initial serials published
  have finished := frame.run runtime leaks owner event opening (initial.recall owner).length
    selected 0 initial initial network roster current prior owned valid
  simp only [Nat.zero_add] at finished
  have inclusion : final ∈ (runtime.interactionStep leaks
      (runtime.decisionWindowPlayers leaks owner event opening (initial.recall owner).length
        selected) network (.includeLatest event owner) current).support := by
    simpa only [runInteractionPlan, PMF.bind_pure] using reached
  exact finished.settle runtime leaks owner event opening (initial.recall owner).length
    selected initial current serials _ network final inclusion

theorem decisionWindowMixture_settlement (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (roster : List Player) (choices : PMF (Fin (roster.count owner) × Bool))
    (initial : (runtime.reactiveApplication leaks).Execution)
    (serials : initial.network.SerialsBeforeNext)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id)
    (owned : ∀ candidate raw, opening = some (candidate, raw) → candidate.1 = owner)
    (valid : ∀ candidate raw, opening = some (candidate, raw) →
      initial.application.candidates.lookup candidate = .openable raw)
    (network : runtime.NetworkPolicy leaks) :
    (runtime.runInteractionPlan leaks
      (runtime.decisionWindowMixturePlayers leaks owner event opening
        (initial.recall owner).length choices) network
      (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) initial).map
        (fun final => final.application) =
      choices.map (fun selected => ((runtime.reactiveApplication leaks).handle initial.application
        (runtime.decisionEnvelope leaks owner event opening selected.2 initial)).getD
          initial.application) := by
  rw [runtime.decisionWindowMixture_law leaks owner event opening
    (initial.recall owner).length choices network _ initial (Nat.le_refl _), PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro selected _
  apply pmf_eq_pure_of_support_subset_singleton
  intro result supported
  obtain ⟨final, reached, rfl⟩ := PMF.support_map .. ▸ supported
  exact (runtime.decisionWindow_settlement leaks owner event opening roster selected
    initial serials published owned (fun _ => valid) network final reached).1

end Vegas.EventGraphRuntime
