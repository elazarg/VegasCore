/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOpeningWindow
import Vegas.Pending.ReactiveServiceRecall
import Interaction.ReactiveAllocation
import Interaction.DeferredObservation

/-! # Protected inclusion after a finite opening window

The proof tracks the actual network through a roster of activations. A selected
owner visit creates one fresh certified envelope; subsequent transmissions can
only replay known envelopes. Pending observations and replay multiplicity remain
in the execution. The invariant below is a proof predicate, not runtime state.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def openingPassed {slots : Nat} (selected : Option (Fin slots)) (visits : Nat) : Bool :=
  selected.any fun slot => slot.val < visits

theorem openingPassed_zero {slots : Nat} (selected : Option (Fin slots)) :
    openingPassed selected 0 = false := by
  cases selected <;> simp [openingPassed]

def windowEnvelope (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (initial : (runtime.reactiveApplication leaks).Execution) :
    Message Player (WitnessedPacket graph) :=
  ⟨(owner, initial.network.nextSerial owner),
    ⟨.opening event candidate raw, some ⟨candidate, raw⟩⟩⟩

structure OpeningWindowFrame (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots)) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution) : Prop where
  application : current.application = initial.application
  ledger : current.network.ledger = initial.network.ledger
  receipts : current.receipts = initial.receipts
  count : (current.recall owner).length = offset + visits
  counters : current.network.nextSerial = fun who => initial.network.nextSerial who +
    if who = owner ∧ openingPassed selected visits then 1 else 0
  serials : current.network.SerialsBeforeNext
  packets : current.network.Satisfies fun message =>
    message.id ∈ initial.network.ledger.map Message.id ∨
      message = runtime.windowEnvelope leaks owner event candidate raw initial
  opened : openingPassed selected visits = true →
    runtime.windowEnvelope leaks owner event candidate raw initial ∈ current.network.pending

theorem OpeningWindowFrame.initial (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    {slots : Nat} (selected : Option (Fin slots))
    (initial : (runtime.reactiveApplication leaks).Execution)
    (serials : initial.network.SerialsBeforeNext)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id) :
    runtime.OpeningWindowFrame leaks owner event candidate raw (initial.recall owner).length
      selected 0 initial initial where
  application := rfl
  ledger := rfl
  receipts := rfl
  count := by simp
  counters := by simp only [openingPassed_zero, Bool.false_eq_true, and_false, ↓reduceIte,
    Nat.add_zero]
  serials := serials
  packets := published.mono fun _ member => Or.inl member
  opened := by simp only [openingPassed_zero, Bool.false_eq_true, false_implies]

theorem OpeningWindowFrame.activate (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots)) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.OpeningWindowFrame leaks owner event candidate raw offset selected visits
      initial current) (who : Player) (sample : Finset (MessageId Player)) :
    runtime.OpeningWindowFrame leaks owner event candidate raw offset selected visits initial
      (current.sampledActivation (runtime.reactiveApplication leaks) who sample) where
  application := frame.application
  ledger := frame.ledger
  receipts := frame.receipts
  count := frame.count
  counters := frame.counters
  serials := frame.serials.learn who sample
  packets := frame.packets.learn who sample
  opened := frame.opened

theorem OpeningWindowFrame.waiting_response (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots)) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.OpeningWindowFrame leaks owner event candidate raw offset selected visits
      initial current) (who : Player) (action : (runtime.reactiveApplication leaks).Action)
    (waiting : action = ⟨none⟩ ∨ ∃ id, action = ⟨some (.replay id)⟩)
    (passed : openingPassed selected (visits + if who = owner then 1 else 0) =
      openingPassed selected visits) :
    runtime.OpeningWindowFrame leaks owner event candidate raw offset selected
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
          message = runtime.windowEnvelope leaks owner event candidate raw initial) ∧
      current.network.pending ⊆ (current.respond app who action).network.pending := by
    rcases waiting with rfl | ⟨id, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, frame.serials, frame.packets, fun _ member => member⟩
    · refine ⟨rfl, ?_, rfl, ?_, frame.serials.replay who id,
        frame.packets.replay who id, ?_⟩
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
  refine ⟨data.1.trans frame.application, data.2.1.trans frame.ledger,
    data.2.2.1.trans frame.receipts, ?_, ?_, data.2.2.2.2.1, data.2.2.2.2.2.1, ?_⟩
  · rw [app.respond_recall_length, frame.count]
    omega
  · rw [passed, data.2.2.2.1]
    exact frame.counters
  · intro opened
    rw [passed] at opened
    exact data.2.2.2.2.2.2 (frame.opened opened)

theorem OpeningWindowFrame.opening_response (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (slot : Fin slots)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.OpeningWindowFrame leaks owner event candidate raw offset (some slot)
      slot.val initial current)
    (owned : candidate.1 = owner)
    (valid : initial.application.candidates.lookup candidate = .openable raw) :
    runtime.OpeningWindowFrame leaks owner event candidate raw offset (some slot)
      (slot.val + 1) initial
      (current.respond (runtime.reactiveApplication leaks) owner
        (runtime.windowOpening leaks event candidate raw)) := by
  let app := runtime.reactiveApplication leaks
  let packet : WitnessedPacket graph := ⟨.opening event candidate raw, some ⟨candidate, raw⟩⟩
  have before : openingPassed (some slot) slot.val = false := by simp [openingPassed]
  have after : openingPassed (some slot) (slot.val + 1) = true := by simp [openingPassed]
  have serial : current.network.nextSerial owner = initial.network.nextSerial owner := by
    simpa only [before, Bool.false_eq_true, and_false, ↓reduceIte, Nat.add_zero] using
      congrFun frame.counters owner
  have prior : current.network.nextSerial = initial.network.nextSerial := by
    simpa only [before, Bool.false_eq_true, and_false, ↓reduceIte, Nat.add_zero] using
      frame.counters
  have materialized := runtime.windowOpening_packet leaks owner event candidate raw
    current.application (current.network.known owner) owned (frame.application ▸ valid)
  have network : (current.respond app owner
      (runtime.windowOpening leaks event candidate raw)).network =
      (current.network.submit owner packet).2 := by
    change (current.network.submit owner (app.packet current.application owner
      (current.network.known owner) (disclosureSubmission (.opening event candidate raw)))).2 = _
    rw [materialized]
  refine ⟨frame.application, ?_, frame.receipts, ?_, ?_, ?_, ?_, ?_⟩
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
    exact Or.inr (by simp only [windowEnvelope, serial]; rfl)
  · intro _
    rw [network]
    simp only [MessageNetwork.submit, List.mem_append, List.mem_singleton]
    exact Or.inr (by simp only [windowEnvelope, serial]; rfl)

theorem OpeningWindowFrame.response (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots)) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.OpeningWindowFrame leaks owner event candidate raw offset selected visits
      initial current) (who : Player) (action : (runtime.reactiveApplication leaks).Action)
    (supported : action ∈ (runtime.openingWindowPlayers leaks owner event candidate raw offset
      selected who (current.recall who)
        (current.observe (runtime.reactiveApplication leaks) who)).support)
    (owned : candidate.1 = owner)
    (valid : selected.isSome → initial.application.candidates.lookup candidate = .openable raw) :
    runtime.OpeningWindowFrame leaks owner event candidate raw offset selected
      (visits + if who = owner then 1 else 0) initial
      (current.respond (runtime.reactiveApplication leaks) who action) := by
  let app := runtime.reactiveApplication leaks
  by_cases active : who = owner
  · subst who
    simp only [openingWindowPlayers, ↓reduceIte, ReactiveApplication.scheduledPolicy,
      frame.count] at supported
    split at supported
    · rename_i chosen
      cases selected with
      | none => simp at chosen
      | some slot =>
          have atSlot : visits = slot.val := by simpa using chosen.symm
          subst visits
          cases FinDist.mem_support_pure.mp supported
          simpa only [↓reduceIte] using
            frame.opening_response runtime leaks owner event candidate raw offset slot
              initial current owned (valid rfl)
    · rename_i waiting
      apply frame.waiting_response runtime leaks owner event candidate raw offset selected
        visits initial current owner action (app.replayPolicy_cases _ _ action supported)
      simp only [↓reduceIte]
      cases selected with
      | none => rfl
      | some slot =>
          have different : slot.val ≠ visits := by simpa using waiting
          simp only [openingPassed, Option.any_some]
          by_cases earlier : slot.val < visits
          · have advanced : slot.val < visits + 1 := by omega
            simp only [earlier, advanced, decide_true]
          · have advanced : ¬ slot.val < visits + 1 := by omega
            simp only [earlier, advanced, decide_false]
  · simp only [openingWindowPlayers, active, ↓reduceIte] at supported
    exact frame.waiting_response runtime leaks owner event candidate raw offset selected
      visits initial current who action (app.replayPolicy_cases _ _ action supported)
        (by simp only [active, ↓reduceIte, Nat.add_zero])

theorem OpeningWindowFrame.run (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots)) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.OpeningWindowFrame leaks owner event candidate raw offset selected visits
      initial current) (network : runtime.NetworkPolicy leaks) (roster : List Player)
    (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks
      (runtime.openingWindowPlayers leaks owner event candidate raw offset selected) network
        (roster.map ServiceInstruction.player) current).support)
    (owned : candidate.1 = owner)
    (valid : selected.isSome → initial.application.candidates.lookup candidate = .openable raw) :
    runtime.OpeningWindowFrame leaks owner event candidate raw offset selected
      (visits + roster.count owner) initial final := by
  let app := runtime.reactiveApplication leaks
  induction roster generalizing current visits with
  | nil =>
      cases FinDist.mem_support_pure.mp reached
      simpa only [List.count_nil, Nat.add_zero] using frame
  | cons who rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, FinDist.bind_map,
        FinDist.bind_bind] at reached
      obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      obtain ⟨action, supported, reached⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      have activated := frame.activate runtime leaks owner event candidate raw offset selected
        visits initial current who sample
      have responded := activated.response runtime leaks owner event candidate raw offset selected
        visits initial (current.sampledActivation app who sample) who action supported owned valid
      have continued := ih (visits + if who = owner then 1 else 0)
        ((current.sampledActivation app who sample).respond app who action) responded reached
      convert continued using 1
      simp only [List.count_cons]
      split <;> simp_all [beq_iff_eq, Nat.add_comm, Nat.add_left_comm]

theorem OpeningWindowFrame.before_published (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots)) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.OpeningWindowFrame leaks owner event candidate raw offset selected visits
      initial current) (before : openingPassed selected visits = false) :
    current.network.Satisfies fun message =>
      message.id ∈ current.network.ledger.map Message.id := by
  have serial : current.network.nextSerial owner = initial.network.nextSerial owner := by
    simpa only [before, Bool.false_eq_true, and_false, ↓reduceIte, Nat.add_zero] using
      congrFun frame.counters owner
  have impossible (message : Message Player (WitnessedPacket graph))
      (bound : message.id.2 < current.network.nextSerial message.id.1)
      (safe : message.id ∈ initial.network.ledger.map Message.id ∨
        message = runtime.windowEnvelope leaks owner event candidate raw initial) :
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
    fun input member => impossible input.envelope (frame.serials.inputs input member)
      (frame.packets.inputs input member)⟩

theorem OpeningWindowFrame.selection (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots))
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.OpeningWindowFrame leaks owner event candidate raw offset selected slots
      initial current) (serials : initial.network.SerialsBeforeNext) :
    runtime.reactiveLatest leaks event owner
      (current.observeEnvironment (runtime.reactiveApplication leaks)) =
        if selected.isSome then .include (owner, initial.network.nextSerial owner) else .wait := by
  let app := runtime.reactiveApplication leaks
  cases selected with
  | none =>
      have allPublished := frame.before_published runtime leaks owner event candidate raw offset
        none slots initial current rfl
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      unfold reactiveLatest
      split
      · rfl
      · rename_i message found
        have member := List.mem_reverse.mp (List.mem_of_find?_eq_some found)
        have good : message.sender = owner ∧ message.payload.call.event? graph = some event ∧
            (current.observeEnvironment app).Unpublished app message.id := by
          simpa only [decide_eq_true_eq] using List.find?_some found
        exact False.elim (good.2.2 (allPublished.pending message member))
  | some slot =>
      have opened : openingPassed (some slot) slots = true := by
        simpa only [openingPassed, Option.any_some, decide_eq_true_eq] using slot.isLt
      have pending := frame.opened opened
      have fresh : (current.observeEnvironment app).Unpublished app
          (owner, initial.network.nextSerial owner) := by
        change (owner, initial.network.nextSerial owner) ∉ current.network.ledger.map Message.id
        rw [frame.ledger]
        exact serials.next_unpublished owner
      simp only [Option.isSome_some, ↓reduceIte]
      unfold reactiveLatest
      split
      · rename_i absent
        have excluded := List.find?_eq_none.mp absent
          (runtime.windowEnvelope leaks owner event candidate raw initial)
            (List.mem_reverse.mpr pending)
        exact False.elim (excluded (decide_eq_true_iff.mpr ⟨rfl, rfl, fresh⟩))
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

theorem OpeningWindowFrame.lookup_opened (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots)) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.OpeningWindowFrame leaks owner event candidate raw offset selected visits
      initial current) (serials : initial.network.SerialsBeforeNext)
    (opened : openingPassed selected visits = true) :
    current.network.lookup (owner, initial.network.nextSerial owner) =
      some (runtime.windowEnvelope leaks owner event candidate raw initial) := by
  have pending := frame.opened opened
  cases found : current.network.lookup (owner, initial.network.nextSerial owner) with
  | none =>
    have excluded := List.find?_eq_none.mp found
      (runtime.windowEnvelope leaks owner event candidate raw initial) pending
    exact False.elim (excluded (decide_eq_true_iff.mpr rfl))
  | some message =>
    have member := List.mem_of_find?_eq_some found
    have same : message.id = (owner, initial.network.nextSerial owner) := by
      simpa only [decide_eq_true_eq] using List.find?_some found
    rcases frame.packets.pending message member with old | rfl
    · exact False.elim (serials.next_unpublished owner (same ▸ old))
    · rfl

theorem OpeningWindowFrame.include_published (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots)) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.OpeningWindowFrame leaks owner event candidate raw offset selected visits
      initial current) (serials : initial.network.SerialsBeforeNext)
    (opened : openingPassed selected visits = true) :
    let included := current.network.includePending (owner, initial.network.nextSerial owner)
    included.2.Satisfies fun message => message.id ∈ included.2.ledger.map Message.id := by
  have found := frame.lookup_opened runtime leaks owner event candidate raw offset selected
    visits initial current serials opened
  apply (frame.packets.includePending (owner, initial.network.nextSerial owner)).mono
  intro message safe
  simp only [MessageNetwork.includePending, found, List.map_append, List.mem_append]
  rcases safe with old | rfl
  · exact Or.inl (by simpa only [frame.ledger] using old)
  · exact Or.inr (by simp)

theorem OpeningWindowFrame.settle (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots))
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.OpeningWindowFrame leaks owner event candidate raw offset selected slots
      initial current) (serials : initial.network.SerialsBeforeNext)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.interactionStep leaks players network
      (.includeLatest event owner) current).support) :
    final.application = (if selected.isSome then
      ((runtime.reactiveApplication leaks).handle initial.application
        (runtime.windowEnvelope leaks owner event candidate raw initial)).getD initial.application
      else initial.application) ∧
    final.network.Satisfies (fun message => message.id ∈ final.network.ledger.map Message.id) := by
  let app := runtime.reactiveApplication leaks
  have selection := frame.selection runtime leaks owner event candidate raw offset selected
    initial current serials
  simp only [interactionStep, interactionInstruction, FinDist.pure_bind, selection] at reached
  cases selected with
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
        FinDist.map_pure, FinDist.pure_bind, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume] at reached
      cases FinDist.mem_support_pure.mp reached
      exact ⟨frame.application, frame.before_published runtime leaks owner event candidate raw
        offset none slots initial current rfl⟩
  | some slot =>
      have opened : openingPassed (some slot) slots = true := by
        simpa only [openingPassed, Option.any_some, decide_eq_true_eq] using slot.isLt
      have found := frame.lookup_opened runtime leaks owner event candidate raw offset (some slot)
        slots initial current serials opened
      have published := frame.include_published runtime leaks owner event candidate raw offset
        (some slot) slots initial current serials opened
      simp only [Option.isSome_some, ↓reduceIte,
        ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
        FinDist.map_pure, FinDist.pure_bind, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume] at reached
      cases FinDist.mem_support_pure.mp reached
      simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found, frame.application, Option.isSome_some, ↓reduceIte]
      refine ⟨True.intro, ?_⟩
      simpa only [MessageNetwork.includePending, found] using published

theorem openingWindow_settlement (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (roster : List Player) (selected : Option (Fin (roster.count owner)))
    (initial : (runtime.reactiveApplication leaks).Execution)
    (serials : initial.network.SerialsBeforeNext)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id)
    (owned : candidate.1 = owner)
    (valid : selected.isSome → initial.application.candidates.lookup candidate = .openable raw)
    (network : runtime.NetworkPolicy leaks)
    (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks
      (runtime.openingWindowPlayers leaks owner event candidate raw
        (initial.recall owner).length selected) network
      (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) initial).support) :
    final.application = (if selected.isSome then
      ((runtime.reactiveApplication leaks).handle initial.application
        (runtime.windowEnvelope leaks owner event candidate raw initial)).getD initial.application
      else initial.application) ∧
    final.network.Satisfies (fun message => message.id ∈ final.network.ledger.map Message.id) := by
  rw [runtime.runInteractionPlan_append] at reached
  obtain ⟨current, prior, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  have frame := OpeningWindowFrame.initial runtime leaks owner event candidate raw selected
    initial serials published
  have finished := frame.run runtime leaks owner event candidate raw (initial.recall owner).length
    selected 0 initial initial network roster current prior owned valid
  simp only [Nat.zero_add] at finished
  have inclusion : final ∈ (runtime.interactionStep leaks
      (runtime.openingWindowPlayers leaks owner event candidate raw (initial.recall owner).length
        selected) network (.includeLatest event owner) current).support := by
    simpa only [runInteractionPlan, FinDist.bind_pure] using reached
  exact finished.settle runtime leaks owner event candidate raw (initial.recall owner).length
    selected initial current serials _ network final inclusion

theorem openingWindowMixture_settlement (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (roster : List Player) (choices : FinDist (Option (Fin (roster.count owner))))
    (initial : (runtime.reactiveApplication leaks).Execution)
    (serials : initial.network.SerialsBeforeNext)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id)
    (owned : candidate.1 = owner)
    (valid : initial.application.candidates.lookup candidate = .openable raw)
    (network : runtime.NetworkPolicy leaks) :
    (runtime.runInteractionPlan leaks
      (runtime.openingWindowMixturePlayers leaks owner event candidate raw
        (initial.recall owner).length choices) network
      (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) initial).map
        (fun final => final.application) =
      choices.map (fun selected => if selected.isSome then
        ((runtime.reactiveApplication leaks).handle initial.application
          (runtime.windowEnvelope leaks owner event candidate raw initial)).getD initial.application
        else initial.application) := by
  rw [runtime.openingWindowMixture_law leaks owner event candidate raw
    (initial.recall owner).length choices network _ initial (Nat.le_refl _), FinDist.map_bind]
  conv_rhs => rw [FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro selected _
  apply FinDist.eq_pure_of_support_subset_singleton
  intro result supported
  obtain ⟨final, reached, rfl⟩ := FinDist.support_map .. ▸ supported
  exact (runtime.openingWindow_settlement leaks owner event candidate raw roster selected
    initial serials published owned (fun _ => valid) network final reached).1

end Vegas.EventGraphRuntime
