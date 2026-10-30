/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealService
import Vegas.Pending.ReactiveAsyncContract
import Vegas.Pending.ReactiveStateInvariant
import Interaction.ReactiveOwnerSelection
import Interaction.ReactiveRecallInvariant
import Interaction.ReactiveReceipts

/-! # Packet selection and receipts in initialized services

An authored packet with a sole event identifier remains pending until publication,
and the reserved inclusion selects that identifier. Initialized raw histories
supply graph reachability, provenance, recall, packet retention and sound receipts
under arbitrary player responses and schedulers.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] in
private theorem forall₂_exists_right {α β : Type} {R : α → β → Prop} :
    ∀ {left : List α} {right : List β}, List.Forall₂ R left right →
      ∀ item ∈ left, ∃ partner ∈ right, R item partner
  | _, _, .nil, _, member => by cases member
  | _, _, .cons head tail, item, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self .., head⟩
      · obtain ⟨partner, inside, related⟩ := forall₂_exists_right tail item later
        exact ⟨partner, List.mem_cons_of_mem _ inside, related⟩

omit [DecidableEq Player] in
/-- A published identifier has a receipt. -/
theorem receipt_of_published {app : ReactiveApplication Player} (execution : app.Execution)
    (sound : execution.ReceiptsSound app (fun _ => True)) (id : MessageId Player)
    (published : id ∈ execution.network.ledger.map Message.id) :
    ∃ accepted, (id, accepted) ∈ execution.receipts := by
  obtain ⟨message, member, rfl⟩ := List.mem_map.mp published
  obtain ⟨receipt, inside, same, _⟩ := forall₂_exists_right sound message member
  refine ⟨receipt.2, ?_⟩
  rw [← same]
  exact inside

section Selection

variable {graph : EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- When every packet of its own an owner emits for an event carries the
identifier of its authored packet, that packet, when unpublished, is pending and its
identifier is exactly what `reactiveLatest` selects: every pending envelope by
that author addressed to the event was emitted by the owner, so it carries that
identifier. -/
theorem reactiveLatest_sole
    (execution : (runtime.reactiveApplication leaks).Execution)
    (origins : execution.Provenance (runtime.reactiveApplication leaks))
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (retained : execution.network.PendingOrPublished)
    (event : graph.EventId) (owner : Player)
    (earlier later : List (runtime.reactiveApplication leaks).PlayerEntry)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket graph))
    (split : execution.recall owner = earlier ++ entry :: later)
    (emitted : entry.emitted = some message) (authored : message.sender = owner)
    (addressed : message.payload.call.event? graph = some event)
    (sole : ∀ other ∈ earlier ++ later, ¬ EmitsOtherFor runtime leaks other event message.id)
    (unpublished : message.id ∉ execution.network.ledger.map Message.id) :
    message ∈ execution.network.pending ∧
      runtime.reactiveLatest leaks event owner
        (execution.observeEnvironment (runtime.reactiveApplication leaks)) =
          .include message.id := by
  have output : message ∈ (runtime.reactiveApplication leaks).outputs (execution.recall owner) :=
    List.mem_filterMap.mpr ⟨entry, by rw [split]; simp, emitted⟩
  have pending := ((runtime.reactiveApplication leaks).pending_iff_recalled execution owner
    message authored unpublished origins recalled retained).mpr output
  refine ⟨pending, ?_⟩
  unfold reactiveLatest
  split
  · rename_i absent
    exact (List.find?_eq_none.mp absent message (List.mem_reverse.mpr pending)
      (decide_eq_true ⟨authored, addressed, unpublished⟩)).elim
  · rename_i selected found
    have good := List.find?_some found
    simp only [decide_eq_true_eq] at good
    obtain ⟨selectedAuthored, selectedAddressed, selectedUnpublished⟩ := good
    have selectedPending := List.mem_reverse.mp (List.mem_of_find?_eq_some found)
    have selectedOutput := ((runtime.reactiveApplication leaks).pending_iff_recalled execution
      owner selected selectedAuthored selectedUnpublished origins recalled retained).mp
        selectedPending
    obtain ⟨other, member, otherEmitted⟩ := List.mem_filterMap.mp selectedOutput
    rw [split] at member
    have sameId : selected.id = message.id := by
      by_cases same : other = entry
      · subst other
        rw [emitted] at otherEmitted
        cases Option.some.inj otherEmitted
        rfl
      · have outside : other ∈ earlier ++ later := by
          simp only [List.mem_append, List.mem_cons] at member ⊢
          tauto
        by_contra different
        exact sole other outside ⟨selected, otherEmitted, selectedAuthored.trans authored.symm,
          selectedAddressed, different⟩
    rw [sameId]

/-- Including the identifier of a pending envelope records a receipt for it. -/
theorem includePending_receipt_of_pending
    (execution : (runtime.reactiveApplication leaks).Execution)
    (message : Message Player (WitnessedPacket graph))
    (pending : message ∈ execution.network.pending) :
    ∃ accepted, (message.id, accepted) ∈
      (execution.includePending (runtime.reactiveApplication leaks) message.id).receipts := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  cases found : execution.network.lookup message.id with
  | none =>
      exact (List.find?_eq_none.mp found message pending (decide_eq_true rfl)).elim
  | some selected =>
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _)⟩

end Selection

/-! ## Facts at every legal history -/

/-- Scheduler-independent facts at every legal roster-service history: the
runtime invariant, envelope provenance, input recall, retention of known
envelopes, and receipts for published envelopes. -/
theorem roster_trace_facts (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    {control : (serviceApplication setup mode deadline leaks).Control}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some control)) :
    (∃ inputs, control.execution.application.Invariant inputs) ∧
      control.execution.Provenance (serviceApplication setup mode deadline leaks) ∧
      control.execution.InputRecall (serviceApplication setup mode deadline leaks) ∧
      control.execution.network.PendingOrPublished ∧
      control.execution.ReceiptsSound (serviceApplication setup mode deadline leaks)
          (fun _ => True) := by
  have nativeTrace :
      ((serviceApplication setup mode deadline leaks).protocol
        ((setup.initialLaw.map setup.eventInputs).map State.initial)
        horizon scheduler).Trace (some control) := by
    rw [PMF.map_comp]
    exact trace
  have valid := (serviceRuntime setup mode deadline).reactive_history_invariant leaks
    (setup.initialLaw.map setup.eventInputs) horizon scheduler nativeTrace
  have receipts : (serviceApplication setup mode deadline leaks).ServiceInvariant scheduler
      (fun execution => execution.ReceiptsSound (serviceApplication setup mode deadline leaks)
          (fun _ => True)) :=
    { respond := fun execution who action valid =>
        (serviceApplication setup mode deadline leaks).receiptsSound_respond _ execution who
        action valid
      environment := fun execution next command valid _ reached =>
        (serviceApplication setup mode deadline leaks).receiptsSound_environmentStep _ execution
        next command valid (fun _ _ _ => trivial) reached }
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨inputs, _supported, invariant⟩ := valid
    exact ⟨inputs, invariant⟩
  · exact (serviceApplication setup mode deadline leaks).history_provenance
        (serviceInitialLaw setup mode) horizon scheduler trace
  · exact (serviceApplication setup mode deadline leaks).history_inputRecall
        (serviceInitialLaw setup mode) horizon scheduler trace
  · exact (serviceApplication setup mode deadline leaks).pendingOrPublished_history scheduler
        (serviceInitialLaw setup mode) horizon trace
  · exact receipts.history (serviceInitialLaw setup mode) horizon
      (fun state _ => (serviceApplication setup mode deadline leaks).receiptsSound_initial _
          state) trace

end Vegas
