/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealService
import Vegas.Game.SourceServiceFreshCall
import Vegas.Pending.ReactiveEventStability
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.Pending.ReactivePacketEvidence
import Vegas.Pending.ReactiveStateInvariant
import Interaction.ReactiveProvenance
import Interaction.ReactiveMessageIdentity
import Interaction.ReactiveAllocation
import Interaction.ReactiveReceipts

/-! # Raw initialized service-history facts

Readiness, fixed binding meanings, authentic evidence, recall and packet identities follow
from the native operations at every initialized history. They require no reserved schedule,
source policy, factorization or successful public guards.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- The initial native law is the image of the existing typed setup inputs. -/
theorem serviceInitialLaw_eq_inputs :
    serviceInitialLaw setup mode =
      (setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)) := by
  rw [PMF.map_comp]
  rfl

/-- The native facts used to transport acceptable recorded calls. -/
structure LegalFacts (execution : (serviceApplication setup mode deadline leaks).Execution) :
    Prop where
  stable : EntryStable (serviceRuntime setup mode deadline) leaks execution
  eventStable : EntryEventStable (serviceRuntime setup mode deadline) leaks execution
  storeStable : EntryStoreStable (serviceRuntime setup mode deadline) leaks execution
  binding : execution.application.BindingInvariant
  evidence : ((serviceRuntime setup mode deadline).packetEvidence leaks).Sound execution
  receipts : execution.ReceiptsSound (serviceApplication setup mode deadline leaks) (fun _ => True)
  serials : execution.network.SerialsBeforeNext
  unique : execution.network.UniqueIds
  provenance : execution.Provenance (serviceApplication setup mode deadline leaks)
  inputs : execution.InputRecall (serviceApplication setup mode deadline leaks)
  quiescent : ∀ event, ¬ execution.application.AutomaticReady event

/-- Every initialized raw history supplies these facts under arbitrary responses and scheduler. -/
theorem legalFacts (horizon : Nat)
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control)) :
    LegalFacts setup leaks control.execution := by
  let app := serviceApplication setup mode deadline leaks
  have nativeTrace := trace
  rw [serviceInitialLaw_eq_inputs setup] at nativeTrace
  have receipts := (app.receiptServiceInvariant (fun _ => True) (fun _ => True)
    ⟨by intros; trivial, by intros; trivial, by intros; trivial⟩
    (by intros; trivial) scheduler).history (serviceInitialLaw setup mode) horizon
      (fun state _ => ⟨trivial, app.receiptsSound_initial (fun _ => True) state⟩) trace
  exact {
    stable := entryStable_history (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler trace
    eventStable := entryEventStable_history (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler trace
    storeStable := entryStoreStable_history (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler trace
    binding := (serviceRuntime setup mode deadline).reactiveBindingInvariant_history leaks
      (setup.initialLaw.map setup.eventInputs) horizon scheduler nativeTrace
    evidence := ((serviceRuntime setup mode deadline).packetEvidence leaks).history_sound
      (serviceInitialLaw setup mode) horizon scheduler trace
    receipts := receipts.2
    serials := app.serialsBeforeNext_history scheduler (serviceInitialLaw setup mode) horizon trace
    unique := app.uniqueIds_history scheduler (serviceInitialLaw setup mode) horizon control trace
    provenance := app.history_provenance (serviceInitialLaw setup mode) horizon scheduler trace
    inputs := app.history_inputRecall (serviceInitialLaw setup mode) horizon scheduler trace
    quiescent := (serviceRuntime setup mode deadline).reactive_history_quiescent leaks
      (setup.initialLaw.map setup.eventInputs) horizon scheduler nativeTrace }

omit [DecidableEq Player] in
private theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {left : List α} {right : List β}, List.Forall₂ R left right →
      ∀ b ∈ right, ∃ a ∈ left, R a b
  | [], [], .nil, _, member => by simp at member
  | a :: left, b :: right, .cons head tail, x, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨a, List.mem_cons_self, head⟩
      · obtain ⟨y, inside, related⟩ := forall₂_mem_right tail x member
        exact ⟨y, List.mem_cons_of_mem _ inside, related⟩

/-- No receipt names an identifier not yet allocated. -/
theorem no_receipt_next (execution : (serviceApplication setup mode deadline leaks).Execution)
    (sound : execution.ReceiptsSound (serviceApplication setup mode deadline leaks) (fun _ => True))
    (serials : execution.network.SerialsBeforeNext) (who : Player) (accepted : Bool) :
    ((who, execution.network.nextSerial who), accepted) ∉ execution.receipts := by
  intro member
  obtain ⟨message, published, same, _⟩ := forall₂_mem_right sound _ member
  have bound := serials.ledger message published
  rw [← same] at bound
  exact Nat.lt_irrefl _ bound

/-- The entry a response appends to its author's recall. A fresh submission
emits the author's next identifier. -/
theorem respond_recall_self (execution : (serviceApplication setup mode deadline leaks).Execution)
    (who : Player) (action : (serviceApplication setup mode deadline leaks).Action) : ∃ emitted,
    (execution.respond (serviceApplication setup mode deadline leaks) who action).recall who =
    execution.recall who ++
    [⟨execution.observe (serviceApplication setup mode deadline leaks) who, action, emitted⟩] ∧ ∀
    material, action.transmission = some material → ∀ message,
        emitted = some message → message.id = (who, execution.network.nextSerial who) := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      exact ⟨none, by simp [ReactiveApplication.Execution.respond], by simp⟩
  | some material =>
      refine
          ⟨some (execution.network.submit who
              ((serviceApplication setup mode deadline leaks).packet
              ((serviceApplication setup mode deadline leaks).submit execution.application who
              material) who (execution.network.known who) material)).1, by simp only
              [ReactiveApplication.Execution.respond, ↓reduceIte], ?_⟩
      rintro _ ⟨⟩ message ⟨⟩
      rfl

private theorem settled_congr {event : (serviceGraph setup mode).EventId} {id : MessageId Player}
    {before after : (serviceApplication setup mode deadline leaks).Execution}
    (configEq : after.application.config = before.application.config)
    (receiptsEq : after.receipts = before.receipts)
    (settled : Settled setup leaks event id before) : Settled setup leaks event id after := by
  unfold Settled
  rw [configEq, receiptsEq]
  exact settled

/-- A response preserves the settlement invariant. -/
theorem settlesFreshCalls_respond (owner : Player) (event : (serviceGraph setup mode).EventId)
    (bound : (serviceGraph setup mode).EventId → Nat)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (facts : LegalFacts setup leaks execution) (who : Player)
    (action : (serviceApplication setup mode deadline leaks).Action)
    (valid : SettlesFreshCalls setup leaks owner event bound execution) :
    SettlesFreshCalls setup leaks owner event bound
      (execution.respond (serviceApplication setup mode deadline leaks) who action) := by
  let app := serviceApplication setup mode deadline leaks
  have configEq :=
      ((serviceRuntime setup mode deadline).reactive_respond_application leaks execution who
          action).1
  have receiptsEq := app.respond_receipts execution who action
  intro earlier entry later message split call sole
  apply settled_congr setup leaks configEq receiptsEq
  by_cases same : who = owner
  · subst who
    obtain ⟨emitted, recallEq, idOf⟩ := respond_recall_self setup leaks execution owner action
    rw [recallEq] at split
    rcases List.eq_nil_or_concat later with rfl | ⟨init, last, rfl⟩
    · obtain ⟨_, entryEq⟩ := List.append_inj' split rfl
      have newEntry := (List.singleton_inj.mp entryEq).symm
      subst newEntry
      obtain ⟨material, submitted⟩ := call.fresh
      have idEq := idOf material submitted message call.emitted
      have readyNow : execution.application.config.cut.Ready event :=
        (execution.application.publicView_eventReady event).mp call.ready
      refine ⟨fun finished => (readyNow.1 finished).elim, fun accepted member => ?_,
        fun member => ?_⟩
      · rw [idEq] at member
        exact (no_receipt_next setup leaks execution facts.receipts facts.serials owner accepted
          member).elim
      · rw [idEq] at member
        exact (no_receipt_next setup leaks execution facts.receipts facts.serials owner true
          member).elim
    · simp only [List.concat_eq_append] at split sole
      have reassociated : earlier ++ entry :: (init ++ [last]) =
          (earlier ++ entry :: init) ++ [last] := by simp
      rw [reassociated] at split
      obtain ⟨older, _⟩ := List.append_inj' split rfl
      exact valid earlier entry init message older call fun other member =>
        sole other (by
          rcases List.mem_append.mp member with inside | inside
          · exact List.mem_append_left _ inside
          · exact List.mem_append_right _ (List.mem_append_left _ inside))
  · rw [app.respond_recall_other execution who owner (Ne.symm same) action] at split
    exact valid earlier entry later message split call sole

end Vegas
