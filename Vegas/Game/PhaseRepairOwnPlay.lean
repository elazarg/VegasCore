/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseBindingResponseRatio
import Vegas.Game.PhaseWaitingPrefix
import Vegas.Game.PhaseOpeningResponseSymmetry

/-! # Actual callback witnesses for directed response comparisons -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- A sending comparison records the actual replacement slot, legal raw
material at the repaired callback and the chosen typed source result. -/
def phaseBindingSendingPair (who : Player)
    (firstRecord secondRecord : (N).InfoState who × (E).Action who) : Prop :=
  ∃ (first second : (app).Control)
    (_firstTrace : (E).Trace (some first)) (_secondTrace : (E).Trace (some second))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (_binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (serial : Nat) (preparation : Option (Raw L))
    (evidence : EvidenceRequest (serviceGraph setup mode))
    (result : PublicationResult (L.Val payload)) (original : (app).Action),
    first.actor = some who ∧ second.actor = some who ∧
    second.execution.application.SeedRequest who ⟨second.execution.application.attempt, event⟩ ∧
    (∀ message ∈ (app).outputs (second.execution.recall who), PhaseCount.event? message.payload ≠
      some ⟨second.execution.application.attempt, event⟩) ∧
    (∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) ∧
    second.execution.application.current.excluded = ∅ ∧
    original ∈ PhaseCount.onePacketActions runtime leaks bounds who (first.execution.recall who)
      (first.execution.observe app who) ∧
    (⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩ : (app).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds who (second.execution.recall who)
        (second.execution.observe app who) ∧
    firstRecord = (some (first.execution.recall who, first.execution.observe app who), original) ∧
    secondRecord = (some (second.execution.recall who, second.execution.observe app who),
      phaseBindingResponse runtime leaks who event payload result serial)

/-- An opening pair retains the directed physical frame and the actual source
callback's continuation to a clear binding request. Both raw actions coincide. -/
def phaseOpeningResponsePair (who : Player)
    (firstRecord secondRecord : (N).InfoState who × (E).Action who) : Prop :=
  ∃ (remaining : Nat) (original repaired : (app).Execution)
    (memory : BindingMemory runtime (PhaseBindingRepair.nativeLeaks
      (graph := serviceGraph setup mode)))
    (_frame : PhaseBindingRepair.Frame runtime leaks memory who original repaired)
    (leftTrace : (E).Trace (some ⟨remaining, some who, original⟩))
    (_rightTrace : (E).Trace (some ⟨remaining, some who, repaired⟩))
    (final : (app).Control) (finalTrace : (E).Trace (some final))
    (_prefix : TracePrefix leftTrace finalTrace)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding who payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve who payload binding checks)
    (_node : nodeView (serviceGraph setup mode) event =
      .resolve who payload binding checks outputEq codeEq)
    (bindingEvent : (serviceGraph setup mode).EventId) (bindingOwner : Player)
    (bindingPayload : L.Ty)
    (_bindingOutput : (serviceGraph setup mode).outputLayout bindingEvent =
      .binding bindingOwner bindingPayload) (action : (app).Action),
    final.execution.application.current.excluded = ∅ ∧
    original.application.SeedRequest who ⟨original.application.attempt, event⟩ ∧
    repaired.application.SeedRequest who ⟨repaired.application.attempt, event⟩ ∧
    (∀ message ∈ (app).outputs (original.recall who), PhaseCount.event? message.payload ≠
      some ⟨original.application.attempt, event⟩) ∧
    (∀ message ∈ (app).outputs (repaired.recall who), PhaseCount.event? message.payload ≠
      some ⟨repaired.application.attempt, event⟩) ∧
    (∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) ∧
    final.execution.application.SeedRequest bindingOwner
      ⟨final.execution.application.attempt, bindingEvent⟩ ∧
    firstRecord = (some (original.recall who, original.observe app who), action) ∧
    secondRecord = (some (repaired.recall who, repaired.observe app who), action)

/-- Inert callbacks have no owned request or have already sent for the current
request. Both cases retain actual callback and physical own-packet evidence. -/
def phaseInertResponsePair (who : Player)
    (firstRecord secondRecord : (N).InfoState who × (E).Action who) : Prop :=
  ∃ (first second : (app).Control)
    (_firstTrace : (E).Trace (some first)) (_secondTrace : (E).Trace (some second)),
    first.actor = some who ∧ second.actor = some who ∧
    first.execution.application.current.excluded = ∅ ∧
    second.execution.application.current.excluded = ∅ ∧
    ((∀ coordinate, ¬first.execution.application.SeedRequest who coordinate) ∨
      ∃ coordinate, first.execution.application.SeedRequest who coordinate ∧
        ∃ message ∈ (app).outputs (first.execution.recall who),
          PhaseSeedScheduler.ownPacket coordinate who message = true) ∧
    ((∀ coordinate, ¬second.execution.application.SeedRequest who coordinate) ∨
      ∃ coordinate, second.execution.application.SeedRequest who coordinate ∧
        ∃ message ∈ (app).outputs (second.execution.recall who),
          PhaseSeedScheduler.ownPacket coordinate who message = true) ∧
    firstRecord = (some (first.execution.recall who, first.execution.observe app who), ⟨none⟩) ∧
    secondRecord = (some (second.execution.recall who, second.execution.observe app who), ⟨none⟩)

/-- Chronological comparison of actual own-action records. Counts distinguish
replacement costs from the near-one binding-wait factors; exact opening and
inert factors contribute neither cost. No probability inequality is a field. -/
inductive PhaseRepairOwnPlay (who : Player) :
    List ((N).InfoState who × (E).Action who) →
    List ((N).InfoState who × (E).Action who) → Nat → Nat → Prop
  | nil : PhaseRepairOwnPlay who [] [] 0 0
  | sending {first second restFirst restSecond sends waits}
      (pair : phaseBindingSendingPair setup mode runtime leaks bounds plan horizon scheduler who
        first second)
      (tail : PhaseRepairOwnPlay who restFirst restSecond sends waits) :
      PhaseRepairOwnPlay who (first :: restFirst) (second :: restSecond) (sends + 1) waits
  | waiting {first second restFirst restSecond sends waits}
      (pair : phaseBindingWaitingPair setup mode runtime leaks bounds plan horizon scheduler who
        first second)
      (tail : PhaseRepairOwnPlay who restFirst restSecond sends waits) :
      PhaseRepairOwnPlay who (first :: restFirst) (second :: restSecond) sends (waits + 1)
  | opening {first second restFirst restSecond sends waits}
      (pair : phaseOpeningResponsePair setup mode runtime leaks bounds plan horizon scheduler who
        first second)
      (tail : PhaseRepairOwnPlay who restFirst restSecond sends waits) :
      PhaseRepairOwnPlay who (first :: restFirst) (second :: restSecond) sends waits
  | inert {first second restFirst restSecond sends waits}
      (pair : phaseInertResponsePair setup mode runtime leaks bounds plan horizon scheduler who
        first second)
      (tail : PhaseRepairOwnPlay who restFirst restSecond sends waits) :
      PhaseRepairOwnPlay who (first :: restFirst) (second :: restSecond) sends waits

/-- Actual chronological witnesses concatenate with additive send and wait
counts. In particular, appending any one constructor at the empty relation
extends a trace driver by one callback without inspecting its earlier proof. -/
theorem PhaseRepairOwnPlay.append {who : Player}
    {first second moreFirst moreSecond : List ((N).InfoState who × (E).Action who)}
    {sends waits moreSends moreWaits : Nat}
    (prior : PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who first
      second sends waits)
    (later : PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who moreFirst
      moreSecond moreSends moreWaits) :
    PhaseRepairOwnPlay setup mode runtime leaks bounds plan horizon scheduler who
      (first ++ moreFirst) (second ++ moreSecond) (sends + moreSends) (waits + moreWaits) := by
  induction prior with
  | nil => simpa only [List.nil_append, Nat.zero_add] using later
  | sending pair _prior ih =>
    simpa only [List.cons_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      PhaseRepairOwnPlay.sending pair ih
  | waiting pair _prior ih =>
    simpa only [List.cons_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      PhaseRepairOwnPlay.waiting pair ih
  | opening pair _prior ih => exact PhaseRepairOwnPlay.opening pair ih
  | inert pair _prior ih => exact PhaseRepairOwnPlay.inert pair ih

end Vegas
