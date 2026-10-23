/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochFocalWord
import Vegas.Pending.PhaseCountedOpeningSubmission
import Vegas.Game.ReservedEpochStoppedOpening

/-! # Exact old opening episode bits in the actual reserved experiment -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The old opening's physical receipt bit. A previously sent opening must
still be pending; the actual old UNSENT episode uses its first callback/expiry
race and finite next processing epoch. Guard success is a separate question. -/
def openingFrontierReceipt {length : Nat} (tape : Tape Player length)
    (anchor : (app).Execution) (owner : Player) (event : graph.EventId) : Prop := by
  classical
  let unsent := ∀ message ∈ (app).outputs (anchor.recall owner),
    PhaseCount.event? message.payload ≠ some ⟨anchor.application.attempt, event⟩
  exact ∃ entered, anchor.application.current.native.activatedAt event = some entered ∧
    if unsent then
      UnsentQualification runtime leaks (packetCapacity runtime) (completionCycles runtime) tape
        anchor.environmentRecall.length entered owner event
    else ∃ message ∈ anchor.network.pending, ∃ candidate value,
      message.sender = owner ∧ message.payload.packet.call = .opening event candidate value ∧
      message.payload.attempt = anchor.application.attempt ∧
      ∃ epoch, tape.nextProcessingEpoch (anchor.environmentRecall.length /
          cycleWidth (graph := graph) (packetCapacity runtime) + 1) = some epoch ∧
        epoch < completionCycles runtime ∧ epoch - entered < runtime.deadline event

/-- The proposal-emission bit retains late SENDs. Its first callback need only
precede the actual due EXPIRY COMMAND and physical horizon; no processing
qualification or strict callback-clock deadline test occurs here. -/
def openingFrontierEmission {length : Nat} (tape : Tape Player length)
    (anchor : (app).Execution) (owner : Player) (event : graph.EventId) : Prop := by
  classical
  exact (∃ message ∈ (app).outputs (anchor.recall owner), ∃ candidate value,
      message.payload.attempt = anchor.application.attempt ∧
        message.payload.packet.call = .opening event candidate value) ∨
    ∃ entered, anchor.application.current.native.activatedAt event = some entered ∧
      ∃ cursor, anchor.environmentRecall.length ≤ cursor ∧ cursor < executionHorizon runtime ∧
        (∀ view, (command runtime leaks (packetCapacity runtime) tape cursor view).actor? app =
          some owner) ∧
        (∀ earlier, anchor.environmentRecall.length ≤ earlier → earlier < cursor → ∀ view,
          (command runtime leaks (packetCapacity runtime) tape earlier view).actor? app ≠
            some owner) ∧
        (∀ earlier, anchor.environmentRecall.length ≤ earlier → earlier < cursor → ∀ view,
          command runtime leaks (packetCapacity runtime) tape earlier view =
            .application (.expire event) →
            earlier / cycleWidth (graph := graph) (packetCapacity runtime) - entered <
              runtime.deadline event)

/-- Both old receipt branches are invariant under another owner's actual
current response. This reads the literal foreign recall/pending/stamp/cursor;
it does not assert equality of later clocks or private observations. -/
theorem openingFrontierReceipt_respond_foreign {length : Nat} (tape : Tape Player length)
    (execution : (app).Execution) (actor owner : Player) (different : owner ≠ actor)
    (response : (app).Action) (event : graph.EventId) :
    openingFrontierReceipt runtime leaks tape (execution.respond app actor response) owner event ↔
      openingFrontierReceipt runtime leaks tape execution owner event := by
  have recalled := (app).respond_recall_other execution actor owner different response
  have cursor := (app).respond_environmentRecall execution actor response
  have attempt : (execution.respond app actor response).application.attempt =
      execution.application.attempt := by
    cases response with
    | mk transmission => cases transmission <;> rfl
  have activated : (execution.respond app actor response).application.current.native.activatedAt =
      execution.application.current.native.activatedAt := by
    cases response with
    | mk transmission => cases transmission with
      | none => rfl
      | some material =>
        exact congrArg (fun view : PhasePublicView graph => view.native.activatedAt)
          (PhaseCount.submit_publicView execution.application actor material)
  unfold openingFrontierReceipt
  dsimp only
  rw [recalled, cursor, attempt, activated]
  apply exists_congr
  intro entered
  apply and_congr_right
  intro _stamp
  split_ifs with unsent
  · rfl
  · constructor
    · rintro ⟨message, pending, candidate, value, sender, call, address, epoch⟩
      exact ⟨message, (response_foreign_pending runtime leaks execution actor owner different
        response message sender).mp pending, candidate, value, sender, call, address, epoch⟩
    · rintro ⟨message, pending, candidate, value, sender, call, address, epoch⟩
      exact ⟨message, (response_foreign_pending runtime leaks execution actor owner different
        response message sender).mpr pending, candidate, value, sender, call, address, epoch⟩

/-- The old full emission bit also uses the same literal foreign inputs.
In particular a due-cycle callback preceding expiry remains an emission in
both runs even when its physical receipt bit is FALSE. -/
theorem openingFrontierEmission_respond_foreign {length : Nat} (tape : Tape Player length)
    (execution : (app).Execution) (actor owner : Player) (different : owner ≠ actor)
    (response : (app).Action) (event : graph.EventId) :
    openingFrontierEmission runtime leaks tape (execution.respond app actor response) owner event ↔
      openingFrontierEmission runtime leaks tape execution owner event := by
  have recalled := (app).respond_recall_other execution actor owner different response
  have cursor := (app).respond_environmentRecall execution actor response
  have attempt : (execution.respond app actor response).application.attempt =
      execution.application.attempt := by
    cases response with
    | mk transmission => cases transmission <;> rfl
  have activated : (execution.respond app actor response).application.current.native.activatedAt =
      execution.application.current.native.activatedAt := by
    cases response with
    | mk transmission => cases transmission with
      | none => rfl
      | some material =>
        exact congrArg (fun view : PhasePublicView graph => view.native.activatedAt)
          (PhaseCount.submit_publicView execution.application actor material)
  unfold openingFrontierEmission
  rw [recalled, cursor, attempt, activated]

/-- A qualifying later WAIT continuation also qualifies an immediate opening
at the SAME original entered stamp. The retained finite horizon and monotone
next processing epoch supply the implication. -/
theorem openingFrontierReceipt_wait_imp_send {length : Nat} (tape : Tape Player length)
    (execution : (app).Execution) (owner : Player) (event : graph.EventId)
    (candidate : Handle graph) (value : Raw L) (material : WitnessedSubmission graph)
    (call : material.call.packet = .opening event candidate value)
    (unsent : ∀ message ∈ (app).outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩) :
    openingFrontierReceipt runtime leaks tape (execution.respond app owner ⟨none⟩) owner event →
      openingFrontierReceipt runtime leaks tape
        (execution.respond app owner ⟨some material⟩) owner event := by
  classical
  let silent := execution.respond app owner ⟨none⟩
  let sent := execution.respond app owner ⟨some material⟩
  let message : Message Player (app).Payload :=
    ⟨(owner, execution.network.nextSerial owner),
      (app).packet ((app).submit execution.application owner material) owner
        (execution.network.known owner) material⟩
  have silentOutputs : (app).outputs (silent.recall owner) =
      (app).outputs (execution.recall owner) := by
    simp only [silent, ReactiveApplication.Execution.respond, ↓reduceIte,
      ReactiveApplication.outputs, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, List.append_nil]
  have silentUnsent : ∀ packet ∈ (app).outputs (silent.recall owner),
      PhaseCount.event? packet.payload ≠ some ⟨silent.application.attempt, event⟩ := by
    simpa only [silentOutputs, show silent.application.attempt = execution.application.attempt
      from rfl] using unsent
  have pending : message ∈ sent.network.pending := List.mem_append_right _
    (List.mem_singleton_self _)
  have emitted : message ∈ (app).outputs (sent.recall owner) := by
    simp [sent, ReactiveApplication.Execution.respond, MessageNetwork.submit,
      ReactiveApplication.outputs, message]
  have named : message.payload.packet.call = .opening event candidate value := by
    change (PhaseRuntimeState.emit (execution.application.submit owner material) owner
      (execution.network.known owner) material).packet.call = _
    rw [phase_emit_call, call]
  have addressed : message.payload.attempt = sent.application.attempt := rfl
  have sentUnsent : ¬ ∀ packet ∈ (app).outputs (sent.recall owner),
      PhaseCount.event? packet.payload ≠ some ⟨sent.application.attempt, event⟩ := by
    intro absent
    apply absent message emitted
    simp only [PhaseCount.event?, named, Payload.event?, Option.map_some, addressed]
  intro qualified
  change openingFrontierReceipt runtime leaks tape silent owner event at qualified
  change openingFrontierReceipt runtime leaks tape sent owner event
  unfold openingFrontierReceipt at qualified ⊢
  dsimp only at qualified ⊢
  obtain ⟨entered, stamp, later⟩ := qualified
  rw [ite_eq_left silentUnsent] at later
  have cursor : silent.environmentRecall.length = execution.environmentRecall.length :=
    congrArg List.length ((app).respond_environmentRecall execution owner ⟨none⟩)
  rw [cursor] at later
  obtain ⟨epoch, selected, bounded, timely⟩ := processing_epoch_of_unsent runtime leaks tape
    _ entered owner event later
  have activated : sent.application.current.native.activatedAt =
      execution.application.current.native.activatedAt := congrArg
    (fun view : PhasePublicView graph => view.native.activatedAt)
      (PhaseCount.submit_publicView execution.application owner material)
  refine ⟨entered, (congrFun activated event).trans stamp, ?_⟩
  rw [ite_eq_right sentUnsent]
  refine ⟨message, pending, candidate, value, rfl, named, addressed, epoch, ?_, bounded, timely⟩
  simpa only [sent, (app).respond_environmentRecall] using selected

end Vegas.EventGraphRuntime.ReservedEpoch
