/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourcePhaseBindingStep
import Vegas.Game.RevealService
import Vegas.Pending.PhaseCountedRequestResolution
import Vegas.Pending.PhaseBindingStampHistory

/-! # Accepting physical binding windows and original source steps

A timely first loss of a counted binding request identifies its real accepting
packet. Its immutable typed meaning gives the exact original source instruction,
including immediate close or retry, while the physical endpoint retains its
actual normalization. The paired source cursor is an input to this local step;
this result alone does not construct a complete source/runtime macro coupling.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The first timely loss of a counted binding request is its actual accepting
receipt. The same immutable typed result gives one legal original source step,
including immediate block close or retry, and extends the supplied source trace.
The physical endpoint retains the actual normalizer; no post-reset live-store
identification is assumed. -/
theorem sourcePhase_binding_first_loss_kernel
    (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime ((toEventGraph setup.program).withMode .sequential))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode .sequential)))
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode .sequential))
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (before : (phaseApplication runtime leaks).Control)
    (trace : ((phaseApplication runtime leaks).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some before))
    {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (tail : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard tail))
    (lift : ProtocolState (.commit name owner fresh guard tail) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (.commit name owner fresh guard tail) lift)
    (entry : SourceProgram.Config Player L Γ) (current : CommitRecoveryState setup.program)
    (sourceTrace : setup.commitRecoveryProtocol.Trace (some current))
    (point : current.point = lift (.inl entry))
    (excluded : current.excluded = before.execution.application.current.excluded)
    (message : Message Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode .sequential)))
    (allowed : ∀ packet ∈ before.execution.network.inputs, packet.sender = owner →
      PhaseCount.Permits before.execution.network.inputs packet)
    (input : message ∈ before.execution.network.inputs) (sender : message.sender = owner)
    (candidate : Handle ((toEventGraph setup.program).withMode .sequential))
    (call : message.payload.packet.call = .commitment
      (embedding.event ⟨0, by simp only [eventCount]; omega⟩) candidate)
    (requested : before.execution.application.SeedRequest owner
      ⟨message.payload.attempt, embedding.event ⟨0, by simp only [eventCount]; omega⟩⟩)
    (timely : before.execution.application.current.native.WithinDeadline runtime
      (embedding.event ⟨0, by simp only [eventCount]; omega⟩))
    (after : (phaseApplication runtime leaks).Execution)
    (command : (phaseApplication runtime leaks).Command)
    (moved : after ∈ (before.execution.environmentStep (phaseApplication runtime leaks)
      command).support)
    (lost : ¬ after.application.SeedRequest owner
      ⟨message.payload.attempt, embedding.event ⟨0, by simp only [eventCount]; omega⟩⟩) :
    let event := embedding.event ⟨0, by simp only [eventCount]; omega⟩
    let result := before.execution.application.current.native.bindingResult candidate payload
    let joint := current.commitJoint owner name payload result false
    command = .include message.id ∧
      before.execution.network.lookup message.id = some message ∧
      (message.id, true) ∈ after.receipts ∧
      ∃ native,
        EventGraphRuntime.handle runtime before.execution.application.current.native
          ⟨message.id, message.payload.packet.call⟩ = some native ∧
        native.accepted (.inr event) = some candidate ∧
        native.bindingResult candidate payload = result ∧
        after.application = ({ before.execution.application with
          current := before.execution.application.current.inclusionResult
            message.payload.packet.call native } :
              PhaseRuntimeState ((toEventGraph setup.program).withMode .sequential)).normalize ∧
        ∃ monotone : current.excluded ⊆ current.excluded,
          ∃ legal : setup.commitRecoveryProtocol.Legal (some current) joint,
            let next := ((current.install
              (lift (.inr (ProtocolState.entry tail (commitSuccessor name guard entry result))),
                current.excluded) monotone).close)
            setup.commitRecoveryProtocol.step (some current) ⟨joint, legal⟩ =
              PMF.pure (some next) ∧
            ∃ nextTrace : setup.commitRecoveryProtocol.Trace (some next),
              TracePrefix sourceTrace nextTrace := by
  intro event result joint
  have named : message.payload.packet.call.event?
      ((toEventGraph setup.program).withMode .sequential) = some event := by
    rw [call]
    rfl
  obtain ⟨commandEq, found, _handled, receipt, native, _ready, _action, accepted,
      _step, normalized⟩ := PhaseCount.timely_request_loss_accepts runtime leaks plan
    (serviceGraph_revealRelaxedOrdered setup .sequential) (setup.initialLaw.map encodeInputs)
    horizon scheduler before trace owner ⟨message.payload.attempt, event⟩ allowed requested timely
    message input sender rfl named after command moved lost
  have active : owner ∉ current.excluded := by
    rw [excluded]
    exact requested.2.2.2.2
  have nativeCall : EventGraphRuntime.handle runtime before.execution.application.current.native
      ⟨message.id, .commitment event candidate⟩ = some native := by
    simpa only [call] using accepted
  have table := (handle_commitment_tables runtime before.execution.application.current.native
    native message.id event candidate nativeCall).2.1
  have stored : native.accepted (.inr event) = some candidate := by
    rw [table, Function.update_self]
  have meaning : native.bindingResult candidate payload = result :=
    raw_handle_bindingResult runtime before.execution.application.current.native native _
      accepted candidate payload
  have sourceAccepted : native.accepted (.inr
      (embedding.event ⟨0, by simp only [eventCount]; omega⟩)) = some candidate := stored
  have sourceResult : ((native.accepted (.inr
      (embedding.event ⟨0, by simp only [eventCount]; omega⟩))).elim PublicationResult.failure
      (fun selected => native.bindingResult selected payload)) = result := by
    rw [sourceAccepted]
    exact meaning
  have sourceMissing : (native.accepted (.inr
      (embedding.event ⟨0, by simp only [eventCount]; omega⟩))).isNone = false := by
    rw [sourceAccepted]
    rfl
  have sourceKernel := sourcePhase_binding_receipt_kernel setup .sequential fresh guard tail
    embedding native lift origin entry current point
  dsimp only at sourceKernel
  rw [sourceResult, sourceMissing] at sourceKernel
  simp only [ite_eq_right active, excludeCommit, Bool.false_eq_true, ite_false] at sourceKernel
  obtain ⟨monotone, legal, kernel⟩ := sourceKernel
  refine ⟨commandEq, found, receipt, native, accepted, stored, meaning, normalized,
    monotone, legal, kernel, ?_⟩
  refine ⟨sourceTrace.extend joint legal ?_, ?_⟩
  · rw [kernel]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · exact .extend .refl _ _ _

end Vegas
