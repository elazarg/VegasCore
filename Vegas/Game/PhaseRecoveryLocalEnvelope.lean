/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseRecoveryMenuProjection
import Vegas.Game.SequentialPhaseObservation
import Vegas.Game.PhaseClearPacketInformation
import Vegas.Pending.PhaseBindingCountTransport
import Vegas.Pending.PhaseSentMenu
import Vegas.Pending.PhaseStaticCountVerdict

/-! # Actual signed envelope agreement before singleton phase exclusion

The local response projection agrees exactly when the phase admits its event.
Actual singleton histories fix that event's static attempt address. These facts
compare emitted envelopes; count menus and equilibrium transport are separate.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRecoveryProjection

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (recoveryLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "P" => phaseApplication runtime leaks
local notation "R" => runtime.recoveryApplication recoveryLeaks

/-- Phase admission removes exactly the additional public token mask. -/
theorem localEnvelope_projected_of_allows (who : Player) (past : List (P).PlayerEntry)
    (view : (P).PlayerView) (material : WitnessedSubmission graph)
    (allowed : PhaseCount.allows view.application.2 material.call.packet = true) :
    PhaseCount.nativeMessage (PhaseCount.localEnvelope runtime leaks who past view material) =
      Recovery.localEnvelope runtime recoveryLeaks who
        (past.map (playerEntry runtime leaks recoveryLeaks))
        (playerView runtime leaks recoveryLeaks view) material := by
  unfold Recovery.localEnvelope EventGraphRuntime.localEnvelope
  rw [RecoveryProjection.submissionCount, RecoveryProjection.knownPackets,
    submissionCount, knownPackets]
  simp only [PhaseCount.localEnvelope, PhaseCount.nativeMessage,
    RecoveryProjection.playerView, playerView, PhaseCount.maskPacket, allowed, ↓reduceIte]
  rfl

variable {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)
  (sourceRuntime : EventGraphRuntime ((toEventGraph program).withMode .sequential))
  (sourceLeaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket ((toEventGraph program).withMode .sequential)))

local notation "S" => phaseApplication sourceRuntime sourceLeaks

variable [Fintype Player]
  (bounds : MessageBounds ((toEventGraph program).withMode .sequential))

/-- Every authorized callback has the unique static source-event attempt address. -/
theorem localEnvelope_static_history
    (inputs : PMF ((toEventGraph program).withMode .sequential).Inputs) (horizon : Nat)
    (scheduler : (S).Scheduler) {control : (S).Control}
    (trace : ((PhaseCount.onePacketMenu sourceRuntime sourceLeaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial (sequentialRuntimePhasePlan program)))
        horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) (who : Player)
    (material : WitnessedSubmission ((toEventGraph program).withMode .sequential))
    (authorized : (PhaseCount.localEnvelope sourceRuntime sourceLeaks who
      (control.execution.recall who) (control.execution.observe (S) who)
        material).payload.packet.tokenValid = true)
    (event : Fin (eventCount program))
    (named : (PhaseCount.localEnvelope sourceRuntime sourceLeaks who
      (control.execution.recall who) (control.execution.observe (S) who)
        material).payload.packet.call.event? _ = some event) :
    (PhaseCount.localEnvelope sourceRuntime sourceLeaks who (control.execution.recall who)
      (control.execution.observe (S) who) material).payload.attempt = ⟨event.val, 0⟩ := by
  let plan := sequentialRuntimePhasePlan program
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let rawTrace := (PhaseCount.onePacketMenu sourceRuntime sourceLeaks bounds).toRawTrace
    initial horizon scheduler trace
  obtain ⟨phase, installed, inside⟩ := PhaseCount.localEnvelope_phase sourceRuntime sourceLeaks
    control.execution who material event authorized named
  have suffix := phasePlanSuffix_history sourceRuntime sourceLeaks plan inputs horizon
    scheduler rawTrace
  have member : phase ∈ plan.phases := suffix.subset (List.mem_of_mem_head? installed)
  have same := (event_mem_sequentialRuntimePhasePlan program phase event).mp ⟨member, inside⟩
  have phaseEq : control.execution.application.attempt.phase = event.val := by
    simp only [PhaseRuntimeState.attempt, Option.mem_def.mp installed, Option.map_some,
      Option.getD_some, same]
    rfl
  have zero := (phaseClearMetadata_history sourceRuntime sourceLeaks plan inputs horizon scheduler
    rawTrace clear).1
  change control.execution.application.attempt = _
  exact congrArg₂ CommitAttemptId.mk phaseEq zero

/-- Every earlier actual counted input has its unique static source-event address. -/
theorem input_static_history
    (inputs : PMF ((toEventGraph program).withMode .sequential).Inputs) (horizon : Nat)
    (scheduler : (S).Scheduler) {control : (S).Control}
    (trace : ((PhaseCount.onePacketMenu sourceRuntime sourceLeaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial (sequentialRuntimePhasePlan program)))
        horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (message : Message Player (CommitAttemptPacket ((toEventGraph program).withMode .sequential)))
    (present : message ∈ control.execution.network.inputs)
    (event : Fin (eventCount program))
    (named : message.payload.packet.call.event? _ = some event) :
    message.payload.attempt = ⟨event.val, 0⟩ := by
  let plan := sequentialRuntimePhasePlan program
  obtain ⟨phase, member, actual, addressed, inside, phaseAddress⟩ :=
    PhaseCount.packetPhaseOrigins_history sourceRuntime sourceLeaks plan bounds inputs horizon
      scheduler trace message present
  have sameEvent : actual = event := Option.some.inj (addressed.symm.trans named)
  subst actual
  have samePhase := (event_mem_sequentialRuntimePhasePlan program phase event).mp ⟨member, inside⟩
  have phaseEq : message.payload.attempt.phase = event.val := by
    rw [samePhase] at phaseAddress
    exact phaseAddress
  have restamp := PhaseCount.clear_input_restamp_history sourceRuntime sourceLeaks plan bounds
    inputs horizon scheduler trace clear message present
  have generationEq := congrArg (fun packet => packet.attempt.generation) restamp
  exact congrArg₂ CommitAttemptId.mk phaseEq generationEq.symm

variable (sourceRecoveryLeaks : MessageNetwork.ObservationRule Player
  (WitnessedPacket ((toEventGraph program).withMode .sequential)))

/-- Actual phase count admission implies original recovery count admission.
This direction needs neither a guessed inverse history nor a native equilibrium. -/
theorem recovery_countPermits_of_phase_history
    (inputs : PMF ((toEventGraph program).withMode .sequential).Inputs) (horizon : Nat)
    (scheduler : (S).Scheduler) {control : (S).Control}
    (trace : ((PhaseCount.onePacketMenu sourceRuntime sourceLeaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial (sequentialRuntimePhasePlan program)))
        horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) (who : Player)
    (material : WitnessedSubmission ((toEventGraph program).withMode .sequential))
    (permitted : PhaseCount.permits ((S).outputs (control.execution.recall who))
      (PhaseCount.localEnvelope sourceRuntime sourceLeaks who (control.execution.recall who)
        (control.execution.observe (S) who) material) = true) :
    countPermits ((sourceRuntime.recoveryApplication sourceRecoveryLeaks).outputs
        ((control.execution.recall who).map
          (playerEntry sourceRuntime sourceLeaks sourceRecoveryLeaks)))
      (Recovery.localEnvelope sourceRuntime sourceRecoveryLeaks who
        ((control.execution.recall who).map
          (playerEntry sourceRuntime sourceLeaks sourceRecoveryLeaks))
        (playerView sourceRuntime sourceLeaks sourceRecoveryLeaks
          (control.execution.observe (S) who)) material) = true := by
  let plan := sequentialRuntimePhasePlan program
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let rawTrace := (PhaseCount.onePacketMenu sourceRuntime sourceLeaks bounds).toRawTrace
    initial horizon scheduler trace
  have recalled := (S).history_inputRecall initial horizon scheduler rawTrace
  have admitted := (PhaseCount.permits_eq_true_iff _ _).mp permitted
  have static : ∀ other ∈ (S).outputs (control.execution.recall who), ∀ event,
      other.payload.packet.call.event? _ = some event →
        other.payload.attempt = (⟨event.val, 0⟩ : CommitAttemptId) := by
    intro other output event named
    rw [← recalled who] at output
    exact input_static_history program sourceRuntime sourceLeaks bounds inputs horizon scheduler
      trace clear other (List.mem_filter.mp output).1 event named
  have tag := localEnvelope_static_history program sourceRuntime sourceLeaks bounds inputs
    horizon scheduler trace clear who material admitted.1
  have native := PhaseCount.countPermits_of_permits_of_static
    (fun event => ⟨event.val, 0⟩) _ _ static tag admitted
  have allowed := (PhaseBindingRepair.localEnvelope_admitted sourceRuntime sourceLeaks
    control.execution who material admitted.1).1
  rw [← PhaseCount.allows_publicView] at allowed
  rw [← localEnvelope_projected_of_allows sourceRuntime sourceLeaks sourceRecoveryLeaks who
    (control.execution.recall who) (control.execution.observe (S) who) material allowed, outputs]
  exact (countPermits_eq_true_iff _ _).mpr native

end Vegas.EventGraphRuntime.PhaseRecoveryProjection
