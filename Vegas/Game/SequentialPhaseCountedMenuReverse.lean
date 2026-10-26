/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseCountedMenu
import Vegas.Game.OnePacketClearCountedResponse
import Vegas.Pending.ExclusionMenuProjection

/-! # Reverse counted callbacks at paired actual clear prefixes

The native prefix is an actual source-game history. Equality of its current
state and the deciding player's full input with the phase projection supplies
pointwise induction data, rather than a final-law or equilibrium certificate.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

private theorem countClean_outputs (execution : (phaseApplication runtime leaks).Execution)
    (clean : CountClean runtime leaks execution) (who : Player) :
    ∀ other ∈ (phaseApplication runtime leaks).outputs (execution.recall who),
      Permits ((phaseApplication runtime leaks).outputs (execution.recall who)) other := by
  intro other output
  have own : other ∈ execution.network.inputs.filter (fun message => message.sender = who) := by
    rwa [clean.1.1 who]
  obtain ⟨present, sender⟩ := List.mem_filter.mp own
  have senderEq : other.sender = who := of_decide_eq_true sender
  apply (permits_eq_true_iff _ _).mp
  rw [permits_congr _ _ _ ?_]
  · exact clean.2 other present
  · intro prior
    constructor
    · rintro ⟨before, same, lower⟩
      rw [← clean.1.1 who] at before
      exact ⟨(List.mem_filter.mp before).1, same, lower⟩
    · rintro ⟨before, same, lower⟩
      refine ⟨?_, same, lower⟩
      rw [← clean.1.1 who]
      exact List.mem_filter.mpr ⟨before, by simp only [same, senderEq, decide_true]⟩

end Vegas.EventGraphRuntime.PhaseCount

namespace Vegas.EventGraphRuntime.PhaseRecoveryProjection

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)
  (runtime : EventGraphRuntime ((toEventGraph program).withMode .sequential))
  (leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket ((toEventGraph program).withMode .sequential)))
  (recoveryLeaks : MessageNetwork.ObservationRule Player
    (WitnessedPacket ((toEventGraph program).withMode .sequential)))
  (bounds : MessageBounds ((toEventGraph program).withMode .sequential))

local notation "P" => phaseApplication runtime leaks
local notation "R" => runtime.recoveryApplication recoveryLeaks

/-- At actual clear callbacks, phase admission is the only additional count guard. -/
theorem phase_countPermits_of_recovery_history
    (inputs : PMF ((toEventGraph program).withMode .sequential).Inputs) (horizon : Nat)
    (scheduler : (P).Scheduler) {control : (P).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial (sequentialRuntimePhasePlan program)))
        horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) (who : Player)
    (material : WitnessedSubmission ((toEventGraph program).withMode .sequential))
    (allowed : PhaseCount.allows control.execution.application.publicView
      material.call.packet = true)
    (permitted : countPermits ((R).outputs ((control.execution.recall who).map
      (playerEntry runtime leaks recoveryLeaks)))
      (Recovery.localEnvelope runtime recoveryLeaks who
        ((control.execution.recall who).map (playerEntry runtime leaks recoveryLeaks))
        (playerView runtime leaks recoveryLeaks (control.execution.observe (P) who)) material) =
          true) :
    PhaseCount.permits ((P).outputs (control.execution.recall who))
      (PhaseCount.localEnvelope runtime leaks who (control.execution.recall who)
        (control.execution.observe (P) who) material) = true := by
  let plan := sequentialRuntimePhasePlan program
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon
    scheduler trace
  have recalled := (P).history_inputRecall initial horizon scheduler rawTrace
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have envelope := localEnvelope_projected_of_allows runtime leaks recoveryLeaks who
    (control.execution.recall who) (control.execution.observe (P) who) material allowed
  rw [← envelope, outputs] at permitted
  have authorized := ((countPermits_eq_true_iff _ _).mp permitted).1
  have static : ∀ other ∈ (P).outputs (control.execution.recall who), ∀ event,
      other.payload.packet.call.event? _ = some event →
        other.payload.attempt = (⟨event.val, 0⟩ : CommitAttemptId) := by
    intro other output event named
    rw [← recalled who] at output
    exact input_static_history program runtime leaks bounds inputs horizon scheduler trace clear
      other (List.mem_filter.mp output).1 event named
  have tag := localEnvelope_static_history program runtime leaks bounds inputs horizon scheduler
    trace clear who material authorized
  rw [PhaseCount.permits_eq_countPermits_of_static (fun event => ⟨event.val, 0⟩) _ _
    static tag (PhaseCount.countClean_outputs runtime leaks control.execution clean who)]
  exact permitted

end Vegas.EventGraphRuntime.PhaseRecoveryProjection

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (recoveryLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup))

local notation "P" => phaseApplication runtime leaks
local notation "R" => recoveryApplication runtime recoveryLeaks
local notation "N" => application (runtime := runtime) setup recoveryLeaks

/-- A permitted recovery callback at paired actual clear prefixes belongs to the installed phase. -/
theorem phase_allows_of_recovery_countPermits_paired_history
    (inputs : PMF (graph setup).Inputs) (horizon : Nat)
    (scheduler : (P).Scheduler) {control : (P).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial (sequentialRuntimePhasePlan setup.program)))
        horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (nativeScheduler : (N).Scheduler) (nativeControl : (N).Control)
    (nativeTrace : (onePacketProtocol (runtime := runtime) setup recoveryLeaks bounds horizon
      nativeScheduler).Trace
      (some nativeControl))
    (nativeClear : ExclusionEvidence 0 ∅
      (⟨nativeControl.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (current : control.execution.application.current.native = nativeControl.execution.application)
    (who : Player)
    (past : ((control.execution.recall who).map
      (PhaseRecoveryProjection.playerEntry runtime leaks recoveryLeaks)).map
        (RecoveryProjection.playerEntry runtime recoveryLeaks) =
          nativeControl.execution.recall who)
    (view : RecoveryProjection.playerView runtime recoveryLeaks
      (PhaseRecoveryProjection.playerView runtime leaks recoveryLeaks
        (control.execution.observe (P) who)) = nativeControl.execution.observe (N) who)
    (material : WitnessedSubmission (graph setup))
    (permitted : countPermits ((R).outputs ((control.execution.recall who).map
      (PhaseRecoveryProjection.playerEntry runtime leaks recoveryLeaks)))
      (Recovery.localEnvelope runtime recoveryLeaks who
        ((control.execution.recall who).map
          (PhaseRecoveryProjection.playerEntry runtime leaks recoveryLeaks))
        (PhaseRecoveryProjection.playerView runtime leaks recoveryLeaks
          (control.execution.observe (P) who)) material) = true) :
    PhaseCount.allows control.execution.application.publicView material.call.packet = true := by
  have empty : (PhaseRecoveryProjection.playerView runtime leaks recoveryLeaks
      (control.execution.observe (P) who)).application.2 = ∅ := clear
  rw [Recovery.localEnvelope_of_empty runtime recoveryLeaks who _ _ empty,
    ← RecoveryProjection.outputs, past, view] at permitted
  have authorized := ((countPermits_eq_true_iff _ _).mp permitted).1
  obtain ⟨event, named, _token⟩ := (WitnessedPacket.tokenValid_iff _).mp authorized
  have addressed : material.call.packet.event? (graph setup) = some event := named
  have ready := countPermits_localEnvelope_ready_of_clear_trace (runtime := runtime) nativeTrace
    nativeClear who
    material permitted event addressed
  rw [← current] at ready
  let plan := sequentialRuntimePhasePlan setup.program
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial
    horizon scheduler trace
  have frontier := (phaseApplication_frontier runtime leaks).history initial horizon
    scheduler (fun state supported => by
      obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_frontier plan draw) rawTrace
  have live := ((phaseApplication_live runtime leaks).history initial horizon scheduler
    (fun state supported => by
      obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨PhaseRuntimeState.initial_frontier plan draw,
        PhaseRuntimeState.initial_live plan draw⟩) rawTrace).2
  rw [PhaseCount.allows_publicView]
  cases phases : control.execution.application.phases with
  | nil =>
      exact (ready.1 (by rw [frontier.terminal phases]; exact Finset.mem_univ _)).elim
  | cons phase remaining =>
      have head : control.execution.application.phases.head? = some phase := by rw [phases]; rfl
      have positioned := frontier.positioned
      rw [phases] at positioned
      have inside := phase.ready_mem_sequential control.execution.application.current positioned.2
        (live phase (by rw [head]; rfl)) event ready
      simp only [PhaseRuntimeState.allows, head, addressed]
      exact decide_eq_true inside

/-- At paired actual clear prefixes every recovery canonical callback is admitted by the phase menu.
The conclusion also derives its operational normal form, rather than assuming it. -/
theorem phase_onePacket_mem_of_recovery_paired_history
    (inputs : PMF (graph setup).Inputs) (horizon : Nat)
    (scheduler : (P).Scheduler) {control : (P).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial (sequentialRuntimePhasePlan setup.program)))
        horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (nativeScheduler : (N).Scheduler) (nativeControl : (N).Control)
    (nativeTrace : (onePacketProtocol (runtime := runtime) setup recoveryLeaks bounds horizon
      nativeScheduler).Trace
      (some nativeControl))
    (nativeClear : ExclusionEvidence 0 ∅
      (⟨nativeControl.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (current : control.execution.application.current.native = nativeControl.execution.application)
    (who : Player)
    (past : ((control.execution.recall who).map
      (PhaseRecoveryProjection.playerEntry runtime leaks recoveryLeaks)).map
        (RecoveryProjection.playerEntry runtime recoveryLeaks) =
          nativeControl.execution.recall who)
    (view : RecoveryProjection.playerView runtime recoveryLeaks
      (PhaseRecoveryProjection.playerView runtime leaks recoveryLeaks
        (control.execution.observe (P) who)) = nativeControl.execution.observe (N) who)
    (response : (P).Action)
    (member : PhaseRecoveryProjection.action runtime leaks recoveryLeaks response ∈
      Recovery.onePacketActions runtime recoveryLeaks bounds who
        ((control.execution.recall who).map
          (PhaseRecoveryProjection.playerEntry runtime leaks recoveryLeaks))
        (PhaseRecoveryProjection.playerView runtime leaks recoveryLeaks
          (control.execution.observe (P) who))) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who
        (control.execution.recall who) (control.execution.observe (P) who) ∧
      (PhaseCount.normalization runtime leaks).action who (control.execution.recall who)
        (control.execution.observe (P) who) response = response := by
  obtain ⟨recoveryMenu, permitted⟩ := (Recovery.mem_onePacketActions runtime recoveryLeaks
      bounds
    who _ _ _).mp member
  have canonical := (PhaseRecoveryProjection.normalizedMenu_projected runtime leaks
    recoveryLeaks bounds who (control.execution.recall who) (control.execution.observe (P) who)
      response).mpr recoveryMenu
  have fixed := (PhaseCount.normalization runtime leaks).menu_normal
    (PhaseCount.rawMenu runtime leaks bounds) who (control.execution.recall who)
    (control.execution.observe (P) who) response canonical
  refine ⟨(PhaseCount.mem_onePacketActions runtime leaks bounds who _ _ _).mpr
    ⟨?_, ?_⟩, fixed⟩
  · obtain ⟨original, raw, normalized⟩ :=
      (ReactiveApplication.SubmissionNormalization.menu_mem _ _ _ _ _ _).mp canonical
    have projectedRaw := (PhaseRecoveryProjection.rawMenu_projected runtime leaks
      recoveryLeaks bounds who (control.execution.recall who) (control.execution.observe (P) who)
        original).mp raw
    have normalizedRaw := Recovery.rawMenu_closed runtime recoveryLeaks bounds who _ _ _
      projectedRaw
    rw [← PhaseRecoveryProjection.normalization_projected, normalized] at normalizedRaw
    exact (PhaseRecoveryProjection.rawMenu_projected runtime leaks recoveryLeaks bounds
      who (control.execution.recall who) (control.execution.observe (P) who) response).mpr
        normalizedRaw
  · rcases permitted with silent | ⟨material, transmitted, admitted⟩
    · exact Or.inl silent
    · refine Or.inr ⟨material, transmitted, ?_⟩
      have allowed := phase_allows_of_recovery_countPermits_paired_history setup runtime leaks
        recoveryLeaks
        bounds inputs horizon scheduler trace clear nativeScheduler nativeControl nativeTrace
        nativeClear current who past view material admitted
      exact PhaseRecoveryProjection.phase_countPermits_of_recovery_history setup.program
        runtime leaks recoveryLeaks bounds inputs horizon scheduler trace clear who
        material allowed admitted

end Vegas
