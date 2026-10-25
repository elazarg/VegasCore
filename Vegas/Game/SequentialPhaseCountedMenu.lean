/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseRecoveryLocalEnvelope

/-! # Canonical counted callbacks projected to the recovery game

The existing operational normalizer identifies canonical responses. At every
clear singleton phase prefix, any canonical admitted callback is a legal recovery one-packet
callback. No actual recovery trace or equilibrium is assumed.
-/

noncomputable section

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

/-- Exact canonical response admission on every actual clear counted prefix. -/
theorem recovery_onePacket_mem_of_normal_phase_history
    (inputs : PMF ((toEventGraph program).withMode .sequential).Inputs) (horizon : Nat)
    (scheduler : (P).Scheduler) {control : (P).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial (sequentialRuntimePhasePlan program)))
        horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) (who : Player)
    (response : (P).Action)
    (member : response ∈ PhaseCount.onePacketActions runtime leaks bounds who
      (control.execution.recall who) (control.execution.observe (P) who))
    (normal : (PhaseCount.normalization runtime leaks).action who
      (control.execution.recall who) (control.execution.observe (P) who) response = response) :
    action runtime leaks recoveryLeaks response ∈ Recovery.onePacketActions runtime recoveryLeaks
      bounds who ((control.execution.recall who).map (playerEntry runtime leaks recoveryLeaks))
      (playerView runtime leaks recoveryLeaks (control.execution.observe (P) who)) := by
  obtain ⟨raw, allowed⟩ := (PhaseCount.mem_onePacketActions runtime leaks bounds who
    (control.execution.recall who) (control.execution.observe (P) who) response).mp member
  apply (Recovery.mem_onePacketActions runtime recoveryLeaks bounds who _ _ _).mpr
  refine ⟨?_, ?_⟩
  · apply (normalizedMenu_projected runtime leaks recoveryLeaks bounds who
      (control.execution.recall who) (control.execution.observe (P) who) response).mp
    exact (ReactiveApplication.SubmissionNormalization.menu_mem _ _ _ _ _ _).mpr
      ⟨response, raw, normal⟩
  · rcases allowed with silent | ⟨material, transmitted, permitted⟩
    · exact Or.inl silent
    · exact Or.inr ⟨material, transmitted,
        recovery_countPermits_of_phase_history program runtime leaks bounds recoveryLeaks inputs
          horizon scheduler trace clear who material permitted⟩

end Vegas.EventGraphRuntime.PhaseRecoveryProjection
