/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseStoppedPayoff
import Vegas.Game.SequentialPhaseTransition

/-! # Physical readouts for phase debt-stopped utility -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (recoveryLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

local notation "projection" =>
  PhaseRecoveryProjection.protocolState runtime leaks recoveryLeaks

/-- Source debt depends only on the full physical current state. -/
theorem phaseOwesFailure_eq_projected
    (source : BehavioralProfile setup.program) (who : Player)
    (state : (phaseApplication runtime leaks).ProtocolState) :
    PhaseOwesFailure setup runtime leaks source who state =
      RecoveryDecodedState (runtime := runtime) (leaks := recoveryLeaks) source
        (ProtocolState.OwesFailure who setup.program) (projection state) := by
  cases state <;> rfl

/-- The stop is exactly public physical exclusion or focal source debt. -/
theorem phaseDebtStopped_eq_projected
    (source : BehavioralProfile setup.program) (who : Player)
    (state : (phaseApplication runtime leaks).ProtocolState) :
    PhaseDebtStopped setup runtime leaks source who state ↔
      RecoveryPublicExclusion (runtime := runtime) (setup := setup) (leaks := recoveryLeaks)
        (projection state) ∨
        RecoveryDecodedState (runtime := runtime) (leaks := recoveryLeaks) source
          (ProtocolState.OwesFailure who setup.program) (projection state) := by
  cases state <;>
    simp only [PhaseDebtStopped, PhaseOwesFailure, ReactiveApplication.stateInvariant,
      PhaseRecoveryProjection.protocolState, Option.map_none, Option.map_some,
      RecoveryPublicExclusion, RecoveryDecodedState,
        not_true_eq_false, false_or]
  rfl

open Classical in
/-- The original stopped payoff is a physical state readout on every genuinely
covered phase endpoint; only the existing exclusion/debt floor is used. -/
theorem phaseDebtStoppedPayoff_eq_projected {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (source : BehavioralProfile setup.program) (who : Player)
    (state : (phaseApplication runtime leaks).ProtocolState)
    (coverage : ∀ control, state = some control → control.execution.application.FailureCoverage) :
    phaseDebtStoppedPayoff setup runtime leaks parameter utility excludedPayoff source who state =
      if RecoveryPublicExclusion (runtime := runtime) (setup := setup) (leaks := recoveryLeaks)
        (projection state) ∨
          RecoveryDecodedState (runtime := runtime) (leaks := recoveryLeaks) source
            (ProtocolState.OwesFailure who setup.program) (projection state) then
        excludedPayoff who
      else recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff (projection
        state) who := by
  simp only [phaseDebtStoppedPayoff,
    phaseDebtStopped_eq_projected setup runtime leaks recoveryLeaks]
  split_ifs
  · rfl
  · cases state with
    | none => rfl
    | some control =>
      exact phaseExclusionBase_eq_recoveryExclusionBase (runtime := runtime) setup leaks
        recoveryLeaks parameter
        utility excludedPayoff control (coverage control rfl) who

end Vegas
