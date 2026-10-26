/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseStoppedPayoffProjection

/-! # Actual phase history readouts for debt-stopped comparisons -/

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

/-- Focal physical exclusion is unchanged by projection of the current state. -/
theorem phaseExcluded_eq_projected (who : Player)
    (state : (phaseApplication runtime leaks).ProtocolState) :
    PhaseExcluded setup .sequential runtime leaks who state =
      RecoveryExcluded (runtime := runtime) (setup := setup) (leaks := recoveryLeaks) who
        (projection state) := by
  cases state <;> rfl

open Classical in
/-- On every actual initialized phase history, the original stopped payoff is
exactly the recovery payoff readout, with its existing debt/exit floor.
Coverage is derived from the actual raw phase trace rather than assumed. -/
theorem phaseDebtStoppedPayoff_history_eq_projected
    (plan : RuntimePhasePlan (graph setup)) (inputs : PMF (graph setup).Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (source : BehavioralProfile setup.program) (who : Player)
    (history : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).History) :
    phaseDebtStoppedPayoff setup runtime leaks parameter utility excludedPayoff source who
      history.state =
      if RecoveryPublicExclusion (runtime := runtime) (setup := setup) (leaks := recoveryLeaks)
          (projection history.state) ∨
          RecoveryDecodedState (runtime := runtime) (leaks := recoveryLeaks) source
            (ProtocolState.OwesFailure who setup.program) (projection history.state) then
        excludedPayoff who
      else recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff
        (projection history.state) who := by
  apply phaseDebtStoppedPayoff_eq_projected setup runtime leaks recoveryLeaks
  intro control current
  exact phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    (current ▸ menu.toRawTrace (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler
      history.trace)

/-- The exact foreign-exit error event is a physical readout, so stopped
pushforward laws transport its probability without a history bijection. -/
theorem phase_foreign_debt_exit_eq_projected
    (source : BehavioralProfile setup.program) (who : Player)
    (state : (phaseApplication runtime leaks).ProtocolState) :
    (PhaseDebtStopped setup runtime leaks source who state ∧
      ¬ PhaseExcluded setup .sequential runtime leaks who state ∧
      ¬ PhaseOwesFailure setup runtime leaks source who state) ↔
    ((RecoveryPublicExclusion (runtime := runtime) (setup := setup) (leaks := recoveryLeaks)
      (projection state) ∨
        RecoveryDecodedState (runtime := runtime) (leaks := recoveryLeaks) source
          (ProtocolState.OwesFailure who setup.program) (projection state)) ∧
      ¬ RecoveryExcluded (runtime := runtime) (setup := setup) (leaks := recoveryLeaks) who
        (projection state) ∧
      ¬ RecoveryDecodedState (runtime := runtime) (leaks := recoveryLeaks) source
        (ProtocolState.OwesFailure who setup.program) (projection state)) := by
  rw [phaseDebtStopped_eq_projected setup runtime leaks recoveryLeaks,
    phaseExcluded_eq_projected setup runtime leaks recoveryLeaks,
    phaseOwesFailure_eq_projected setup runtime leaks recoveryLeaks]

end Vegas
