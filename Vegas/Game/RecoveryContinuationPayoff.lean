/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryExclusionPayoff
import Vegas.Pending.ExclusionContinuationLaw

/-! # Actual recovery payoff laws before the first-exclusion error

The comparison is with the concrete native profile and scheduler, without a
completion contract on that comparison runtime. The error is the actual
first-exclusion probability; bounding foreign exclusion further is separate.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
  Interaction EventGraphRuntime EventGraphRuntime.RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Under arbitrary raw behavioral play, the joint recovery base-payoff law is
within the actual exclusion probability of its concrete native continuation law. -/
theorem recovery_exclusionPayoffs_withinTV {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (initial : PMF (RecoveryState (graph setup)))
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨EventGraphRuntime.State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
    (horizon : Nat) (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)
    (profile : ∀ who, ((recoveryApplication (runtime setup) leaks).information initial horizon
      scheduler).BehavioralPolicy who)
    (nativeCertificate : ((application setup leaks).protocol (initial.map RecoveryState.native)
      horizon (nativeScheduler (runtime setup) leaks scheduler)).WellFoundedHistories)
    (recoveryCertificate : ((recoveryApplication (runtime setup) leaks).protocol initial horizon
      scheduler).WellFoundedHistories)
    (history : ((recoveryApplication (runtime setup) leaks).protocol initial horizon
      scheduler).History)
    (current : (recoveryApplication (runtime setup) leaks).Control)
    (state : history.state = some current) (empty : current.execution.application.excluded = ∅) :
    let nativeModel := (application setup leaks).information (initial.map RecoveryState.native)
      horizon (nativeScheduler (runtime setup) leaks scheduler)
    let recoveryModel := (recoveryApplication (runtime setup) leaks).information initial horizon
      scheduler
    let clear := fun next (same : history.state = some next) =>
      (Option.some.inj (state.symm.trans same)) ▸ empty
    let stopped := recoveryModel.runBehavioralUntil recoveryCertificate profile
      (fun history => ¬ RecoveryClear (runtime setup) leaks initial horizon scheduler history)
      history
    PMF.WithinTV (((stopped.map
      (recoveryStoppedReadout (runtime setup) leaks initial horizon scheduler)) none).toReal)
      ((recoveryModel.runBehavioralTerminalFrom recoveryCertificate profile history).map
        (fun final => recoveryExclusionBase parameter utility excludedPayoff final.state))
      ((nativeModel.runBehavioralTerminalFrom nativeCertificate
        (nativeProfile (runtime setup) leaks initial horizon scheduler profile)
        (nativeHistory (runtime setup) leaks initial horizon scheduler history clear)).map
          (fun final => exclusionBase setup parameter utility excludedPayoff leaks final.state)) :=
    by
  intro nativeModel recoveryModel clear stopped
  refine terminal_readout_withinTV_of_exclusion (runtime setup) leaks initial horizon scheduler
    initialized profile nativeCertificate recoveryCertificate
    (fun final => exclusionBase setup parameter utility excludedPayoff leaks final.state)
    (fun final => recoveryExclusionBase parameter utility excludedPayoff final.state)
    ?_ history current state empty
  intro stop clearStop
  funext who
  change recoveryExclusionBase parameter utility excludedPayoff stop.state who =
    exclusionBase setup parameter utility excludedPayoff leaks
      (protocolState (runtime setup) leaks stop.state) who
  cases stoppedState : stop.state with
  | none => rfl
  | some control =>
      exact recoveryExclusionBase_of_not_excluded parameter utility excludedPayoff control who
        (by simp [clearStop control stoppedState])

end Vegas
