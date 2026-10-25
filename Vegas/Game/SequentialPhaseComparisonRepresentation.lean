/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseComparisonWeights

/-! # Every active clear recovery input is represented in singleton phases -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler]

local notation "P" => phaseApplication (runtime setup) leaks
local notation "A" => recoveryApplication (runtime setup) (recoveryLeaks setup leaks)
local notation "M" => model setup leaks bounds horizon scheduler
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "oldInitial" => recoveryInitialLaw setup
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "oldMenu" => Recovery.onePacketMenu (runtime setup) (oldLeaks) bounds
local notation "projection" => PhaseRecoveryProjection.protocolState (runtime setup) leaks oldLeaks

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq

/-- The actual clear recovery prefix lifts under the original complete prior.
The inactive ghost input is excluded because it carries no player observation. -/
theorem represented_of_clear (agent : (R).InformationAgent (R).playedInformation)
    (clear : RecoveryProjection.ClearInput (runtime setup) (oldLeaks) agent.2.1)
    (activeInput : agent.2.1 ≠ none) :
    Represented setup leaks bounds horizon scheduler agent := by
  classical
  have played := agent.2.2
  unfold InformationModel.playedInformation at played
  obtain ⟨history, member, seen⟩ := Finset.mem_image.mp played
  have running := (Finset.mem_filter.mp member).2
  have observed := ((oldMenu).info (oldInitial) horizon (oldScheduler) agent.1
    history.trace).symm.trans seen
  cases oldAt : history.state with
  | none => rw [oldAt] at observed; exact (activeInput observed.symm).elim
  | some oldControl =>
      by_cases acting : oldControl.actor = some agent.1
      · have atControl : (A).observe agent.1 (some oldControl) = agent.2.1 := by
          rwa [oldAt] at observed
        have empty : oldControl.execution.application.excluded = ∅ := by
          have flags := congrArg (fun input : (A).Info =>
            input.map fun pair => pair.2.application.2) clear
          rw [← atControl] at flags
          simp only [ReactiveApplication.observe, acting, ↓reduceIte] at flags
          change some (∅ : Finset Player) = some oldControl.execution.application.excluded at flags
          exact (Option.some.inj flags).symm
        have priors : oldInitial = (Vegas.initialLaw setup).map
            (fun native => (⟨native, ∅⟩ : RecoveryState (graph setup))) := by
          simp only [recoveryInitialLaw, Vegas.initialLaw, serviceInitialLaw, PMF.map_comp,
            Function.comp_def]
        have oldTrace := Eq.mp (congrArg
          (fun prior : PMF (RecoveryState (graph setup)) =>
            ((oldMenu).protocol prior horizon (oldScheduler)).Trace (some oldControl)) priors)
          (oldAt ▸ history.trace)
        obtain ⟨phase, matched, _length⟩ := exists_canonical_phase_of_clear_recovery_trace setup
          leaks bounds horizon scheduler oldTrace empty
        have phaseRunning : ¬ (P).terminal phase.state := by
          have oldRunning : ¬ (A).terminal (some oldControl) := by
            change ¬ (A).terminal history.state at running
            rwa [oldAt] at running
          rw [← matched] at oldRunning
          cases phaseAt : phase.state with
          | none => rw [phaseAt] at oldRunning; exact oldRunning
          | some current => rw [phaseAt] at oldRunning; exact oldRunning
        have phasePlayed := (M).mem_playedInformation (who := agent.1) (history := phase)
          phaseRunning
        let phaseAgent : (M).InformationAgent (M).playedInformation :=
          ⟨agent.1, ⟨(M).infoOf agent.1 phase.trace, phasePlayed⟩⟩
        have phaseObserve : (M).infoOf agent.1 phase.trace = (P).observe agent.1 phase.state :=
          (menu setup leaks bounds).info (initialLaw setup) horizon scheduler agent.1 phase.trace
        have sameInput : PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks)
            phaseAgent.2.1 = agent.2.1 := by
          exact (congrArg (PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks))
            phaseObserve).trans ((PhaseRecoveryProjection.observe_state (runtime setup) leaks
              (oldLeaks) agent.1 phase.state).symm.trans
                ((congrArg ((A).observe agent.1) matched).trans atControl))
        have phaseClear : ClearInput setup leaks phaseAgent.2.1 := by
          change ClearInput setup leaks ((M).infoOf agent.1 phase.trace)
          rw [phaseObserve]
          cases phaseAt : phase.state with
          | none => rw [phaseAt] at matched; cases matched
          | some current =>
              rw [phaseAt] at matched
              have controls := Option.some.inj matched
              have actor : current.actor = some agent.1 :=
                (congrArg ReactiveApplication.Control.actor controls).trans acting
              simp only [ReactiveApplication.observe, actor, ↓reduceIte]
              have excluded := congrArg (fun control : (A).Control =>
                control.execution.application.excluded) controls
              exact excluded.trans empty
        refine ⟨phaseAgent, phaseClear, ?_⟩
        cases agent with
        | mk who info =>
            apply congrArg (Sigma.mk who)
            apply Subtype.ext
            exact sameInput
      · rw [oldAt] at observed
        simp only [ReactiveApplication.observe, acting, ↓reduceIte] at observed
        exact (activeInput observed.symm).elim

end Vegas.SequentialPhase
