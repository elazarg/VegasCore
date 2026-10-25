/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseComponents
import Vegas.Game.SequentialPhaseClearLift
import Vegas.Game.SequentialPhasePlayerInformation
import Vegas.Game.RecoveryNativeComparison

/-! # Recovery comparison weights for actual singleton phase mixtures

Represented clear inputs use the pure player-information decoder. Free choices
are relabeled by their local equivalence, and late pools retain the same local
key. Unrepresented recovery pools receive arbitrary valid weights.
-/

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
local notation "M" => model setup leaks bounds horizon scheduler
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "oldInitial" => recoveryInitialLaw setup
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "oldMenu" => Recovery.onePacketMenu (runtime setup) (oldLeaks) bounds
local notation "decode" => SequentialPhasePlayerInformation.information setup.program
  (runtime setup) leaks (oldLeaks)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq

/-- Clear played phase inputs are recovered from their old player input alone. -/
theorem decoded_projected_input (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1) :
    decode (PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks) agent.2.1) =
      agent.2.1 := by
  classical
  have played := agent.2.2
  unfold InformationModel.playedInformation at played
  obtain ⟨history, _member, seen⟩ := Finset.mem_image.mp played
  have observed := ((menu setup leaks bounds).info (initialLaw setup) horizon scheduler agent.1
    history.trace).symm.trans seen
  cases current : history.state with
  | none => rw [current] at observed; rw [← observed] at clear; exact clear.elim
  | some control =>
      by_cases acting : control.actor = some agent.1
      · have observation : (P).observe agent.1 (some control) = agent.2.1 := by
          rwa [current] at observed
        have empty : control.execution.application.current.excluded = ∅ := by
          have valid : ClearInput setup leaks ((P).observe agent.1 (some control)) :=
            observation.symm ▸ clear
          simp only [ReactiveApplication.observe, acting, ↓reduceIte] at valid
          exact valid
        have trace := (PhaseCount.normalized_onePacket_included (runtime setup) leaks bounds).trace
          (initialLaw setup) horizon scheduler (current ▸ history.trace)
        have recovered := SequentialPhasePlayerInformation.information_history setup.program
          (runtime setup) leaks (oldLeaks) bounds (setup.initialLaw.map setup.eventInputs) horizon
          scheduler trace empty agent.1
        rwa [observation] at recovered
      · rw [current] at observed
        simp only [ReactiveApplication.observe, acting, ↓reduceIte] at observed
        rw [← observed] at clear
        exact clear.elim

/-- Representation is a factual image condition on actual played clear inputs. -/
def Represented (agent : (R).InformationAgent (R).playedInformation) : Prop :=
  ∃ phase : (M).InformationAgent (M).playedInformation,
    ∃ clear : ClearInput setup leaks phase.2.1,
      projectedAgent setup leaks bounds horizon scheduler phase clear = agent

private theorem decoded_input_played (agent : (R).InformationAgent (R).playedInformation)
    (represented : Represented setup leaks bounds horizon scheduler agent) :
    decode agent.2.1 ∈ (M).playedInformation agent.1 := by
  obtain ⟨phase, clear, rfl⟩ := represented
  change decode (PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks) phase.2.1) ∈ _
  rw [decoded_projected_input setup leaks bounds horizon scheduler phase clear]
  exact phase.2.2

/-- The reverse agent's data are exactly the pure local decoder; witnesses
occur only in its membership proof. -/
def liftedAgent (agent : (R).InformationAgent (R).playedInformation)
    (represented : Represented setup leaks bounds horizon scheduler agent) :
    (M).InformationAgent (M).playedInformation :=
  ⟨agent.1, ⟨decode agent.2.1,
    decoded_input_played setup leaks bounds horizon scheduler agent represented⟩⟩

theorem lifted_projectedAgent (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1)
    (represented : Represented setup leaks bounds horizon scheduler
      (projectedAgent setup leaks bounds horizon scheduler agent clear)) :
    liftedAgent setup leaks bounds horizon scheduler
      (projectedAgent setup leaks bounds horizon scheduler agent clear) represented = agent := by
  have input := decoded_projected_input setup leaks bounds horizon scheduler agent clear
  cases agent with
  | mk who info =>
      apply congrArg (Sigma.mk who)
      apply Subtype.ext
      exact input

theorem liftedAgent_clear (agent : (R).InformationAgent (R).playedInformation)
    (represented : Represented setup leaks bounds horizon scheduler agent) :
    ClearInput setup leaks
      (liftedAgent setup leaks bounds horizon scheduler agent represented).2.1 := by
  obtain ⟨phase, clear, rfl⟩ := represented
  change ClearInput setup leaks (decode
    (PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks) phase.2.1))
  rwa [decoded_projected_input setup leaks bounds horizon scheduler phase clear]

theorem projected_liftedAgent (agent : (R).InformationAgent (R).playedInformation)
    (represented : Represented setup leaks bounds horizon scheduler agent) :
    projectedAgent setup leaks bounds horizon scheduler
        (liftedAgent setup leaks bounds horizon scheduler agent represented)
        (liftedAgent_clear setup leaks bounds horizon scheduler agent represented) = agent := by
  obtain ⟨phase, clear, rfl⟩ := represented
  have same := decoded_projected_input setup leaks bounds horizon scheduler phase clear
  cases phase with
  | mk who input =>
      apply congrArg (Sigma.mk who)
      apply Subtype.ext
      exact congrArg (PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks)) same

theorem freeAgent_projected_iff (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1) :
    RecoveryOnePacket.FreeAgent setup (oldLeaks) bounds (oldInitial) horizon (oldScheduler)
        (projectedAgent setup leaks bounds horizon scheduler agent clear) ↔
      FreeAgent setup leaks bounds horizon scheduler agent := by
  constructor
  · intro free ⟨otherClear, forced⟩
    exact free forced
  · intro free forced
    exact free ⟨clear, forced⟩

private theorem liftedAgent_free (agent : (R).InformationAgent (R).playedInformation)
    (represented : Represented setup leaks bounds horizon scheduler agent)
    (free : RecoveryOnePacket.FreeAgent setup (oldLeaks) bounds (oldInitial) horizon (oldScheduler)
      agent) :
    FreeAgent setup leaks bounds horizon scheduler
      (liftedAgent setup leaks bounds horizon scheduler agent represented) := by
  apply (freeAgent_projected_iff setup leaks bounds horizon scheduler _
    (liftedAgent_clear setup leaks bounds horizon scheduler agent represented)).mp
  rwa [projected_liftedAgent setup leaks bounds horizon scheduler agent represented]

/-- Local choice relabeling back to the supplied represented recovery agent. -/
def liftedChoiceEquiv (agent : (R).InformationAgent (R).playedInformation)
    (represented : Represented setup leaks bounds horizon scheduler agent) :
    (M).Choice agent.1
        (liftedAgent setup leaks bounds horizon scheduler agent represented).2.1 ≃
      (R).Choice agent.1 agent.2.1 :=
  (choiceEquiv setup leaks bounds horizon scheduler
    (liftedAgent setup leaks bounds horizon scheduler agent represented)
    (liftedAgent_clear setup leaks bounds horizon scheduler agent represented)).trans
      (Equiv.cast (congrArg (fun input => (R).Choice agent.1 input)
        (congrArg (fun other : (R).InformationAgent (R).playedInformation => other.2.1)
          (projected_liftedAgent setup leaks bounds horizon scheduler agent represented))))

open Classical in
/-- Extend actual phase weights to a global recovery comparison. Neither
post-exclusion equality nor optimality of these comparison weights is asserted. -/
def recoveryComparisonWeights {slots : Nat}
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p)) :
    ∀ p, PMF (RecoveryOnePacket.Part setup (oldLeaks) bounds (oldInitial) horizon (oldScheduler)
      slots p)
  | .inl owner =>
      if represented : Represented setup leaks bounds horizon scheduler owner.1 then
        (weights (.inl ⟨liftedAgent setup leaks bounds horizon scheduler owner.1 represented,
          liftedAgent_free setup leaks bounds horizon scheduler owner.1 represented owner.2⟩)).map
            (liftedChoiceEquiv setup leaks bounds horizon scheduler owner.1 represented)
      else PMF.pure (Classical.arbitrary _)
  | .inr none => PMF.pure ()
  | .inr (some key) =>
      if represented : key.1 ∈ Set.range
          (fun agent : {agent : (M).InformationAgent (M).playedInformation //
            ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
              (KeyedAgent setup leaks bounds horizon scheduler) agent} =>
            agentKey setup leaks bounds horizon scheduler agent.1) then
        weights (.inr (some ⟨key.1, represented⟩))
      else PMF.pure (Classical.arbitrary _)

end Vegas.SequentialPhase
