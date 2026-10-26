/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseComparisonWeights
import Vegas.Game.OnePacketSlotLawDischarge

/-! # Exact recovery comparison mixtures at clear phase inputs -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  [(phaseApplication runtime leaks).FiniteNature (phaseInitialLaw setup) scheduler]

local notation "M" => model setup runtime leaks bounds horizon scheduler
local notation "R" => recoveryModel setup runtime leaks bounds horizon scheduler
local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "RecoveryPrior" => recoveryInitialLaw setup
local notation "RecoveryScheduler" => recoveryScheduler setup runtime leaks scheduler
local notation "RecoveryMenu" => Recovery.onePacketMenu runtime (RecoveryLeaks) bounds
local notation "project" => fun choice => Option.map
  (PhaseRecoveryProjection.action runtime leaks (RecoveryLeaks)) (Subtype.val choice)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

omit [(phaseApplication runtime leaks).FiniteNature (phaseInitialLaw setup) scheduler] in
private theorem choice_cast_val {who : Player} {first second : (R).InfoState who}
    (same : first = second) (choice : (R).Choice who first) :
    (Equiv.cast (congrArg (fun input => (R).Choice who input) same) choice).1 = choice.1 := by
  subst second
  rfl

theorem liftedChoiceEquiv_val (agent : (R).InformationAgent (R).playedInformation)
    (represented : Represented setup runtime leaks bounds horizon scheduler agent)
    (choice : (M).Choice agent.1
      (liftedAgent setup runtime leaks bounds horizon scheduler agent represented).2.1) :
    (liftedChoiceEquiv setup runtime leaks bounds horizon scheduler agent represented choice).1 =
      project choice := by
  unfold liftedChoiceEquiv
  simp only [Equiv.trans_apply]
  have same : PhaseRecoveryProjection.information runtime leaks (RecoveryLeaks)
      (liftedAgent setup runtime leaks bounds horizon scheduler agent represented).2.1 = agent.2.1
        :=
    congrArg (fun other : (R).InformationAgent (R).playedInformation => other.2.1)
      (projected_liftedAgent setup runtime leaks bounds horizon scheduler agent represented)
  exact choice_cast_val setup runtime leaks bounds horizon scheduler (who := agent.1)
    (first := PhaseRecoveryProjection.information runtime leaks (RecoveryLeaks)
      (liftedAgent setup runtime leaks bounds horizon scheduler agent represented).2.1)
    (second := agent.2.1) same _

theorem uniform_phase_map (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup runtime leaks agent.2.1) :
    (((menu setup runtime leaks bounds).uniformPolicy (phaseInitialLaw setup) horizon scheduler
      agent.1
        agent.2.1).map (choiceEquiv setup runtime leaks bounds horizon scheduler agent clear)) =
      (RecoveryMenu).uniformPolicy (RecoveryPrior) horizon (RecoveryScheduler) agent.1
        (projectedAgent setup runtime leaks bounds horizon scheduler agent clear).2.1 := by
  rw [← uniform_recovery_map setup runtime leaks bounds horizon scheduler agent clear, PMF.map_comp]
  simp only [Function.comp_def, Equiv.apply_symm_apply]
  exact PMF.map_id _

theorem prescribedComponent_recovery (assessment : setup.intendedModel.BehavioralAssessment)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup runtime leaks agent.2.1) :
    (prescribedComponent setup runtime leaks bounds horizon scheduler assessment scale nonnegative
      le_one
        agent).map project =
      (RecoveryOnePacket.prescribedComponent (runtime := runtime) setup (RecoveryLeaks) bounds
        (RecoveryPrior) horizon
        (RecoveryScheduler) assessment scale nonnegative le_one
        (projectedAgent setup runtime leaks bounds horizon scheduler agent clear)).map Subtype.val
          := by
  unfold prescribedComponent
  rw [dite_eq_left clear, PMF.map_comp]
  congr 1
  funext choice
  exact congrArg Subtype.val
    ((choiceEquiv setup runtime leaks bounds horizon scheduler agent clear).apply_symm_apply choice)

theorem keyedComponent_recovery (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup runtime leaks agent.2.1) (option : LateOption slots) :
    (keyedComponent setup runtime leaks bounds horizon scheduler assessment scale nonnegative le_one
        agent option).map project =
      (RecoveryOnePacket.keyedComponent (runtime := runtime) setup (RecoveryLeaks) bounds
        (RecoveryPrior) horizon
        (RecoveryScheduler) assessment scale nonnegative le_one
        (projectedAgent setup runtime leaks bounds horizon scheduler agent clear) option).map
          Subtype.val := by
  unfold keyedComponent
  rw [dite_eq_left clear, PMF.map_comp]
  congr 1
  funext choice
  exact congrArg Subtype.val
    ((choiceEquiv setup runtime leaks bounds horizon scheduler agent clear).apply_symm_apply choice)

theorem recoveryComparisonWeights_free {slots : Nat}
    (weights : ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots p))
    (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup runtime leaks agent.2.1)
    (free : FreeAgent setup runtime leaks bounds horizon scheduler agent) :
    (recoveryComparisonWeights setup runtime leaks bounds horizon scheduler weights
        (.inl ⟨projectedAgent setup runtime leaks bounds horizon scheduler agent clear,
          (freeAgent_projected_iff setup runtime leaks bounds horizon scheduler agent clear).mpr
            free⟩)).map
            Subtype.val =
      (weights (.inl ⟨agent, free⟩)).map project := by
  classical
  have represented : Represented setup runtime leaks bounds horizon scheduler
      (projectedAgent setup runtime leaks bounds horizon scheduler agent clear) := ⟨agent, clear,
        rfl⟩
  simp only [recoveryComparisonWeights, dite_eq_left represented, PMF.map_comp]
  have same := lifted_projectedAgent setup runtime leaks bounds horizon scheduler agent clear
    represented
  have owner :
      (⟨liftedAgent setup runtime leaks bounds horizon scheduler
          (projectedAgent setup runtime leaks bounds horizon scheduler agent clear) represented,
        same.symm ▸ free⟩ : {agent : (M).InformationAgent (M).playedInformation //
          FreeAgent setup runtime leaks bounds horizon scheduler agent}) = ⟨agent, free⟩ :=
    Subtype.ext same
  have erased := congrArg
    (fun owner : {agent : (M).InformationAgent (M).playedInformation //
        FreeAgent setup runtime leaks bounds horizon scheduler agent} =>
      (weights (.inl owner)).map project) owner
  refine Eq.trans ?_ erased
  congr 1
  funext choice
  exact liftedChoiceEquiv_val setup runtime leaks bounds horizon scheduler _ represented choice

/-- Every actual clear phase component mixture has exactly the recovery
comparison's optional-response law. No equality after exclusion is used. -/
theorem recoveryComparisonMixture_at_clear
    (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots p))
    (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup runtime leaks agent.2.1) :
    ((recoveryComparisonWeights setup runtime leaks bounds horizon scheduler weights
        (RecoveryOnePacket.pool (runtime := runtime) setup (RecoveryLeaks) bounds (RecoveryPrior)
          horizon
            (RecoveryScheduler)
          (projectedAgent setup runtime leaks bounds horizon scheduler agent clear))).bind
      (RecoveryOnePacket.component (runtime := runtime) setup (RecoveryLeaks) bounds
        (RecoveryPrior) horizon
          (RecoveryScheduler)
        assessment scale nonnegative le_one
        (projectedAgent setup runtime leaks bounds horizon scheduler agent clear))).map
          Subtype.val =
      ((weights (pool setup runtime leaks bounds horizon scheduler agent)).bind
        (component setup runtime leaks bounds horizon scheduler assessment scale nonnegative le_one
          agent)).map project := by
  classical
  let recoveryAgent := projectedAgent setup runtime leaks bounds horizon scheduler agent clear
  let recoveryWeights := recoveryComparisonWeights setup runtime leaks bounds horizon scheduler
    weights
  let phaseFree := freeLaw setup runtime leaks bounds horizon scheduler scale nonnegative le_one
  let phasePrescribed := prescribedComponent setup runtime leaks bounds horizon scheduler
    assessment scale
    nonnegative le_one
  let phaseKeyed := keyedComponent setup runtime leaks bounds horizon scheduler assessment scale
    nonnegative le_one (slots := slots)
  let recoveryFree := RecoveryOnePacket.freeLaw setup runtime (RecoveryLeaks) bounds
    (RecoveryPrior) horizon
    (RecoveryScheduler) scale nonnegative le_one
  let recoveryPrescribed := RecoveryOnePacket.prescribedComponent (runtime := runtime) setup
    (RecoveryLeaks) bounds
      (RecoveryPrior)
    horizon (RecoveryScheduler) assessment scale nonnegative le_one
  let recoveryKeyed := RecoveryOnePacket.keyedComponent (runtime := runtime) setup (RecoveryLeaks)
    bounds (RecoveryPrior)
      horizon
    (RecoveryScheduler) assessment scale nonnegative le_one (slots := slots)
  have freeIff := freeAgent_projected_iff setup runtime leaks bounds horizon scheduler agent clear
  by_cases free : FreeAgent setup runtime leaks bounds horizon scheduler agent
  · have recoveryIsFree := freeIff.mpr free
    have phaseMix : (weights (pool setup runtime leaks bounds horizon scheduler agent)).bind
        (component setup runtime leaks bounds horizon scheduler assessment scale nonnegative
          le_one agent) =
        (weights (.inl ⟨agent, free⟩)).bind (phaseFree agent) := by
      change (weights (freeKeyedPool _ _ _ agent)).bind
        (freeKeyedComponent phaseFree phasePrescribed phaseKeyed agent) = _
      unfold freeKeyedComponent
      rw [freeKeyedPool_of_free free]
      congr 1
      funext choice
      exact dite_eq_left rfl
    have recoveryMixture : (recoveryWeights (RecoveryOnePacket.pool (runtime := runtime) setup
      (RecoveryLeaks) bounds
        (RecoveryPrior) horizon
          (RecoveryScheduler) recoveryAgent)).bind
        (RecoveryOnePacket.component (runtime := runtime) setup (RecoveryLeaks) bounds
          (RecoveryPrior) horizon
            (RecoveryScheduler)
          assessment scale nonnegative le_one recoveryAgent) =
        (recoveryWeights (.inl ⟨recoveryAgent, recoveryIsFree⟩)).bind (recoveryFree recoveryAgent)
            := by
      change (recoveryWeights (freeKeyedPool _ _ _ recoveryAgent)).bind
        (freeKeyedComponent recoveryFree recoveryPrescribed recoveryKeyed recoveryAgent) = _
      unfold freeKeyedComponent
      rw [freeKeyedPool_of_free recoveryIsFree]
      congr 1
      funext choice
      exact dite_eq_left rfl
    change ((recoveryWeights (RecoveryOnePacket.pool (runtime := runtime) setup (RecoveryLeaks)
      bounds (RecoveryPrior)
        horizon
      (RecoveryScheduler) recoveryAgent)).bind
        (RecoveryOnePacket.component (runtime := runtime) setup (RecoveryLeaks) bounds
          (RecoveryPrior) horizon
            (RecoveryScheduler)
          assessment scale nonnegative le_one recoveryAgent)).map Subtype.val = _
    rw [recoveryMixture, phaseMix]
    change ((recoveryWeights (.inl ⟨recoveryAgent, recoveryIsFree⟩)).bind (fun choice =>
      mix scale nonnegative le_one
        ((RecoveryMenu).uniformPolicy (RecoveryPrior) horizon (RecoveryScheduler) recoveryAgent.1
            recoveryAgent.2.1)
        (PMF.pure choice))).map Subtype.val =
      ((weights (.inl ⟨agent, free⟩)).bind (fun choice => mix scale nonnegative le_one
        ((menu setup runtime leaks bounds).uniformPolicy (phaseInitialLaw setup) horizon scheduler
          agent.1
          agent.2.1) (PMF.pure choice))).map project
    rw [bind_mix_pure, bind_mix_pure, mix_map, mix_map]
    congr 1
    · have same := congrArg (fun law => law.map Subtype.val)
        (uniform_phase_map setup runtime leaks bounds horizon scheduler agent clear)
      rw [PMF.map_comp] at same
      exact same.symm
    · exact recoveryComparisonWeights_free setup runtime leaks bounds horizon scheduler weights
        agent
        clear free
  · have recoveryNotFree : ¬ RecoveryOnePacket.FreeAgent (runtime := runtime) setup
      (RecoveryLeaks) bounds
      (RecoveryPrior) horizon
        (RecoveryScheduler) recoveryAgent := fun recoveryFree => free (freeIff.mp recoveryFree)
    by_cases keyed : KeyedAgent setup runtime leaks bounds horizon scheduler agent
    · have phaseOwned : ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
          (KeyedAgent setup runtime leaks bounds horizon scheduler) agent := ⟨keyed, free⟩
      have recoveryOwned : ownedKeyed
          (RecoveryOnePacket.FreeAgent (runtime := runtime) setup (RecoveryLeaks) bounds
            (RecoveryPrior) horizon
              (RecoveryScheduler))
          (RecoveryOnePacket.KeyedAgent (runtime := runtime) setup (RecoveryLeaks) bounds
            (RecoveryPrior) horizon
              (RecoveryScheduler))
          recoveryAgent := ⟨keyed, recoveryNotFree⟩
      have phaseMix := Vegas.freeKeyedMixture_of_keyed weights phaseFree phasePrescribed phaseKeyed
        free phaseOwned
      have recoveryMixture := Vegas.freeKeyedMixture_of_keyed recoveryWeights recoveryFree
          recoveryPrescribed recoveryKeyed
        recoveryNotFree recoveryOwned
      have represented :
          RecoveryOnePacket.agentKey (runtime := runtime) setup (RecoveryLeaks) bounds
            (RecoveryPrior) horizon
              (RecoveryScheduler) recoveryAgent ∈ Set.range
          (fun agent : {agent : (M).InformationAgent (M).playedInformation //
            ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
              (KeyedAgent setup runtime leaks bounds horizon scheduler) agent} =>
            agentKey setup runtime leaks bounds horizon scheduler agent.1) := ⟨⟨agent,
              phaseOwned⟩, rfl⟩
      change ((recoveryWeights (freeKeyedPool _ _ _ recoveryAgent)).bind
        (freeKeyedComponent recoveryFree recoveryPrescribed recoveryKeyed recoveryAgent)).map
            Subtype.val =
          ((weights (freeKeyedPool _ _ _ agent)).bind
            (freeKeyedComponent phaseFree phasePrescribed phaseKeyed agent)).map project
      rw [recoveryMixture, phaseMix]
      simp only [recoveryWeights, recoveryComparisonWeights, dite_eq_left represented]
      rw [PMF.map_bind, PMF.map_bind]
      congr 1
      funext option
      exact (keyedComponent_recovery setup runtime leaks bounds horizon scheduler assessment scale
        nonnegative le_one agent clear option).symm
    · have phaseNotOwned : ¬ ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
          (KeyedAgent setup runtime leaks bounds horizon scheduler) agent := fun owned => keyed
            owned.1
      have recoveryNotOwned : ¬ ownedKeyed
          (RecoveryOnePacket.FreeAgent (runtime := runtime) setup (RecoveryLeaks) bounds
            (RecoveryPrior) horizon
              (RecoveryScheduler))
          (RecoveryOnePacket.KeyedAgent (runtime := runtime) setup (RecoveryLeaks) bounds
            (RecoveryPrior) horizon
              (RecoveryScheduler))
          recoveryAgent := fun owned => keyed owned.1
      have phaseMix := Vegas.freeKeyedMixture_of_not_keyed weights phaseFree phasePrescribed
        phaseKeyed free phaseNotOwned
      have recoveryMixture := Vegas.freeKeyedMixture_of_not_keyed recoveryWeights recoveryFree
          recoveryPrescribed recoveryKeyed
        recoveryNotFree recoveryNotOwned
      change ((recoveryWeights (freeKeyedPool _ _ _ recoveryAgent)).bind
        (freeKeyedComponent recoveryFree recoveryPrescribed recoveryKeyed recoveryAgent)).map
            Subtype.val =
          ((weights (freeKeyedPool _ _ _ agent)).bind
            (freeKeyedComponent phaseFree phasePrescribed phaseKeyed agent)).map project
      rw [recoveryMixture, phaseMix]
      exact (prescribedComponent_recovery setup runtime leaks bounds horizon scheduler assessment
        scale
        nonnegative le_one agent clear).symm

/-- Equality also holds in the actual recovery choice type, including menu proofs. -/
theorem recoveryComparisonMixture_choice
    (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots p))
    (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup runtime leaks agent.2.1) :
    ((weights (pool setup runtime leaks bounds horizon scheduler agent)).bind
        (component setup runtime leaks bounds horizon scheduler assessment scale nonnegative le_one
          agent)).map (choiceEquiv setup runtime leaks bounds horizon scheduler agent clear) =
      (recoveryComparisonWeights setup runtime leaks bounds horizon scheduler weights
        (RecoveryOnePacket.pool (runtime := runtime) setup (RecoveryLeaks) bounds (RecoveryPrior)
          horizon
            (RecoveryScheduler)
          (projectedAgent setup runtime leaks bounds horizon scheduler agent clear))).bind
      (RecoveryOnePacket.component (runtime := runtime) setup (RecoveryLeaks) bounds
        (RecoveryPrior) horizon
          (RecoveryScheduler)
        assessment scale nonnegative le_one
        (projectedAgent setup runtime leaks bounds horizon scheduler agent clear)) := by
  apply pmf_map_injective Subtype.val_injective
  rw [PMF.map_comp]
  exact (recoveryComparisonMixture_at_clear setup runtime leaks bounds horizon scheduler
    assessment scale
    nonnegative le_one weights agent clear).symm

end Vegas.SequentialPhase
