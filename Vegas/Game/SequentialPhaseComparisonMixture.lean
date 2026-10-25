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
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler]

local notation "M" => model setup leaks bounds horizon scheduler
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "oldInitial" => recoveryInitialLaw setup
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "oldMenu" => Recovery.onePacketMenu (runtime setup) (oldLeaks) bounds
local notation "project" => fun choice => Option.map
  (PhaseRecoveryProjection.action (runtime setup) leaks (oldLeaks)) (Subtype.val choice)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq

omit [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler] in
private theorem choice_cast_val {who : Player} {first second : (R).InfoState who}
    (same : first = second) (choice : (R).Choice who first) :
    (Equiv.cast (congrArg (fun input => (R).Choice who input) same) choice).1 = choice.1 := by
  subst second
  rfl

theorem liftedChoiceEquiv_val (agent : (R).InformationAgent (R).playedInformation)
    (represented : Represented setup leaks bounds horizon scheduler agent)
    (choice : (M).Choice agent.1
      (liftedAgent setup leaks bounds horizon scheduler agent represented).2.1) :
    (liftedChoiceEquiv setup leaks bounds horizon scheduler agent represented choice).1 =
      project choice := by
  unfold liftedChoiceEquiv
  simp only [Equiv.trans_apply]
  have same : PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks)
      (liftedAgent setup leaks bounds horizon scheduler agent represented).2.1 = agent.2.1 :=
    congrArg (fun other : (R).InformationAgent (R).playedInformation => other.2.1)
      (projected_liftedAgent setup leaks bounds horizon scheduler agent represented)
  exact choice_cast_val setup leaks bounds horizon scheduler (who := agent.1)
    (first := PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks)
      (liftedAgent setup leaks bounds horizon scheduler agent represented).2.1)
    (second := agent.2.1) same _

theorem uniform_phase_map (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1) :
    (((menu setup leaks bounds).uniformPolicy (initialLaw setup) horizon scheduler agent.1
        agent.2.1).map (choiceEquiv setup leaks bounds horizon scheduler agent clear)) =
      (oldMenu).uniformPolicy (oldInitial) horizon (oldScheduler) agent.1
        (projectedAgent setup leaks bounds horizon scheduler agent clear).2.1 := by
  rw [← uniform_recovery_map setup leaks bounds horizon scheduler agent clear, PMF.map_comp]
  simp only [Function.comp_def, Equiv.apply_symm_apply]
  exact PMF.map_id _

theorem prescribedComponent_recovery (assessment : setup.intendedModel.BehavioralAssessment)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1) :
    (prescribedComponent setup leaks bounds horizon scheduler assessment scale nonnegative le_one
        agent).map project =
      (RecoveryOnePacket.prescribedComponent setup (oldLeaks) bounds (oldInitial) horizon
        (oldScheduler) assessment scale nonnegative le_one
        (projectedAgent setup leaks bounds horizon scheduler agent clear)).map Subtype.val := by
  unfold prescribedComponent
  rw [dite_eq_left clear, PMF.map_comp]
  congr 1
  funext choice
  exact congrArg Subtype.val
    ((choiceEquiv setup leaks bounds horizon scheduler agent clear).apply_symm_apply choice)

theorem keyedComponent_recovery (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1) (option : LateOption slots) :
    (keyedComponent setup leaks bounds horizon scheduler assessment scale nonnegative le_one
        agent option).map project =
      (RecoveryOnePacket.keyedComponent setup (oldLeaks) bounds (oldInitial) horizon
        (oldScheduler) assessment scale nonnegative le_one
        (projectedAgent setup leaks bounds horizon scheduler agent clear) option).map
          Subtype.val := by
  unfold keyedComponent
  rw [dite_eq_left clear, PMF.map_comp]
  congr 1
  funext choice
  exact congrArg Subtype.val
    ((choiceEquiv setup leaks bounds horizon scheduler agent clear).apply_symm_apply choice)

theorem recoveryComparisonWeights_free {slots : Nat}
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1)
    (free : FreeAgent setup leaks bounds horizon scheduler agent) :
    (recoveryComparisonWeights setup leaks bounds horizon scheduler weights
        (.inl ⟨projectedAgent setup leaks bounds horizon scheduler agent clear,
          (freeAgent_projected_iff setup leaks bounds horizon scheduler agent clear).mpr free⟩)).map
            Subtype.val =
      (weights (.inl ⟨agent, free⟩)).map project := by
  classical
  have represented : Represented setup leaks bounds horizon scheduler
      (projectedAgent setup leaks bounds horizon scheduler agent clear) := ⟨agent, clear, rfl⟩
  simp only [recoveryComparisonWeights, dite_eq_left represented, PMF.map_comp]
  have same := lifted_projectedAgent setup leaks bounds horizon scheduler agent clear represented
  have owner :
      (⟨liftedAgent setup leaks bounds horizon scheduler
          (projectedAgent setup leaks bounds horizon scheduler agent clear) represented,
        same.symm ▸ free⟩ : {agent : (M).InformationAgent (M).playedInformation //
          FreeAgent setup leaks bounds horizon scheduler agent}) = ⟨agent, free⟩ :=
    Subtype.ext same
  have erased := congrArg
    (fun owner : {agent : (M).InformationAgent (M).playedInformation //
        FreeAgent setup leaks bounds horizon scheduler agent} =>
      (weights (.inl owner)).map project) owner
  refine Eq.trans ?_ erased
  congr 1
  funext choice
  exact liftedChoiceEquiv_val setup leaks bounds horizon scheduler _ represented choice

/-- Every actual clear phase component mixture has exactly the recovery
comparison's optional-response law. No equality after exclusion is used. -/
theorem recoveryComparisonMixture_at_clear
    (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1) :
    ((recoveryComparisonWeights setup leaks bounds horizon scheduler weights
        (RecoveryOnePacket.pool setup (oldLeaks) bounds (oldInitial) horizon (oldScheduler)
          (projectedAgent setup leaks bounds horizon scheduler agent clear))).bind
      (RecoveryOnePacket.component setup (oldLeaks) bounds (oldInitial) horizon (oldScheduler)
        assessment scale nonnegative le_one
        (projectedAgent setup leaks bounds horizon scheduler agent clear))).map Subtype.val =
      ((weights (pool setup leaks bounds horizon scheduler agent)).bind
        (component setup leaks bounds horizon scheduler assessment scale nonnegative le_one
          agent)).map project := by
  classical
  let oldAgent := projectedAgent setup leaks bounds horizon scheduler agent clear
  let oldWeights := recoveryComparisonWeights setup leaks bounds horizon scheduler weights
  let phaseFree := freeLaw setup leaks bounds horizon scheduler scale nonnegative le_one
  let phasePrescribed := prescribedComponent setup leaks bounds horizon scheduler assessment scale
    nonnegative le_one
  let phaseKeyed := keyedComponent setup leaks bounds horizon scheduler assessment scale
    nonnegative le_one (slots := slots)
  let oldFree := RecoveryOnePacket.freeLaw setup (oldLeaks) bounds (oldInitial) horizon
    (oldScheduler) scale nonnegative le_one
  let oldPrescribed := RecoveryOnePacket.prescribedComponent setup (oldLeaks) bounds (oldInitial)
    horizon (oldScheduler) assessment scale nonnegative le_one
  let oldKeyed := RecoveryOnePacket.keyedComponent setup (oldLeaks) bounds (oldInitial) horizon
    (oldScheduler) assessment scale nonnegative le_one (slots := slots)
  have freeIff := freeAgent_projected_iff setup leaks bounds horizon scheduler agent clear
  by_cases free : FreeAgent setup leaks bounds horizon scheduler agent
  · have oldIsFree := freeIff.mpr free
    have phaseMix : (weights (pool setup leaks bounds horizon scheduler agent)).bind
        (component setup leaks bounds horizon scheduler assessment scale nonnegative le_one agent) =
        (weights (.inl ⟨agent, free⟩)).bind (phaseFree agent) := by
      change (weights (freeKeyedPool _ _ _ agent)).bind
        (freeKeyedComponent phaseFree phasePrescribed phaseKeyed agent) = _
      unfold freeKeyedComponent
      rw [freeKeyedPool_of_free free]
      congr 1
      funext choice
      exact dite_eq_left rfl
    have oldMix : (oldWeights (RecoveryOnePacket.pool setup (oldLeaks) bounds (oldInitial) horizon
          (oldScheduler) oldAgent)).bind
        (RecoveryOnePacket.component setup (oldLeaks) bounds (oldInitial) horizon (oldScheduler)
          assessment scale nonnegative le_one oldAgent) =
        (oldWeights (.inl ⟨oldAgent, oldIsFree⟩)).bind (oldFree oldAgent) := by
      change (oldWeights (freeKeyedPool _ _ _ oldAgent)).bind
        (freeKeyedComponent oldFree oldPrescribed oldKeyed oldAgent) = _
      unfold freeKeyedComponent
      rw [freeKeyedPool_of_free oldIsFree]
      congr 1
      funext choice
      exact dite_eq_left rfl
    change ((oldWeights (RecoveryOnePacket.pool setup (oldLeaks) bounds (oldInitial) horizon
      (oldScheduler) oldAgent)).bind
        (RecoveryOnePacket.component setup (oldLeaks) bounds (oldInitial) horizon (oldScheduler)
          assessment scale nonnegative le_one oldAgent)).map Subtype.val = _
    rw [oldMix, phaseMix]
    change ((oldWeights (.inl ⟨oldAgent, oldIsFree⟩)).bind (fun choice =>
      mix scale nonnegative le_one
        ((oldMenu).uniformPolicy (oldInitial) horizon (oldScheduler) oldAgent.1 oldAgent.2.1)
        (PMF.pure choice))).map Subtype.val =
      ((weights (.inl ⟨agent, free⟩)).bind (fun choice => mix scale nonnegative le_one
        ((menu setup leaks bounds).uniformPolicy (initialLaw setup) horizon scheduler agent.1
          agent.2.1) (PMF.pure choice))).map project
    rw [bind_mix_pure, bind_mix_pure, mix_map, mix_map]
    congr 1
    · have same := congrArg (fun law => law.map Subtype.val)
        (uniform_phase_map setup leaks bounds horizon scheduler agent clear)
      rw [PMF.map_comp] at same
      exact same.symm
    · exact recoveryComparisonWeights_free setup leaks bounds horizon scheduler weights agent
        clear free
  · have oldNotFree : ¬ RecoveryOnePacket.FreeAgent setup (oldLeaks) bounds (oldInitial) horizon
        (oldScheduler) oldAgent := fun oldFree => free (freeIff.mp oldFree)
    by_cases keyed : KeyedAgent setup leaks bounds horizon scheduler agent
    · have phaseOwned : ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (KeyedAgent setup leaks bounds horizon scheduler) agent := ⟨keyed, free⟩
      have oldOwned : ownedKeyed
          (RecoveryOnePacket.FreeAgent setup (oldLeaks) bounds (oldInitial) horizon (oldScheduler))
          (RecoveryOnePacket.KeyedAgent setup (oldLeaks) bounds (oldInitial) horizon (oldScheduler))
          oldAgent := ⟨keyed, oldNotFree⟩
      have phaseMix := Vegas.freeKeyedMixture_of_keyed weights phaseFree phasePrescribed phaseKeyed
        free phaseOwned
      have oldMix := Vegas.freeKeyedMixture_of_keyed oldWeights oldFree oldPrescribed oldKeyed
        oldNotFree oldOwned
      have represented :
          RecoveryOnePacket.agentKey setup (oldLeaks) bounds (oldInitial) horizon
              (oldScheduler) oldAgent ∈ Set.range
          (fun agent : {agent : (M).InformationAgent (M).playedInformation //
            ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
              (KeyedAgent setup leaks bounds horizon scheduler) agent} =>
            agentKey setup leaks bounds horizon scheduler agent.1) := ⟨⟨agent, phaseOwned⟩, rfl⟩
      change ((oldWeights (freeKeyedPool _ _ _ oldAgent)).bind
        (freeKeyedComponent oldFree oldPrescribed oldKeyed oldAgent)).map Subtype.val =
          ((weights (freeKeyedPool _ _ _ agent)).bind
            (freeKeyedComponent phaseFree phasePrescribed phaseKeyed agent)).map project
      rw [oldMix, phaseMix]
      simp only [oldWeights, recoveryComparisonWeights, dite_eq_left represented]
      rw [PMF.map_bind, PMF.map_bind]
      congr 1
      funext option
      exact (keyedComponent_recovery setup leaks bounds horizon scheduler assessment scale
        nonnegative le_one agent clear option).symm
    · have phaseNotOwned : ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (KeyedAgent setup leaks bounds horizon scheduler) agent := fun owned => keyed owned.1
      have oldNotOwned : ¬ ownedKeyed
          (RecoveryOnePacket.FreeAgent setup (oldLeaks) bounds (oldInitial) horizon (oldScheduler))
          (RecoveryOnePacket.KeyedAgent setup (oldLeaks) bounds (oldInitial) horizon (oldScheduler))
          oldAgent := fun owned => keyed owned.1
      have phaseMix := Vegas.freeKeyedMixture_of_not_keyed weights phaseFree phasePrescribed
        phaseKeyed free phaseNotOwned
      have oldMix := Vegas.freeKeyedMixture_of_not_keyed oldWeights oldFree oldPrescribed oldKeyed
        oldNotFree oldNotOwned
      change ((oldWeights (freeKeyedPool _ _ _ oldAgent)).bind
        (freeKeyedComponent oldFree oldPrescribed oldKeyed oldAgent)).map Subtype.val =
          ((weights (freeKeyedPool _ _ _ agent)).bind
            (freeKeyedComponent phaseFree phasePrescribed phaseKeyed agent)).map project
      rw [oldMix, phaseMix]
      exact (prescribedComponent_recovery setup leaks bounds horizon scheduler assessment scale
        nonnegative le_one agent clear).symm

/-- Equality also holds in the actual recovery choice type, including menu proofs. -/
theorem recoveryComparisonMixture_choice
    (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup leaks bounds horizon scheduler slots p))
    (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1) :
    ((weights (pool setup leaks bounds horizon scheduler agent)).bind
        (component setup leaks bounds horizon scheduler assessment scale nonnegative le_one
          agent)).map (choiceEquiv setup leaks bounds horizon scheduler agent clear) =
      (recoveryComparisonWeights setup leaks bounds horizon scheduler weights
        (RecoveryOnePacket.pool setup (oldLeaks) bounds (oldInitial) horizon (oldScheduler)
          (projectedAgent setup leaks bounds horizon scheduler agent clear))).bind
      (RecoveryOnePacket.component setup (oldLeaks) bounds (oldInitial) horizon (oldScheduler)
        assessment scale nonnegative le_one
        (projectedAgent setup leaks bounds horizon scheduler agent clear)) := by
  apply pmf_map_injective Subtype.val_injective
  rw [PMF.map_comp]
  exact (recoveryComparisonMixture_at_clear setup leaks bounds horizon scheduler assessment scale
    nonnegative le_one weights agent clear).symm

end Vegas.SequentialPhase
