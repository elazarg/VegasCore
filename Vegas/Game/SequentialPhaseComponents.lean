/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseChoiceEquivalence
import Vegas.Game.SequentialPhaseFiniteNature
import Vegas.Game.RecoveryOnePacketComponents

/-! # Operational components of the actual canonical singleton phase game

Clear played inputs use the original recovery components through their exact
local choice equivalence. Every other input has its own freely selected actual
choice. Pool keys and all mapped response data use only player-local projection.
-/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)

abbrev menu := (PhaseCount.normalization (runtime setup) leaks).menu
  (PhaseCount.onePacketMenu (runtime setup) leaks bounds)

def initialLaw : PMF (PhaseRuntimeState (graph setup)) :=
  (setup.initialLaw.map setup.eventInputs).map
    (PhaseRuntimeState.initial (sequentialRuntimePhasePlan setup.program))

def recoveryLeaks := PhaseNativeProjection.nativeLeaks leaks
  (sequentialRuntimePhasePlan setup.program)

def recoveryInitialLaw : PMF (RecoveryState (graph setup)) :=
  (Vegas.initialLaw setup).map fun native => ⟨native, ∅⟩

def recoveryScheduler := SequentialPhaseSchedulerInformation.scheduler setup.program
  (runtime setup) leaks (recoveryLeaks setup leaks) scheduler

abbrev model := (menu setup leaks bounds).information (initialLaw setup) horizon scheduler

abbrev recoveryModel := RecoveryOnePacket.model setup (recoveryLeaks setup leaks) bounds
  (recoveryInitialLaw setup) horizon (recoveryScheduler setup leaks scheduler)

local notation "P" => phaseApplication (runtime setup) leaks
local notation "M" => model setup leaks bounds horizon scheduler
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "oldInitial" => recoveryInitialLaw setup
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "oldMenu" => Recovery.onePacketMenu (runtime setup) (oldLeaks) bounds

instance recoveryNature
    [nature : (phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler] :
    (recoveryApplication (runtime setup) (oldLeaks)).FiniteNature (oldInitial) (oldScheduler) := by
  have phase : (phaseApplication (runtime setup) leaks).FiniteNature
      ((setup.initialLaw.map setup.eventInputs).map
        (PhaseRuntimeState.initial (sequentialRuntimePhasePlan setup.program))) scheduler := nature
  have actual := SequentialPhaseSchedulerInformation.recovery_finiteNature setup.program
    (runtime setup) leaks (setup.initialLaw.map setup.eventInputs) scheduler
  have priors :
      (setup.initialLaw.map setup.eventInputs).map
        (fun draw => (⟨EventGraphRuntime.State.initial draw, ∅⟩ : RecoveryState (graph setup))) =
      oldInitial := by
    simp only [recoveryInitialLaw, Vegas.initialLaw, serviceInitialLaw, PMF.map_comp,
      Function.comp_def]
  exact Eq.mp (congrArg (fun prior : PMF (RecoveryState (graph setup)) =>
    (recoveryApplication (runtime setup) (oldLeaks)).FiniteNature prior (oldScheduler)) priors)
    actual

local instance phaseInfoDecidableEq (who : Player) : DecidableEq ((M).InfoState who) :=
  Classical.decEq _

local instance recoveryInfoDecidableEq (who : Player) : DecidableEq ((R).InfoState who) :=
  Classical.decEq _

variable [nature : (phaseApplication (runtime setup) leaks).FiniteNature
  (initialLaw setup) scheduler]

/-- Public local clearance; inactive ghost inputs do not qualify. -/
def ClearInput (input : (P).Info) : Prop :=
  input.elim False fun data => data.2.application.2.excluded = ∅

def PublicExclusion (input : (P).Info) : Prop :=
  input.elim False fun data => data.2.application.2.excluded ≠ ∅

private theorem clear_agent_origin (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1) :
    ∃ control : (P).Control,
      ∃ _trace : ((menu setup leaks bounds).protocol (initialLaw setup) horizon scheduler).Trace
          (some control),
        ¬ (P).terminal (some control) ∧ control.actor = some agent.1 ∧
          agent.2.1 = some (control.execution.recall agent.1,
            control.execution.observe (P) agent.1) ∧
          control.execution.application.current.excluded = ∅ := by
  classical
  have played := agent.2.2
  unfold InformationModel.playedInformation at played
  obtain ⟨history, member, observed⟩ := Finset.mem_image.mp played
  have running := (Finset.mem_filter.mp member).2
  have seen := ((menu setup leaks bounds).info (initialLaw setup) horizon scheduler agent.1
    history.trace).symm.trans observed
  cases current : history.state with
  | none => rw [current] at seen; rw [← seen] at clear; exact clear.elim
  | some control =>
      by_cases acting : control.actor = some agent.1
      · rw [current] at seen
        simp only [ReactiveApplication.observe, acting, ↓reduceIte] at seen
        refine ⟨control, current ▸ history.trace, ?_, acting, seen.symm, ?_⟩
        · change ¬ (P).terminal history.state at running
          rwa [current] at running
        · rw [← seen] at clear
          exact clear
      · rw [current] at seen
        simp only [ReactiveApplication.observe, acting, ↓reduceIte] at seen
        rw [← seen] at clear
        exact clear.elim

/-- Every clear played phase input is a genuinely played projected recovery input. -/
theorem projected_input_played (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1) :
    PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks) agent.2.1 ∈
      (R).playedInformation agent.1 := by
  obtain ⟨control, trace, running, acting, seen, empty⟩ :=
    clear_agent_origin setup leaks bounds horizon scheduler agent clear
  obtain ⟨prior, _length⟩ := PhaseRecoveryProjection.trace_projected_canonical_clear setup.program
    (runtime setup) leaks bounds (setup.initialLaw.map setup.eventInputs) horizon scheduler trace
    empty
  have priors :
      (setup.initialLaw.map setup.eventInputs).map
        (fun draw => (⟨EventGraphRuntime.State.initial draw, ∅⟩ : RecoveryState (graph setup))) =
      oldInitial := by
    simp only [recoveryInitialLaw, Vegas.initialLaw, serviceInitialLaw, PMF.map_comp,
      Function.comp_def]
  have prior : ((oldMenu).protocol (oldInitial) horizon (oldScheduler)).Trace
      (PhaseRecoveryProjection.protocolState (runtime setup) leaks (oldLeaks) (some control)) :=
    Eq.mp (congrArg (fun initial : PMF (RecoveryState (graph setup)) =>
      ((oldMenu).protocol initial horizon (oldScheduler)).Trace
        (PhaseRecoveryProjection.protocolState (runtime setup) leaks (oldLeaks) (some control)))
      priors) prior
  have stillRunning : ¬ ((oldMenu).protocol (oldInitial) horizon (oldScheduler)).terminal
      (PhaseRecoveryProjection.protocolState (runtime setup) leaks (oldLeaks) (some control)) :=
    running
  have played := (R).mem_playedInformation (who := agent.1) (history := ⟨_, prior⟩) stillRunning
  have observed : (R).infoOf agent.1 prior =
      PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks) agent.2.1 := by
    have currentInput : (P).observe agent.1 (some control) = agent.2.1 := by
      simp only [ReactiveApplication.observe, acting, ↓reduceIte]
      exact seen.symm
    exact ((oldMenu).info (oldInitial) horizon (oldScheduler) agent.1 prior).trans
      ((PhaseRecoveryProjection.observe_state (runtime setup) leaks (oldLeaks) agent.1
        (some control)).trans (congrArg
          (PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks)) currentInput))
  rwa [observed] at played

/-- The represented old agent contains only the projected player-local input. -/
def projectedAgent (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1) : (R).InformationAgent (R).playedInformation :=
  ⟨agent.1, ⟨PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks) agent.2.1,
    projected_input_played setup leaks bounds horizon scheduler agent clear⟩⟩

private theorem choice_admission_iff (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1) (choice : Option (P).Action) :
    choice ∈ (M).menu agent.1 agent.2.1 ↔
      choice.map (PhaseRecoveryProjection.action (runtime setup) leaks (oldLeaks)) ∈
        (R).menu agent.1
          (PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks) agent.2.1) := by
  obtain ⟨control, trace, _running, _acting, seen, empty⟩ :=
    clear_agent_origin setup leaks bounds horizon scheduler agent clear
  rw [seen]
  cases choice with
  | none =>
      change (∃ response ∈ (menu setup leaks bounds).actions agent.1 _ _,
        (none : Option (P).Action) = some response) ↔
        (∃ response ∈ (oldMenu).actions agent.1 _ _,
          (none : Option (recoveryApplication (runtime setup) (oldLeaks)).Action) = some response)
      simp
  | some response =>
      change (∃ candidate ∈ (menu setup leaks bounds).actions agent.1 _ _,
        some response = some candidate) ↔
        (∃ candidate ∈ (oldMenu).actions agent.1 _ _,
          some (PhaseRecoveryProjection.action (runtime setup) leaks (oldLeaks) response) =
            some candidate)
      have callbacks := phase_canonical_callback_iff_recovery setup leaks bounds horizon scheduler
        trace empty agent.1 response
      constructor
      · rintro ⟨candidate, admitted, same⟩
        cases Option.some.inj same
        exact ⟨_, callbacks.mp admitted, rfl⟩
      · rintro ⟨candidate, admitted, same⟩
        cases Option.some.inj same
        exact ⟨_, callbacks.mpr admitted, rfl⟩

/-- The pure response-syntax equivalence at every clear played information input. -/
def choiceEquiv (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1) :
    (M).Choice agent.1 agent.2.1 ≃ (R).Choice agent.1
      (PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks) agent.2.1) where
  toFun choice := ⟨choice.1.map (PhaseRecoveryProjection.action (runtime setup) leaks (oldLeaks)),
    (choice_admission_iff setup leaks bounds horizon scheduler agent clear _).mp choice.2⟩
  invFun choice :=
    ⟨choice.1.map (PhaseRecoveryProjection.phaseAction (runtime setup) leaks (oldLeaks)),
      (choice_admission_iff setup leaks bounds horizon scheduler agent clear _).mpr (by
        have same : (choice.1.map
            (PhaseRecoveryProjection.phaseAction (runtime setup) leaks (oldLeaks))).map
              (PhaseRecoveryProjection.action (runtime setup) leaks (oldLeaks)) = choice.1 := by
          simp only [Option.map_map, Function.comp_def,
            PhaseRecoveryProjection.action_phaseAction]
          exact congrFun Option.map_id choice.1
        rw [same]
        exact choice.2)⟩
  left_inv choice := by
    apply Subtype.ext
    change (choice.1.map (PhaseRecoveryProjection.action (runtime setup) leaks (oldLeaks))).map
      (PhaseRecoveryProjection.phaseAction (runtime setup) leaks (oldLeaks)) = choice.1
    cases chosen : choice.1 with
    | none => rfl
    | some response =>
        exact congrArg some
          (PhaseRecoveryProjection.phaseAction_action (runtime setup) leaks (oldLeaks) response)
  right_inv choice := by
    apply Subtype.ext
    change (choice.1.map (PhaseRecoveryProjection.phaseAction (runtime setup) leaks (oldLeaks))).map
      (PhaseRecoveryProjection.action (runtime setup) leaks (oldLeaks)) = choice.1
    cases chosen : choice.1 with
    | none => rfl
    | some response =>
        exact congrArg some
          (PhaseRecoveryProjection.action_phaseAction (runtime setup) leaks (oldLeaks) response)

/-- The original forced-region classification on the actual projected clear agent. -/
def ForcedAgent (agent : (M).InformationAgent (M).playedInformation) : Prop :=
  ∃ clear : ClearInput setup leaks agent.2.1, RecoveryOnePacket.ForcedAgent setup (oldLeaks) bounds
    (oldInitial) horizon (oldScheduler) (projectedAgent setup leaks bounds horizon scheduler agent
      clear)

def FreeAgent (agent : (M).InformationAgent (M).playedInformation) : Prop :=
  ¬ ForcedAgent setup leaks bounds horizon scheduler agent

def KeyedAgent (agent : (M).InformationAgent (M).playedInformation) : Prop :=
  LateDelivery setup (oldLeaks) agent.1 (RecoveryProjection.information (runtime setup) (oldLeaks)
    (PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks) agent.2.1))

def agentKey (agent : (M).InformationAgent (M).playedInformation) :
    Option (LateKey setup (oldLeaks)) :=
  lateKey setup (oldLeaks) agent.1 (RecoveryProjection.information (runtime setup) (oldLeaks)
    (PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks) agent.2.1))

abbrev pool := freeKeyedPool (FreeAgent setup leaks bounds horizon scheduler)
  (KeyedAgent setup leaks bounds horizon scheduler) (agentKey setup leaks bounds horizon scheduler)

abbrev Part (slots : Nat) := FreeKeyedPart (FreeAgent setup leaks bounds horizon scheduler)
  (KeyedAgent setup leaks bounds horizon scheduler) (agentKey setup leaks bounds horizon scheduler)
  (LateOption slots)

theorem freeAgent_of_publicExclusion (agent : (M).InformationAgent (M).playedInformation)
    (excluded : PublicExclusion setup leaks agent.2.1) :
    FreeAgent setup leaks bounds horizon scheduler agent := by
  rintro ⟨clear, _forced⟩
  cases current : agent.2.1 with
  | none => rw [current] at excluded; exact excluded.elim
  | some input => rw [current] at excluded clear; exact excluded clear

/-- Uniform reference on the actual phase menu, including inactive singleton choices. -/
theorem uniform_fullSupport (agent : (M).InformationAgent (M).playedInformation) :
    FullSupport ((menu setup leaks bounds).uniformPolicy (initialLaw setup) horizon scheduler
      agent.1 agent.2.1) := by
  intro choice
  let := Fintype.ofFinite ((M).Choice agent.1 agent.2.1)
  exact PMF.mem_support_uniformOfFintype choice

/-- The original recovery reference becomes the actual phase reference under
the local bijection; no reweighting or enlarged menu is involved. -/
theorem uniform_recovery_map (agent : (M).InformationAgent (M).playedInformation)
    (clear : ClearInput setup leaks agent.2.1) :
    (((oldMenu).uniformPolicy (oldInitial) horizon (oldScheduler) agent.1
        (PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks) agent.2.1)).map
      (choiceEquiv setup leaks bounds horizon scheduler agent clear).symm) =
      (menu setup leaks bounds).uniformPolicy (initialLaw setup) horizon scheduler agent.1
        agent.2.1 := by
  classical
  let equivalent := choiceEquiv setup leaks bounds horizon scheduler agent clear
  let := Fintype.ofFinite ((M).Choice agent.1 agent.2.1)
  let := Fintype.ofFinite ((R).Choice agent.1
    (PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks) agent.2.1))
  ext choice
  have mapped := pmf_map_apply_of_injective
    ((oldMenu).uniformPolicy (oldInitial) horizon (oldScheduler) agent.1
      (PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks) agent.2.1))
    equivalent.symm.injective (equivalent choice)
  rw [equivalent.symm_apply_apply] at mapped
  rw [mapped]
  simp only [ReactiveApplication.ResponseMenu.uniformPolicy, PMF.uniformOfFintype_apply]
  exact congrArg (fun count : Nat => (count : ENNReal)⁻¹) (Fintype.card_congr equivalent).symm

def freeLaw (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (M).InformationAgent (M).playedInformation)
    (choice : (M).Choice agent.1 agent.2.1) : PMF ((M).Choice agent.1 agent.2.1) :=
  mix scale nonnegative le_one
    ((menu setup leaks bounds).uniformPolicy (initialLaw setup) horizon scheduler agent.1
      agent.2.1) (PMF.pure choice)

open Classical in
/-- The old prescribed operational law, transported through the actual local menu. -/
def prescribedComponent (assessment : setup.intendedModel.BehavioralAssessment)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (M).InformationAgent (M).playedInformation) : PMF ((M).Choice agent.1 agent.2.1) :=
  if clear : ClearInput setup leaks agent.2.1 then
    (RecoveryOnePacket.prescribedComponent setup (oldLeaks) bounds (oldInitial) horizon
      (oldScheduler) assessment scale nonnegative le_one
      (projectedAgent setup leaks bounds horizon scheduler agent clear)).map
        (choiceEquiv setup leaks bounds horizon scheduler agent clear).symm
  else (menu setup leaks bounds).uniformPolicy (initialLaw setup) horizon scheduler agent.1
    agent.2.1

open Classical in
/-- Each old keyed option is read at the same projected player-local input. -/
def keyedComponent (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (M).InformationAgent (M).playedInformation) (option : LateOption slots) :
    PMF ((M).Choice agent.1 agent.2.1) :=
  if clear : ClearInput setup leaks agent.2.1 then
    (RecoveryOnePacket.keyedComponent setup (oldLeaks) bounds (oldInitial) horizon
      (oldScheduler) assessment scale nonnegative le_one
      (projectedAgent setup leaks bounds horizon scheduler agent clear) option).map
        (choiceEquiv setup leaks bounds horizon scheduler agent clear).symm
  else (menu setup leaks bounds).uniformPolicy (initialLaw setup) horizon scheduler agent.1
    agent.2.1

def component (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (agent : (M).InformationAgent (M).playedInformation) :
    Part setup leaks bounds horizon scheduler slots
        (pool setup leaks bounds horizon scheduler agent) →
      PMF ((M).Choice agent.1 agent.2.1) :=
  freeKeyedComponent (freeLaw setup leaks bounds horizon scheduler scale nonnegative le_one)
    (prescribedComponent setup leaks bounds horizon scheduler assessment scale nonnegative le_one)
    (keyedComponent setup leaks bounds horizon scheduler assessment scale nonnegative le_one) agent

theorem freeLaw_fullSupport {scale : ℝ} (positive : 0 < scale) (le_one : scale ≤ 1)
    (agent : (M).InformationAgent (M).playedInformation)
    (choice : (M).Choice agent.1 agent.2.1) :
    FullSupport (freeLaw setup leaks bounds horizon scheduler scale positive.le le_one agent
      choice) :=
  fun other => mem_support_mix_left _ _ _ positive
    (uniform_fullSupport setup leaks bounds horizon scheduler agent other)

theorem prescribedComponent_fullSupport (assessment : setup.intendedModel.BehavioralAssessment)
    {scale : ℝ} (positive : 0 < scale) (le_one : scale ≤ 1)
    (agent : (M).InformationAgent (M).playedInformation) :
    FullSupport (prescribedComponent setup leaks bounds horizon scheduler assessment scale
      positive.le le_one agent) := by
  classical
  unfold prescribedComponent
  split
  · rename_i clear
    have full : FullSupport (RecoveryOnePacket.prescribedComponent setup (oldLeaks) bounds
        (oldInitial) horizon (oldScheduler) assessment scale positive.le le_one
        (projectedAgent setup leaks bounds horizon scheduler agent clear)) := by
      unfold RecoveryOnePacket.prescribedComponent
      apply RecoveryProjection.boundedRecoveryLaw_fullSupport
      exact slotTrembledChoice_fullSupport setup (oldLeaks) bounds
        ((oldInitial).map RecoveryState.native) horizon
        (RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks) (oldScheduler))
        positive le_one _ _ _ _ _
    intro choice
    exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨(choiceEquiv setup leaks bounds horizon scheduler agent clear) choice, full _,
        Equiv.symm_apply_apply _ _⟩
  · exact uniform_fullSupport setup leaks bounds horizon scheduler agent

theorem keyedComponent_fullSupport (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} {scale : ℝ} (positive : 0 < scale) (le_one : scale ≤ 1)
    (agent : (M).InformationAgent (M).playedInformation) (option : LateOption slots) :
    FullSupport (keyedComponent setup leaks bounds horizon scheduler assessment scale positive.le
      le_one agent option) := by
  classical
  unfold keyedComponent
  split
  · rename_i clear
    have full : FullSupport (RecoveryOnePacket.keyedComponent setup (oldLeaks) bounds
        (oldInitial) horizon (oldScheduler) assessment scale positive.le le_one
        (projectedAgent setup leaks bounds horizon scheduler agent clear) option) := by
      unfold RecoveryOnePacket.keyedComponent
      apply RecoveryProjection.boundedRecoveryLaw_fullSupport
      exact lateComponent_fullSupport setup (oldLeaks) bounds
        ((oldInitial).map RecoveryState.native)
        horizon (RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks) (oldScheduler))
        assessment positive le_one _ _ option
    intro choice
    exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨(choiceEquiv setup leaks bounds horizon scheduler agent clear) choice, full _,
        Equiv.symm_apply_apply _ _⟩
  · exact uniform_fullSupport setup leaks bounds horizon scheduler agent

theorem component_fullSupport (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} {scale : ℝ} (positive : 0 < scale) (le_one : scale ≤ 1)
    (agent : (M).InformationAgent (M).playedInformation)
    (part : Part setup leaks bounds horizon scheduler slots
      (pool setup leaks bounds horizon scheduler agent)) :
    FullSupport (component setup leaks bounds horizon scheduler assessment scale positive.le le_one
      agent part) := by
  apply freeKeyedComponent_fullSupport
  · exact freeLaw_fullSupport setup leaks bounds horizon scheduler positive le_one
  · exact prescribedComponent_fullSupport setup leaks bounds horizon scheduler assessment positive
      le_one
  · exact keyedComponent_fullSupport setup leaks bounds horizon scheduler assessment positive le_one

theorem freeLaw_converges (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n)
    (le_one : ∀ n, scale n ≤ 1) (vanishes : Tendsto scale atTop (nhds 0))
    (agent : (M).InformationAgent (M).playedInformation)
    (choice : (M).Choice agent.1 agent.2.1) :
    PMFConvergesPointwise (fun n => freeLaw setup leaks bounds horizon scheduler (scale n)
      (positive n).le (le_one n) agent choice) (PMF.pure choice) :=
  pmfConvergesPointwise_mix_zero scale (fun n => (positive n).le) le_one vanishes
    ((menu setup leaks bounds).uniformPolicy (initialLaw setup) horizon scheduler agent.1 agent.2.1)
    (PMF.pure choice)

end Vegas.SequentialPhase
