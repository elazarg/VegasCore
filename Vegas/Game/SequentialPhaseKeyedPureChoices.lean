/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseKeyedLaw
import Vegas.Game.OnePacketPrescribedCompletion
import GameTheoryExtensions.Analysis.Protocol.SuccessRanking

/-! # Pure keyed choices and their physical tremble error -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability RecoveryProjection Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler]

local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "Initial" => recoveryInitialLaw setup
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "NativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks)
  (oldScheduler)
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) (oldLeaks) bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) (oldLeaks)
local notation "N" => onePacketModel setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol (RMenu) Initial horizon
  (oldScheduler)
local notation "NP" => onePacketProtocol setup (oldLeaks) bounds horizon (NativeScheduler)
local notation "RawNative" => ReactiveApplication.protocol (application setup (oldLeaks))
  (PMF.map RecoveryState.native (Initial)) horizon (NativeScheduler)
local notation "Clear" => ReactiveApplication.stateInvariant (app := application setup (oldLeaks))
  (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

local instance keyedPureComparisonHistory : Fintype ((RMenu).protocol
    ((Vegas.initialLaw setup).map (fun native =>
      (⟨native, ∅⟩ : RecoveryState (graph setup)))) horizon (oldScheduler)).History :=
  sourceHistoryFintype setup leaks bounds horizon scheduler

local instance keyedPureComparisonInformation (who : Player) : DecidableEq
    ((RecoveryOnePacket.model setup (oldLeaks) bounds
      ((Vegas.initialLaw setup).map (fun native =>
        (⟨native, ∅⟩ : RecoveryState (graph setup)))) horizon (oldScheduler)).InfoState who) :=
  sourceInfoDecidableEq setup leaks bounds horizon scheduler who

local instance keyedPureComparisonNature : (application setup (oldLeaks)).FiniteNature
    (Vegas.initialLaw setup) (NativeScheduler) := nativeNature setup leaks scheduler

local instance keyedPureNativeInformation (who : Player) : DecidableEq ((N).InfoState who) :=
  nativeInfoDecidableEq setup leaks bounds horizon scheduler who

local instance keyedPureRecoveryNature :
    (recoveryApplication (runtime setup) (oldLeaks)).FiniteNature
    ((Vegas.initialLaw setup).map (fun native =>
      (⟨native, ∅⟩ : RecoveryState (graph setup)))) (oldScheduler) :=
  recoveryNature setup leaks scheduler

local instance keyedPureNativeHistory : Fintype (NP).History :=
  @ReactiveApplication.ResponseMenu.historyFintype Player _ _ (NMenu) (Vegas.initialLaw setup)
    horizon (NativeScheduler) inferInstance (nativeNature setup leaks scheduler)

local notation "P" => phaseApplication (runtime setup) leaks
local notation "M" => model setup leaks bounds horizon scheduler
local notation "projectInfo" => PhaseRecoveryProjection.information (runtime setup) leaks (oldLeaks)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq

local notation "PhaseProtocol" => ReactiveApplication.ResponseMenu.protocol
  (menu setup leaks bounds) (initialLaw setup) horizon scheduler

open Classical in
/-- A native pure main late option has the same original phase local value up
to the physical tremble mass, for every bounded payoff and actual phase assessment. -/
theorem keyed_main_value_sub_le
    (source : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    {who : Player} (site : (M).InformationSite who) (clear : ClearInput setup leaks site.1)
    (nativeSite : (N).InformationSite who)
    (lifted : RecoveryProjection.liftInformation (runtime setup) (oldLeaks) nativeSite.1 =
      projectInfo site.1) (option : LateOption slots) (choice : (N).Choice who nativeSite.1)
    (main : lateChoice setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon (NativeScheduler)
      source who nativeSite.1 option = PMF.pure choice)
    (assessment : (M).BehavioralAssessment)
    {Outcome : Type*} (observe : (PhaseProtocol).History → Outcome)
    (utility : Outcome → Player → ℝ) {bound : ℝ}
    (bounded : ∀ final : (PhaseProtocol).History, |utility (observe final) who| ≤ bound) :
    let equivalent := ((choiceEquiv setup leaks bounds horizon scheduler ((M).agentAt site)
      clear).trans (Equiv.cast (congrArg (fun input => (R).Choice who input) lifted.symm))).trans
        (RecoveryOnePacket.sourceNativeChoiceEquiv setup (oldLeaks) bounds horizon (oldScheduler)
          who nativeSite.1)
    |localValue (2 * horizon + 1) observe utility assessment site
        (PMF.pure (equivalent.symm choice)) -
      localValue (2 * horizon + 1) observe utility assessment site
        (keyedComponent setup leaks bounds horizon scheduler source scale nonnegative le_one
          ((M).agentAt site) option)| ≤ 6 * scale * bound := by
  intro equivalent
  let value := fun found : (M).Choice who site.1 =>
    localValue (2 * horizon + 1) observe utility assessment site (PMF.pure found)
  have valueBounded : ∀ found, |value found| ≤ bound := by
    intro found
    dsimp only [value]
    rw [localValue_eq_expect_localRun]
    exact expect_abs_le_of_bounded
      (by obtain ⟨final, _⟩ := (localRun (2 * horizon + 1) assessment site
        (PMF.pure found)).support_nonempty
          exact (abs_nonneg _).trans (bounded final)) bounded
  have affine : ∀ law : PMF ((M).Choice who site.1),
      localValue (2 * horizon + 1) observe utility assessment site law = expect law value := by
    intro law
    have linear := localValue_bind (2 * horizon + 1) observe utility assessment site
      ((menu setup leaks bounds).bounded (initialLaw setup) horizon scheduler)
      ((menu setup leaks bounds).decisionRecall (initialLaw setup) horizon
        scheduler).actsOnceWhereItMatters law PMF.pure
    simpa only [PMF.bind_pure] using linear
  have projection : ∀ law : PMF ((M).Choice who site.1),
      expect (law.map equivalent) (fun found => value (equivalent.symm found)) =
        expect law value := by
    intro law
    rw [expect_map]
    congr 1
    funext found
    exact congrArg value (equivalent.symm_apply_apply found)
  have componentMap : (keyedComponent setup leaks bounds horizon scheduler source scale nonnegative
        le_one ((M).agentAt site) option).map equivalent =
      lateComponent setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon (NativeScheduler)
        source scale nonnegative le_one who nativeSite.1 option := by
    have projected := keyedComponent_native_choice setup leaks bounds horizon scheduler source scale
      nonnegative le_one site clear nativeSite lifted option
    simp only [PMF.map_comp] at projected
    convert projected using 1; congr 1
  have component := affine (keyedComponent setup leaks bounds horizon scheduler source scale
    nonnegative le_one ((M).agentAt site) option)
  rw [← projection, componentMap] at component
  have pureBound := valueBounded (equivalent.symm choice)
  have mainValue : expect (lateChoice setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
      (NativeScheduler) source who nativeSite.1 option)
      (fun found => value (equivalent.symm found)) =
      value (equivalent.symm choice) := by rw [main, expect_pure]
  have near := abs_expect_slotTrembledChoice_sub_le nonnegative le_one who nativeSite.1
    (lateChoice setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon (NativeScheduler) source
      who nativeSite.1 option)
    (PMF.pure (silenceChoice setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
      (NativeScheduler) who nativeSite.1))
    (slotChoice setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon (NativeScheduler) source
      who nativeSite.1)
    (fun found => value (equivalent.symm found)) (fun found => valueBounded _) pureBound mainValue
  rw [component, abs_sub_comm]
  exact near


open Classical in
/-- Every keyed option is one pure part of the actual target pool. -/
theorem keyed_component_gain_le_of_mixtures
    (source : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    {who : Player} (site : (M).InformationSite who)
    (keyed : ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
      (KeyedAgent setup leaks bounds horizon scheduler) ((M).agentAt site))
    (assessment : (M).BehavioralAssessment)
    {Outcome : Type*} (observe : (PhaseProtocol).History → Outcome)
    (utility : Outcome → Player → ℝ) {error : ℝ}
    (members : ∀ alternative : PMF (Part setup leaks bounds horizon scheduler slots
        (pool setup leaks bounds horizon scheduler ((M).agentAt site))),
      localGain (2 * horizon + 1) observe utility assessment site
        (alternative.bind (component setup leaks bounds horizon scheduler source scale nonnegative
          le_one ((M).agentAt site))) ≤ error)
    (option : LateOption slots) :
    localGain (2 * horizon + 1) observe utility assessment site
      (keyedComponent setup leaks bounds horizon scheduler source scale nonnegative le_one
        ((M).agentAt site) option) ≤ error := by
  let agent := (M).agentAt site
  let best := freeKeyedBest (FreeAgent setup leaks bounds horizon scheduler)
    (KeyedAgent setup leaks bounds horizon scheduler)
    (agentKey setup leaks bounds horizon scheduler)
    (LateOption slots) (fun _ => option)
  let prescribed := prescribedComponent setup leaks bounds horizon scheduler source scale
    nonnegative le_one
  let lateLaw := keyedComponent setup leaks bounds horizon scheduler source (slots := slots) scale
    nonnegative le_one
  have lawEq := freeKeyedComponent_at_not_free
    (freeLaw setup leaks bounds horizon scheduler scale nonnegative le_one) prescribed lateLaw best
    keyed.2
  rw [show best (.inr (keyedPool
      (ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (KeyedAgent setup leaks bounds horizon scheduler))
      (agentKey setup leaks bounds horizon scheduler) agent)) =
      keyedBest (fun _ => option) (keyedPool
        (ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (KeyedAgent setup leaks bounds horizon scheduler))
        (agentKey setup leaks bounds horizon scheduler) agent) from rfl,
    keyedComponent_best_of_keyed prescribed lateLaw (fun _ => option) keyed] at lawEq
  have near := members (PMF.pure (best (pool setup leaks bounds horizon scheduler agent)))
  simp only [PMF.pure_bind] at near
  change localGain (2 * horizon + 1) observe utility assessment site
    (freeKeyedComponent (freeLaw setup leaks bounds horizon scheduler scale nonnegative le_one)
      prescribed lateLaw agent (best (pool setup leaks bounds horizon scheduler agent))) ≤ error
    at near
  rw [lawEq] at near
  exact near

end Vegas.SequentialPhase
