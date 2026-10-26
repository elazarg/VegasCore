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
  (runtime : EventGraphRuntime (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  [(phaseApplication runtime leaks).FiniteNature (phaseInitialLaw setup) scheduler]

local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "RecoveryPrior" => recoveryInitialLaw setup
local notation "RecoveryScheduler" => recoveryScheduler setup runtime leaks scheduler
local notation "NativeScheduler" => RecoveryProjection.nativeScheduler runtime
    (RecoveryLeaks)
  (RecoveryScheduler)
local notation "R" => recoveryModel setup runtime leaks bounds horizon scheduler
local notation "RMenu" => Recovery.onePacketMenu runtime (RecoveryLeaks) bounds
local notation "NMenu" => bounds.onePacketMenu runtime (RecoveryLeaks)
local notation "N" => onePacketModel (runtime := runtime) setup (RecoveryLeaks) bounds
  (Vegas.initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol (RMenu) RecoveryPrior horizon
  (RecoveryScheduler)
local notation "NP" => onePacketProtocol (runtime := runtime) setup (RecoveryLeaks) bounds horizon
  (NativeScheduler)
local notation "RawNative" => ReactiveApplication.protocol (application (runtime := runtime) setup
  (RecoveryLeaks))
  (PMF.map RecoveryState.native (RecoveryPrior)) horizon (NativeScheduler)
local notation "Clear" => ReactiveApplication.stateInvariant (app := application (runtime :=
  runtime) setup
    (RecoveryLeaks))
  (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

local notation "P" => phaseApplication runtime leaks
local notation "M" => model setup runtime leaks bounds horizon scheduler
local notation "projectInfo" => PhaseRecoveryProjection.information runtime leaks
    (RecoveryLeaks)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

local notation "PhaseProtocol" => ReactiveApplication.ResponseMenu.protocol
  (menu setup runtime leaks bounds) (phaseInitialLaw setup) horizon scheduler

open Classical in
/-- A native pure main late option has the same original phase local value up
to the physical tremble mass, for every bounded payoff and actual phase assessment. -/
theorem keyed_main_value_sub_le
    (source : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    {who : Player} (site : (M).InformationSite who) (clear : ClearInput setup runtime leaks site.1)
    (nativeSite : (N).InformationSite who)
    (lifted : RecoveryProjection.liftInformation runtime (RecoveryLeaks) nativeSite.1 =
      projectInfo site.1) (option : LateOption slots) (choice : (N).Choice who nativeSite.1)
    (main : lateChoice (runtime := runtime) setup (RecoveryLeaks) bounds (Vegas.initialLaw setup)
      horizon
        (NativeScheduler)
      source who nativeSite.1 option = PMF.pure choice)
    (assessment : (M).BehavioralAssessment)
    {Outcome : Type*} (observe : (PhaseProtocol).History → Outcome)
    (utility : Outcome → Player → ℝ) {bound : ℝ}
    (bounded : ∀ final : (PhaseProtocol).History, |utility (observe final) who| ≤ bound) :
    let equivalent := ((choiceEquiv setup runtime leaks bounds horizon scheduler ((M).agentAt site)
      clear).trans (Equiv.cast (congrArg (fun input => (R).Choice who input) lifted.symm))).trans
        (RecoveryOnePacket.sourceNativeChoiceEquiv (runtime := runtime) setup (RecoveryLeaks)
          bounds horizon
            (RecoveryScheduler)
          who nativeSite.1)
    |localValue (2 * horizon + 1) observe utility assessment site
        (PMF.pure (equivalent.symm choice)) -
      localValue (2 * horizon + 1) observe utility assessment site
        (keyedComponent setup runtime leaks bounds horizon scheduler source scale nonnegative le_one
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
      ((menu setup runtime leaks bounds).bounded (phaseInitialLaw setup) horizon scheduler)
      ((menu setup runtime leaks bounds).decisionRecall (phaseInitialLaw setup) horizon
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
  have componentMap : (keyedComponent setup runtime leaks bounds horizon scheduler source scale
    nonnegative
        le_one ((M).agentAt site) option).map equivalent =
      lateComponent (runtime := runtime) setup (RecoveryLeaks) bounds (Vegas.initialLaw setup)
        horizon (NativeScheduler)
        source scale nonnegative le_one who nativeSite.1 option := by
    have projected := keyedComponent_native_choice setup runtime leaks bounds horizon scheduler
      source scale
      nonnegative le_one site clear nativeSite lifted option
    simp only [PMF.map_comp] at projected
    convert projected using 1; congr 1
  have component := affine (keyedComponent setup runtime leaks bounds horizon scheduler source scale
    nonnegative le_one ((M).agentAt site) option)
  rw [← projection, componentMap] at component
  have pureBound := valueBounded (equivalent.symm choice)
  have mainValue : expect (lateChoice (runtime := runtime) setup (RecoveryLeaks) bounds
    (Vegas.initialLaw setup) horizon
      (NativeScheduler) source who nativeSite.1 option)
      (fun found => value (equivalent.symm found)) =
      value (equivalent.symm choice) := by rw [main, expect_pure]
  have near := abs_expect_slotTrembledChoice_sub_le (runtime := runtime) nonnegative le_one who
    nativeSite.1
    (lateChoice (runtime := runtime) setup (RecoveryLeaks) bounds (Vegas.initialLaw setup) horizon
      (NativeScheduler)
        source
      who nativeSite.1 option)
    (PMF.pure (silenceChoice (runtime := runtime) setup (RecoveryLeaks) bounds (Vegas.initialLaw
      setup) horizon
      (NativeScheduler) who nativeSite.1))
    (slotChoice (runtime := runtime) setup (RecoveryLeaks) bounds (Vegas.initialLaw setup) horizon
      (NativeScheduler)
        source
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
    (keyed : ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
      (KeyedAgent setup runtime leaks bounds horizon scheduler) ((M).agentAt site))
    (assessment : (M).BehavioralAssessment)
    {Outcome : Type*} (observe : (PhaseProtocol).History → Outcome)
    (utility : Outcome → Player → ℝ) {error : ℝ}
    (members : ∀ alternative : PMF (Part setup runtime leaks bounds horizon scheduler slots
        (pool setup runtime leaks bounds horizon scheduler ((M).agentAt site))),
      localGain (2 * horizon + 1) observe utility assessment site
        (alternative.bind (component setup runtime leaks bounds horizon scheduler source scale
          nonnegative
          le_one ((M).agentAt site))) ≤ error)
    (option : LateOption slots) :
    localGain (2 * horizon + 1) observe utility assessment site
      (keyedComponent setup runtime leaks bounds horizon scheduler source scale nonnegative le_one
        ((M).agentAt site) option) ≤ error := by
  let agent := (M).agentAt site
  let best := freeKeyedBest (FreeAgent setup runtime leaks bounds horizon scheduler)
    (KeyedAgent setup runtime leaks bounds horizon scheduler)
    (agentKey setup runtime leaks bounds horizon scheduler)
    (LateOption slots) (fun _ => option)
  let prescribed := prescribedComponent setup runtime leaks bounds horizon scheduler source scale
    nonnegative le_one
  let lateLaw := keyedComponent setup runtime leaks bounds horizon scheduler source (slots :=
    slots) scale
    nonnegative le_one
  have lawEq := freeKeyedComponent_at_not_free
    (freeLaw setup runtime leaks bounds horizon scheduler scale nonnegative le_one) prescribed
      lateLaw best
    keyed.2
  rw [show best (.inr (keyedPool
      (ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
        (KeyedAgent setup runtime leaks bounds horizon scheduler))
      (agentKey setup runtime leaks bounds horizon scheduler) agent)) =
      keyedBest (fun _ => option) (keyedPool
        (ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
          (KeyedAgent setup runtime leaks bounds horizon scheduler))
        (agentKey setup runtime leaks bounds horizon scheduler) agent) from rfl,
    keyedComponent_best_of_keyed prescribed lateLaw (fun _ => option) keyed] at lawEq
  have near := members (PMF.pure (best (pool setup runtime leaks bounds horizon scheduler agent)))
  simp only [PMF.pure_bind] at near
  change localGain (2 * horizon + 1) observe utility assessment site
    (freeKeyedComponent (freeLaw setup runtime leaks bounds horizon scheduler scale nonnegative
      le_one)
      prescribed lateLaw agent (best (pool setup runtime leaks bounds horizon scheduler agent))) ≤
        error
    at near
  rw [lawEq] at near
  exact near

end Vegas.SequentialPhase
