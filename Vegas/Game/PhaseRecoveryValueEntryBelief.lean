/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueEntry
import Vegas.Game.PhaseClearProfileLocality
import GameTheoryExtensions.Analysis.Protocol.StoppedKernelComparison
import Vegas.Pending.PhaseAttemptEntryStopping
import GameTheoryExtensions.Analysis.Protocol.StoppedComposition

/-! # Original memory at the first actual full attempt entry -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (runtimePlan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)) horizon
      scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)) horizon
      scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "initial" => PMF.map (PhaseRuntimeState.initial runtimePlan)
  (PMF.map encodeInputs setup.initialLaw)
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
  (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent => PhaseUnprotected runtime leaks bound
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound

local instance phaseRecoveryValueEntryBeliefPoolFintype : Fintype Pool := Fintype.ofFinite _

open Classical in
/-- The SAME actual common profile reaches an exact full attempt entry
with the ORIGINAL global source-policy and full owner-plan memory joint.
Only its genuine clear-site recipe is fixed; post-exclusion choices may differ. -/
theorem phaseTimingPlanPolicy_value_common_attempt_entry_joint
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (actual : (N).BehavioralAssessment)
    (assembled : ∀ who (site : (N).InformationSite who),
      ¬ PhasePublicExclusion setup mode runtime leaks site.1 →
      actual.strategy who site.1 = ((N).agentBehavior (N).playedInformation fallback
        (fun agent => (weights (pool agent)).bind
          (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
            wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
              slotBounded agent))) who site.1)
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
    (target : CommitAttemptId) :
    let priors := fun who => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).map (Prod.mk plan)
    let members := fun who memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
      phaseAttemptEntryStop runtime leaks target history.state
    let posteriors := fun history : ((menu).protocol initial horizon scheduler).History =>
      independentProduct (fun who => ((app).policyMixture (priors who) (members who)).posterior
        ((app).recallAt who history.state))
    (independentProduct priors).bind (fun memories =>
      ((N).runBehavioralUntil certificate (fun who => (menu).restrictPolicy initial horizon
        scheduler who (members who (memories who))) stopped
          ((menu).protocol initial horizon scheduler).initHistory).map
            (fun final => (final, memories))) =
      ((N).runBehavioralUntil certificate actual.strategy stopped
        ((menu).protocol initial horizon scheduler).initHistory).bind
          (fun final => (posteriors final).map (Prod.mk final)) := by
  intro priors members stopped posteriors
  let profile := (N).agentBehavior (N).playedInformation fallback (fun agent =>
    (weights (pool agent)).bind (phaseTimingComponent setup mode runtime leaks bounds initial
      horizon scheduler bound wellFormed assessment noise noiseNonnegative noiseBounded
        slotWeight slotNonnegative slotBounded agent))
  let E := (menu).protocol initial horizon scheduler
  have agree : ∀ who (site : (N).InformationSite who),
      ¬ PhasePublicExclusion setup mode runtime leaks site.1 →
        profile who site.1 = actual.strategy who site.1 := by
    intro who site unflagged
    exact (assembled who site unflagged).symm
  have callbacks (history : E.History) (going : ¬ stopped history)
      (_running : ¬ E.terminal history.state) :
      ∀ who, profile who ((N).infoOf who history.trace) =
        actual.strategy who ((N).infoOf who history.trace) := by
    rcases history with ⟨state, trace⟩
    cases state with
    | none =>
        intro who
        exact (N).behavioral_eq_of_not_active (profile who) (actual.strategy who) trace
          (by simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor])
    | some control =>
        have clear : control.execution.application.current.excluded = ∅ := by
          by_contra excluded
          exact going (Or.inl excluded)
        intro who
        exact phase_clear_profile_queries setup mode runtime leaks bounds initial horizon scheduler
          profile actual.strategy agree control trace clear who _
            ((N).infoOf_mem_queriedInfos who ⟨some control, trace⟩)
  have step : ∀ left right : E.History, left = right → ¬ stopped left →
      ¬ E.terminal left.state →
      ∃ joint : PMF (E.History × E.History),
        joint.map Prod.fst = (N).runBehavioralFrom profile 1 left ∧
        joint.map Prod.snd = (N).runBehavioralFrom actual.strategy 1 right ∧
        ∀ next ∈ joint.support, next.1 = next.2 := by
    intro history _ same going running
    subst same
    have answers := (N).behavioralJoint_congr history.trace running
      (callbacks history going running)
    have laws : (N).runBehavioralFrom profile 1 history =
        (N).runBehavioralFrom actual.strategy 1 history := by
      rw [(N).runBehavioralFrom_succ_of_not_terminal profile 0 running,
        (N).runBehavioralFrom_succ_of_not_terminal actual.strategy 0 running, answers]
      rfl
    refine ⟨((N).runBehavioralFrom profile 1 history).map (fun next => (next, next)), ?_, ?_, ?_⟩
    · rw [PMF.map_comp]
      exact PMF.map_id _
    · rw [PMF.map_comp]
      exact (PMF.map_id _).trans laws
    · intro pair member
      obtain ⟨next, _supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp member
      rfl
  have compared := (N).runBehavioralUntil_map_eq_of_paired_steps (N) certificate certificate
    profile actual.strategy stopped stopped id id Eq (by rintro _ _ rfl; rfl)
      (by rintro _ _ rfl _; rfl) step E.initHistory E.initHistory rfl
  have law : (N).runBehavioralUntil certificate profile stopped E.initHistory =
      (N).runBehavioralUntil certificate actual.strategy stopped E.initHistory := by
    simpa only [PMF.map_id] using compared
  have original := (phaseTimingPlanPolicy_value_attempt_entry_joint setup mode runtime leaks bounds
    runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed finite weights
      noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded certificate
        target).1
  exact original.trans (congrArg (fun law => law.bind
    (fun final => (posteriors final).map (Prod.mk final))) law)

end Vegas
