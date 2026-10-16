/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueEntryBelief
import Vegas.Game.PhaseRecoveryValueBelief
import GameTheoryExtensions.Analysis.Protocol.PassageBayes
import Vegas.Game.PhaseClearProfileLocality
import GameTheoryExtensions.Analysis.Protocol.StoppedKernelComparison
import Vegas.Pending.PhaseAttemptEntryStopping
import GameTheoryExtensions.Analysis.Protocol.StoppedComposition

/-! # Actual native Bayes passage through original immutable entry memories -/

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

local instance phaseRecoveryValuePassagePoolFintype : Fintype Pool := Fintype.ofFinite _

open Classical in
private theorem value_common_until
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
    (stopped : ((menu).protocol initial horizon scheduler).History → Prop)
    (clearAt : ∀ control trace, ¬ stopped ⟨some control, trace⟩ →
      control.execution.application.current.excluded = ∅)
    (start : ((menu).protocol initial horizon scheduler).History) :
    let priors := fun who => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).map (Prod.mk plan)
    let members := fun who memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    let posteriors := fun history : ((menu).protocol initial horizon scheduler).History =>
      independentProduct (fun who => ((app).policyMixture (priors who) (members who)).posterior
        ((app).recallAt who history.state))
    (posteriors start).bind (fun memories =>
      (N).runBehavioralUntil certificate (fun who => (menu).restrictPolicy initial horizon
        scheduler who (members who (memories who))) stopped start) =
      (N).runBehavioralUntil certificate actual.strategy stopped start := by
  intro priors members posteriors
  let E := (menu).protocol initial horizon scheduler
  let first := fun who => (menu).restrictPolicy initial horizon scheduler who
    (((app).policyMixture (priors who) (members who)).policy)
  have covered : ∀ who memory past view action, action ∈ (members who memory past view).support →
      action ∈ (menu).actions who past view := by
    intro who memory past view action supported
    exact phaseTimingPlanPolicy_covered setup mode runtime leaks bounds initial horizon scheduler
      bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
            past view action supported
  have mixture := (menu).runUntil_policyMixtures initial horizon scheduler certificate priors
    members covered stopped start
  have agree := phaseTimingPlanPolicy_value_clear_profile_agreement setup mode runtime leaks bounds
    runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed finite weights
      noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded actual assembled
  change ∀ who (site : (N).InformationSite who),
    ¬ PhasePublicExclusion setup mode runtime leaks site.1 →
      first who site.1 = actual.strategy who site.1 at agree
  have callbacks (history : E.History) (going : ¬ stopped history)
      (_running : ¬ E.terminal history.state) :
      ∀ who, first who ((N).infoOf who history.trace) =
        actual.strategy who ((N).infoOf who history.trace) := by
    rcases history with ⟨state, trace⟩
    cases state with
    | none =>
        intro who
        exact (N).behavioral_eq_of_not_active (first who) (actual.strategy who) trace
          (by simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor])
    | some control =>
        intro who
        exact phase_clear_profile_queries setup mode runtime leaks bounds initial horizon scheduler
          first actual.strategy agree control trace (clearAt control trace going) who _
            ((N).infoOf_mem_queriedInfos who ⟨some control, trace⟩)
  have step : ∀ left right : E.History, left = right → ¬ stopped left →
      ¬ E.terminal left.state →
      ∃ joint : PMF (E.History × E.History),
        joint.map Prod.fst = (N).runBehavioralFrom first 1 left ∧
        joint.map Prod.snd = (N).runBehavioralFrom actual.strategy 1 right ∧
        ∀ next ∈ joint.support, next.1 = next.2 := by
    intro history _ same going running
    subst same
    have answers := (N).behavioralJoint_congr history.trace running
      (callbacks history going running)
    have laws : (N).runBehavioralFrom first 1 history =
        (N).runBehavioralFrom actual.strategy 1 history := by
      rw [(N).runBehavioralFrom_succ_of_not_terminal first 0 running,
        (N).runBehavioralFrom_succ_of_not_terminal actual.strategy 0 running, answers]
      rfl
    refine ⟨((N).runBehavioralFrom first 1 history).map (fun next => (next, next)), ?_, ?_, ?_⟩
    · rw [PMF.map_comp]
      exact PMF.map_id _
    · rw [PMF.map_comp]
      exact (PMF.map_id _).trans laws
    · intro pair member
      obtain ⟨next, _supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp member
      rfl
  have compared := (N).runBehavioralUntil_map_eq_of_paired_steps (N) certificate certificate
    first actual.strategy stopped stopped id id Eq (by rintro _ _ rfl; rfl)
      (by rintro _ _ rfl _; rfl) step start start rfl
  exact mixture.trans (by simpa only [PMF.map_id] using compared)

open Classical in
/-- The actual common Bayes belief is genuine passage through the ORIGINAL full-ID
entry law and its recall-updated immutable source-policy/owner-plan members.
The same actual terminal tail remains explicit on all stopped exits; no reset,
skipped entry, public failure or original source-failure mass is discarded. -/
theorem phaseTimingPlanPolicy_value_bayes_entry_passage
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
    (actualMixed : actual.IsFullyMixed)
    (bayes : BehavioralAssessment.IsBayesConsistent (N) actual
      ((menu).decisionInformationAntichain initial horizon scheduler))
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
    (target : CommitAttemptId) (who : Player) (site : (N).InformationSite who) :
    let priors := fun who => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).map (Prod.mk plan)
    let members := fun who memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    let posteriors := fun history : ((menu).protocol initial horizon scheduler).History =>
      independentProduct (fun who => ((app).policyMixture (priors who) (members who)).posterior
        ((app).recallAt who history.state))
    let entryStop := fun history : ((menu).protocol initial horizon scheduler).History =>
      phaseAttemptEntryStop runtime leaks target history.state
    let segmentStop := fun history : ((menu).protocol initial horizon scheduler).History =>
      match history.state with
      | none => False
      | some current => current.execution.application.current.excluded ≠ ∅ ∨
          current.execution.application.attempt ≠ target ∨ (N).infoOf who history.trace = site.1
    let updatedEncountered := ((N).runBehavioralUntil certificate actual.strategy entryStop
      ((menu).protocol initial horizon scheduler).initHistory).bind fun entry =>
        (posteriors entry).bind fun memories =>
          ((N).runBehavioralUntil certificate (fun owner => (menu).restrictPolicy initial horizon
            scheduler owner (members owner (memories owner))) segmentStop entry).bind fun stopped =>
              ((N).runBehavioralTerminalFrom certificate actual.strategy stopped).map
                (site.ancestor? (N))
    let encountered := (independentProduct priors).bind fun memories =>
      ((N).runBehavioralUntil certificate (fun owner => (menu).restrictPolicy initial horizon
        scheduler owner (members owner (memories owner))) entryStop
          ((menu).protocol initial horizon scheduler).initHistory).bind fun entry =>
            ((N).runBehavioralUntil certificate (fun owner => (menu).restrictPolicy initial horizon
              scheduler owner (members owner (memories owner))) segmentStop entry).bind
                fun stopped =>
                ((N).runBehavioralTerminalFrom certificate actual.strategy stopped).map
                  (site.ancestor? (N))
    encountered = updatedEncountered ∧
      (encountered.map Option.isSome) true = (N).informationMass actual.strategy who site ∧
      0 < (encountered.map Option.isSome) true ∧
      (actual.belief who site).map some =
        fiberPosterior encountered Option.isSome true := by
  intro priors members posteriors entryStop segmentStop updatedEncountered encountered
  let E := (menu).protocol initial horizon scheduler
  let Memory := (owner : Player) → ((p : Pool) → Parts p) ×
    (setup.informationModel (CommitmentInterface.forfeiture setup.program)).Policy owner
  let continuation := fun row : E.History × Memory =>
    ((N).runBehavioralUntil certificate (fun owner => (menu).restrictPolicy initial horizon
      scheduler owner (members owner (row.2 owner))) segmentStop row.1).bind fun stopped =>
        ((N).runBehavioralTerminalFrom certificate actual.strategy stopped).map
          (site.ancestor? (N))
  have entryJoint := phaseTimingPlanPolicy_value_common_attempt_entry_joint setup mode runtime
    leaks bounds runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed
      finite weights noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
        actual assembled certificate target
  have initialized : encountered = updatedEncountered := by
    have joint := congrArg (fun law => law.bind continuation) entryJoint
    simpa only [PMF.bind_bind, PMF.bind_map, Function.comp_def, continuation] using joint
  have clearAt : ∀ control trace, ¬ segmentStop ⟨some control, trace⟩ →
      control.execution.application.current.excluded = ∅ := by
    intro control trace going
    by_contra excluded
    exact going (Or.inl excluded)
  have segment (entry : E.History) := value_common_until setup mode runtime leaks bounds
    runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed finite weights
      noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded actual assembled
        certificate segmentStop clearAt entry
  have terminal : ((N).runBehavioralTerminalFrom certificate actual.strategy E.initHistory).map
      (site.ancestor? (N)) = updatedEncountered := by
    rw [(N).runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate actual.strategy
      entryStop E.initHistory, PMF.map_bind]
    apply congrArg (PMF.bind _)
    funext entry
    rw [(N).runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate actual.strategy
      segmentStop entry, PMF.map_bind, ← segment entry]
    simp only [PMF.bind_bind]
    rfl
  have positive := (N).informationMass_pos_of_fullSupport actual.strategy actualMixed who site
  have antichain := (menu).decisionInformationAntichain initial horizon scheduler who site
  have belief := (BehavioralAssessment.isBayesConsistentAt_iff (N) actual who site
    antichain positive).mp (bayes who site positive)
  have passage := site.bayesBelief_eq_conditional_ancestor (N) antichain certificate
    actual.strategy positive
  have mass : (encountered.map Option.isSome) true =
      (N).informationMass actual.strategy who site := by
    rw [initialized, ← terminal]
    exact site.terminal_ancestor_passage (N) antichain certificate actual.strategy
  refine ⟨initialized, mass, ?_, ?_⟩
  · rw [mass]
    exact positive
  · rw [belief]
    exact passage.trans (congrArg (fun law => fiberPosterior law Option.isSome true)
      (terminal.trans initialized.symm))

end Vegas
