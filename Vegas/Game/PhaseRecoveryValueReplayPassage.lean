/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueEntryBelief
import Interaction.ReactiveRecallReplay
import Vegas.Pending.PhaseAttemptPassage
import Vegas.Game.PhaseRecoveryValueBelief
import GameTheoryExtensions.Analysis.Protocol.PassageBayes
import Vegas.Game.PhaseClearProfileLocality
import GameTheoryExtensions.Analysis.Protocol.StoppedKernelComparison
import Vegas.Pending.PhaseAttemptEntryStopping
import GameTheoryExtensions.Analysis.Protocol.StoppedComposition

/-! # Focal replay retains the actual selected immutable entry law -/

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

local instance phaseRecoveryValueReplayPassagePoolFintype : Fintype Pool := Fintype.ofFinite _

open Classical in
private theorem value_intervention_until_joint
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
    (focal : Player) (intervention : (N).BehavioralPolicy focal)
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
    let selected := Function.update actual.strategy focal intervention
    let changed := Function.update members focal (fun _ =>
      (app).decodePolicy ((menu).embedPolicy initial horizon scheduler focal intervention))
    let posteriors := fun history : ((menu).protocol initial horizon scheduler).History =>
      independentProduct (fun who => ((app).policyMixture (priors who) (changed who)).posterior
        ((app).recallAt who history.state))
    (posteriors start).bind (fun memories =>
      ((N).runBehavioralUntil certificate (fun who => (menu).restrictPolicy initial horizon
        scheduler who (changed who (memories who))) stopped start).map
          (fun final => (final, memories))) =
      ((N).runBehavioralUntil certificate selected stopped start).bind fun final =>
        (posteriors final).map (Prod.mk final) := by
  intro priors members selected changed posteriors
  let first := fun who => (menu).restrictPolicy initial horizon scheduler who
    (((app).policyMixture (priors who) (changed who)).policy)
  let baseProfile := fun who => (menu).restrictPolicy initial horizon scheduler who
    (((app).policyMixture (priors who) (members who)).policy)
  have covered : ∀ who memory past view action, action ∈ (changed who memory past view).support →
      action ∈ (menu).actions who past view := by
    intro who memory past view action supported
    by_cases same : who = focal
    · subst who
      simp only [changed, Function.update_self] at supported
      exact (menu).decode_embedPolicy_covered initial horizon scheduler focal intervention
        past view action supported
    · simp only [changed, Function.update_of_ne same] at supported
      exact phaseTimingPlanPolicy_covered setup mode runtime leaks bounds initial horizon scheduler
        bound fallback wellFormed
          (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
            noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
              past view action supported
  have firstEq : first = Function.update baseProfile focal intervention := by
    funext who
    by_cases same : who = focal
    · subst who
      rw [Function.update_self]
      change (menu).restrictPolicy initial horizon scheduler focal
        (((app).policyMixture (priors focal) (changed focal)).policy) = intervention
      have constant : ((app).policyMixture (priors focal) (changed focal)).policy =
          (app).decodePolicy ((menu).embedPolicy initial horizon scheduler focal intervention) := by
        funext past view
        rw [ReactiveApplication.policyMixture_policy]
        simp only [changed, Function.update_self, PMF.bind_const]
      rw [constant, (menu).restrict_decode_embedPolicy initial horizon scheduler focal intervention]
    · simp only [first, changed, Function.update_of_ne same, baseProfile]
  have baseAgree := phaseTimingPlanPolicy_value_clear_profile_agreement setup mode runtime leaks
    bounds runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed finite
      weights noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded actual
        assembled
  change ∀ who (site : (N).InformationSite who),
    ¬ PhasePublicExclusion setup mode runtime leaks site.1 →
      baseProfile who site.1 = actual.strategy who site.1 at baseAgree
  have agree : ∀ who (site : (N).InformationSite who),
      ¬ PhasePublicExclusion setup mode runtime leaks site.1 →
        first who site.1 = selected who site.1 := by
    intro who site clear
    rw [firstEq]
    by_cases same : who = focal
    · subst who
      simp only [selected, Function.update_self]
    · simp only [selected, Function.update_of_ne same]
      exact baseAgree who site clear
  have callbacks (history : ((menu).protocol initial horizon scheduler).History)
      (going : ¬ stopped history) (_running : ¬ ((menu).protocol initial horizon scheduler).terminal
        history.state) :
      ∀ who, first who ((N).infoOf who history.trace) =
        selected who ((N).infoOf who history.trace) := by
    rcases history with ⟨state, trace⟩
    cases state with
    | none =>
        intro who
        exact (N).behavioral_eq_of_not_active (first who) (selected who) trace
          (by simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor])
    | some control =>
        intro who
        exact phase_clear_profile_queries setup mode runtime leaks bounds initial horizon scheduler
          first selected agree control trace (clearAt control trace going) who _
            ((N).infoOf_mem_queriedInfos who ⟨some control, trace⟩)
  let E := (menu).protocol initial horizon scheduler
  have step : ∀ left right : E.History, left = right → ¬ stopped left →
      ¬ E.terminal left.state →
      ∃ joint : PMF (E.History × E.History),
        joint.map Prod.fst = (N).runBehavioralFrom first 1 left ∧
        joint.map Prod.snd = (N).runBehavioralFrom selected 1 right ∧
        ∀ next ∈ joint.support, next.1 = next.2 := by
    intro history _ same going running
    subst same
    have answers := (N).behavioralJoint_congr history.trace running
      (callbacks history going running)
    have laws : (N).runBehavioralFrom first 1 history =
        (N).runBehavioralFrom selected 1 history := by
      rw [(N).runBehavioralFrom_succ_of_not_terminal first 0 running,
        (N).runBehavioralFrom_succ_of_not_terminal selected 0 running, answers]
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
    first selected stopped stopped id id Eq (by rintro _ _ rfl; rfl)
      (by rintro _ _ rfl _; rfl) step start start rfl
  have law : (N).runBehavioralUntil certificate first stopped start =
      (N).runBehavioralUntil certificate selected stopped start := by
    simpa only [PMF.map_id] using compared
  have joint := (menu).runUntil_policyMixtures_joint initial horizon scheduler certificate priors
    changed covered stopped start
  exact joint.trans (congrArg (fun law => law.bind fun final =>
    (posteriors final).map (Prod.mk final)) law)

open Classical in
/-- The actual common belief can use literal focal replay while retaining the
selected profile's genuine entry tilt and ORIGINAL foreign private members.
Its exact stopped denominator is positive; the common own-reach factor is
derived rather than replaced by a uniform lower bound. -/
theorem phaseTimingPlanPolicy_value_replay_bayes_passage
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
    (target : CommitAttemptId) (who : Player) (site : (N).InformationSite who)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (observed : site.1 = some (past, view)) (clear : view.application.2.excluded = ∅)
    (address : view.application.2.attempt = target) :
    let replay := (menu).recallReplayPolicy initial horizon scheduler who past (actual.strategy who)
    let selected := Function.update actual.strategy who replay
    let priors := fun who => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).map (Prod.mk plan)
    let members := fun who memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    let changed := Function.update members who (fun _ =>
      (app).decodePolicy ((menu).embedPolicy initial horizon scheduler who replay))
    let posteriors := fun history : ((menu).protocol initial horizon scheduler).History =>
      independentProduct (fun who => ((app).policyMixture (priors who) (changed who)).posterior
        ((app).recallAt who history.state))
    let entryStop := fun history : ((menu).protocol initial horizon scheduler).History =>
      phaseAttemptEntryStop runtime leaks target history.state
    let segmentStop := fun history : ((menu).protocol initial horizon scheduler).History =>
      match history.state with
      | none => False
      | some current => current.execution.application.current.excluded ≠ ∅ ∨
          current.execution.application.attempt ≠ target ∨ (N).infoOf who history.trace = site.1
    let updatedEncountered := ((N).runBehavioralUntil certificate selected entryStop
      ((menu).protocol initial horizon scheduler).initHistory).bind fun entry =>
        (posteriors entry).bind fun memories =>
          ((N).runBehavioralUntil certificate (fun owner => (menu).restrictPolicy initial horizon
            scheduler owner (changed owner (memories owner))) segmentStop entry).map
              (site.ancestor? (N))
    let encountered := (independentProduct priors).bind fun memories =>
      ((N).runBehavioralUntil certificate (fun owner => (menu).restrictPolicy initial horizon
        scheduler owner (changed owner (memories owner))) entryStop
          ((menu).protocol initial horizon scheduler).initHistory).bind fun entry =>
            ((N).runBehavioralUntil certificate (fun owner => (menu).restrictPolicy initial horizon
              scheduler owner (changed owner (memories owner))) segmentStop entry).map
              (site.ancestor? (N))
    ∃ _selectedPositive : 0 < (N).informationMass selected who site,
      (independentProduct priors).bind (fun memories =>
        ((N).runBehavioralUntil certificate (fun owner => (menu).restrictPolicy initial horizon
          scheduler owner (changed owner (memories owner))) entryStop
            ((menu).protocol initial horizon scheduler).initHistory).map
              (fun entry => (entry, memories))) =
        ((N).runBehavioralUntil certificate selected entryStop
          ((menu).protocol initial horizon scheduler).initHistory).bind
            (fun entry => (posteriors entry).map (Prod.mk entry)) ∧
      encountered = updatedEncountered ∧
      (encountered.map Option.isSome) true = (N).informationMass selected who site ∧
      (actual.belief who site).map some =
        fiberPosterior encountered Option.isSome true ∧
      ∃ ownFactor : ℝ, 0 < ownFactor ∧
        ((N).informationMass actual.strategy who site).toReal =
          ownFactor * ((encountered.map Option.isSome) true).toReal := by
  intro replay selected priors members changed posteriors entryStop segmentStop
    updatedEncountered encountered
  let E := (menu).protocol initial horizon scheduler
  let Memory := (owner : Player) → ((p : Pool) → Parts p) ×
    (setup.informationModel (CommitmentInterface.forfeiture setup.program)).Policy owner
  let memberProfile := fun (memories : Memory) owner =>
    (menu).restrictPolicy initial horizon scheduler owner (changed owner (memories owner))
  have entryClear : ∀ control trace, ¬ entryStop ⟨some control, trace⟩ →
      control.execution.application.current.excluded = ∅ := by
    intro control trace going
    by_contra excluded
    exact going (Or.inl excluded)
  have segmentClear : ∀ control trace, ¬ segmentStop ⟨some control, trace⟩ →
      control.execution.application.current.excluded = ∅ := by
    intro control trace going
    by_contra excluded
    exact going (Or.inl excluded)
  have entryJoint := value_intervention_until_joint setup mode runtime leaks bounds runtimePlan
    horizon scheduler bound maximal fallback wellFormed assessment mixed finite weights noise
      noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded actual assembled who
        replay certificate entryStop entryClear E.initHistory
  change (independentProduct priors).bind (fun memories =>
    ((N).runBehavioralUntil certificate (memberProfile memories) entryStop E.initHistory).map
      (fun entry => (entry, memories))) =
        ((N).runBehavioralUntil certificate selected entryStop E.initHistory).bind
          (fun entry => (posteriors entry).map (Prod.mk entry)) at entryJoint
  let continuation := fun row : E.History × Memory =>
    ((N).runBehavioralUntil certificate (memberProfile row.2) segmentStop row.1).map
      (site.ancestor? (N))
  have initialized : encountered = updatedEncountered := by
    have joint := congrArg (fun law => law.bind continuation) entryJoint
    simpa only [PMF.bind_bind, PMF.bind_map, Function.comp_def, continuation] using joint
  have segment (entry : E.History) :
      (posteriors entry).bind (fun memories =>
        (N).runBehavioralUntil certificate (memberProfile memories) segmentStop entry) =
        (N).runBehavioralUntil certificate selected segmentStop entry := by
    have joint := value_intervention_until_joint setup mode runtime leaks bounds runtimePlan
      horizon scheduler bound maximal fallback wellFormed assessment mixed finite weights noise
        noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded actual assembled who
          replay certificate segmentStop segmentClear entry
    have marginal := congrArg (PMF.map Prod.fst) joint
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at marginal
    change ((posteriors entry).bind fun memories =>
      ((N).runBehavioralUntil certificate (memberProfile memories) segmentStop entry).map id) =
        ((N).runBehavioralUntil certificate selected segmentStop entry).bind
          (fun final => (posteriors final).map (Function.const _ final)) at marginal
    simpa only [PMF.map_id, PMF.map_const, PMF.bind_pure] using marginal
  have initialOrdered : ∀ state ∈ (initial).support, state.Ordered := by
    intro state supported
    obtain ⟨input, _positive, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered runtimePlan input
  have tailGone (entry : E.History)
      (supported : entry ∈ ((N).runBehavioralUntil certificate selected entryStop
        E.initHistory).support) (memories : Memory) :
      ((N).runBehavioralUntil certificate (memberProfile memories) segmentStop entry).bind
        (fun stopped => ((N).runBehavioralTerminalFrom certificate selected stopped).map
          (site.ancestor? (N))) =
        ((N).runBehavioralUntil certificate (memberProfile memories) segmentStop entry).map
          (site.ancestor? (N)) := by
    by_cases terminal : E.terminal entry.state
    · have ended : (N).runBehavioralTerminalFrom certificate selected entry =
          PMF.pure entry := E.randomizedBackwardLaw_of_terminal terminal
      rw [(N).runBehavioralUntil_of_terminal certificate (memberProfile memories) terminal,
        PMF.pure_bind, ended]
    have entryStatus := ((N).mem_support_runBehavioralUntil certificate selected entryStop
      E.initHistory entry supported).resolve_right terminal
    rcases entry with ⟨state, trace⟩
    cases state with
    | none => exact False.elim entryStatus
    | some control =>
      have entered : control.execution.application.current.excluded ≠ ∅ ∨
          control.execution.application.attempt = view.application.2.attempt := by
        simpa only [entryStop, phaseAttemptEntryStop, address] using entryStatus
      have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon
        scheduler initialOrdered ((menu).toRawTrace initial horizon scheduler trace)
      have gone := phase_attempt_stopped_ancestor runtime leaks (menu) initial horizon scheduler
        initialOrdered certificate (memberProfile memories) selected site
          ((menu).decisionInformationAntichain initial horizon scheduler who site) past view
            observed clear control trace ordered entered
      convert gone using 1 <;> congr 2
      all_goals
        funext history
        rcases history with ⟨state, historyTrace⟩
        cases state <;> simp only [segmentStop, address]
  have terminal : ((N).runBehavioralTerminalFrom certificate selected E.initHistory).map
      (site.ancestor? (N)) = updatedEncountered := by
    rw [(N).runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate selected
      entryStop E.initHistory, PMF.map_bind]
    apply bind_congr_on_support _
    intro entry supported
    rw [(N).runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate selected
      segmentStop entry, PMF.map_bind, ← segment entry, PMF.bind_bind]
    apply bind_congr_on_support (posteriors entry)
    intro memories _possible
    exact tailGone entry supported memories
  have positive := (N).informationMass_pos_of_fullSupport actual.strategy actualMixed who site
  obtain ⟨reference, _reached⟩ := (InformationModel.informationMass_pos_iff (N)
    actual.strategy who site).mp positive
  obtain ⟨selectedPositive, sameBelief, ownOne⟩ := (menu).bayesBelief_eq_recallReplay initial
    horizon scheduler actual.strategy who site positive reference past view observed
  change 0 < (N).informationMass selected who site at selectedPositive
  have antichain := (menu).decisionInformationAntichain initial horizon scheduler who site
  have belief := (BehavioralAssessment.isBayesConsistentAt_iff (N) actual who site antichain
    positive).mp (bayes who site positive)
  have mass : (encountered.map Option.isSome) true = (N).informationMass selected who site := by
    rw [initialized, ← terminal]
    exact site.terminal_ancestor_passage (N) antichain certificate selected
  refine ⟨selectedPositive, entryJoint, initialized, mass, ?_, ?_⟩
  · rw [belief, sameBelief]
    exact (site.bayesBelief_eq_conditional_ancestor (N) antichain certificate selected
      selectedPositive).trans (congrArg (fun law => fiberPosterior law Option.isSome true)
        (terminal.trans initialized.symm))
  · obtain ⟨ownFactor, common⟩ := (menu).commonPlayerReachAt initial horizon scheduler
      actual.strategy who site
    refine ⟨ownFactor, (N).commonPlayerReach_pos ownFactor common positive, ?_⟩
    have off : ∀ other, other ≠ who → actual.strategy other = selected other := by
      intro other different
      exact (Function.update_of_ne different _ _).symm
    rw [mass]
    have factor (profile : ∀ owner, (N).BehavioralPolicy owner) (reach : ℝ)
        (same : ∀ history : (N).InformationHistory who site.1,
          (N).playerReachProbability profile who history.1.trace = reach) :
        ((N).informationMass profile who site).toReal = reach *
          ∑' history : (N).InformationHistory who site.1,
            (N).counterfactualReachProbability profile who history.1.trace := by
      unfold informationMass
      rw [ENNReal.tsum_toReal_eq (f := fun history : (N).InformationHistory who site.1 =>
        (N).historyReachWeight profile history.1) fun history => PMF.apply_ne_top _ _,
        ← tsum_mul_left]
      exact tsum_congr fun history => by
        rw [(N).historyReachProbability_eq_player_mul_counterfactual profile who history.1.trace,
          same history]
    have selectedMass := factor selected 1 ownOne
    simp only [one_mul] at selectedMass
    rw [factor actual.strategy ownFactor common, selectedMass]
    apply congrArg (ownFactor * ·)
    exact tsum_congr fun history =>
      (N).counterfactualReachProbability_eq_of_eq_off off history.1.trace

end Vegas
