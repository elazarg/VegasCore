/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValuePassage
import Vegas.Pending.PhaseAttemptPassage
import Vegas.Game.PhaseRecoveryValueBelief
import GameTheoryExtensions.Analysis.Protocol.PassageBayes
import Vegas.Game.PhaseClearProfileLocality
import GameTheoryExtensions.Analysis.Protocol.StoppedKernelComparison
import Vegas.Pending.PhaseAttemptEntryStopping
import GameTheoryExtensions.Analysis.Protocol.StoppedComposition

/-! # Actual clear information passage at the stopped attempt boundary -/

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

local instance phaseRecoveryValueStoppedPassagePoolFintype : Fintype Pool := Fintype.ofFinite _

open Classical in
/-- Actual common Bayes conditioning uses the stopped attempt readout itself.
The original global memories and genuine entry posteriors are retained; all
terminal, skipped-entry and exclusion branches stay in the passage law. -/
theorem phaseTimingPlanPolicy_value_bayes_stopped_passage
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
            scheduler owner (members owner (memories owner))) segmentStop entry).map
              (site.ancestor? (N))
    let encountered := (independentProduct priors).bind fun memories =>
      ((N).runBehavioralUntil certificate (fun owner => (menu).restrictPolicy initial horizon
        scheduler owner (members owner (memories owner))) entryStop
          ((menu).protocol initial horizon scheduler).initHistory).bind fun entry =>
            ((N).runBehavioralUntil certificate (fun owner => (menu).restrictPolicy initial horizon
              scheduler owner (members owner (memories owner))) segmentStop entry).map
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
  let memberProfile := fun (memories : Memory) owner =>
    (menu).restrictPolicy initial horizon scheduler
    owner (members owner (memories owner))
  let tail := fun stopped : E.History =>
    ((N).runBehavioralTerminalFrom certificate actual.strategy stopped).map (site.ancestor? (N))
  let oldEncountered := (independentProduct priors).bind fun memories =>
    ((N).runBehavioralUntil certificate (memberProfile memories) entryStop E.initHistory).bind
      fun entry => ((N).runBehavioralUntil certificate (memberProfile memories)
        segmentStop entry).bind tail
  let oldUpdated := ((N).runBehavioralUntil certificate actual.strategy entryStop
    E.initHistory).bind fun entry => (posteriors entry).bind fun memories =>
      ((N).runBehavioralUntil certificate (memberProfile memories) segmentStop entry).bind tail
  have original := phaseTimingPlanPolicy_value_bayes_entry_passage setup mode runtime leaks bounds
    runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed finite weights
      noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded actual assembled
        actualMixed bayes certificate target who site
  change oldEncountered = oldUpdated ∧
    (oldEncountered.map Option.isSome) true = (N).informationMass actual.strategy who site ∧
      0 < (oldEncountered.map Option.isSome) true ∧
      (actual.belief who site).map some =
        fiberPosterior oldEncountered Option.isSome true at original
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state supported
    obtain ⟨input, _positive, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered runtimePlan input
  have tailGone (profile continuation : ∀ owner, (N).BehavioralPolicy owner)
      (entry : E.History)
      (supported : entry ∈ ((N).runBehavioralUntil certificate profile entryStop
        E.initHistory).support) :
      ((N).runBehavioralUntil certificate continuation segmentStop entry).bind tail =
        ((N).runBehavioralUntil certificate continuation segmentStop entry).map
          (site.ancestor? (N)) := by
    by_cases terminal : E.terminal entry.state
    · have ended : (N).runBehavioralTerminalFrom certificate actual.strategy entry =
          PMF.pure entry := E.randomizedBackwardLaw_of_terminal terminal
      rw [(N).runBehavioralUntil_of_terminal certificate continuation terminal, PMF.pure_bind]
      exact congrArg (fun law => law.map (site.ancestor? (N))) ended
    have entryStatus := ((N).mem_support_runBehavioralUntil certificate profile entryStop
      E.initHistory entry supported).resolve_right terminal
    rcases entry with ⟨state, trace⟩
    cases state with
    | none => exact False.elim entryStatus
    | some control =>
      have entered : control.execution.application.current.excluded ≠ ∅ ∨
          control.execution.application.attempt = view.application.2.attempt := by
        simpa only [entryStop, phaseAttemptEntryStop, address] using entryStatus
      have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon
        scheduler initialized ((menu).toRawTrace initial horizon scheduler trace)
      have gone := phase_attempt_stopped_ancestor runtime leaks (menu) initial horizon scheduler
        initialized certificate continuation actual.strategy site
          ((menu).decisionInformationAntichain initial horizon scheduler who site) past view
            observed clear control trace ordered entered
      convert gone using 1 <;> congr 2
      all_goals
        funext history
        rcases history with ⟨state, historyTrace⟩
        cases state <;> simp only [segmentStop, address]
  have first : oldEncountered = encountered := by
    apply bind_congr_on_support (independentProduct priors)
    intro memories _supported
    apply bind_congr_on_support _
    intro entry supported
    exact tailGone (memberProfile memories) (memberProfile memories) entry supported
  have second : oldUpdated = updatedEncountered := by
    apply bind_congr_on_support _
    intro entry supported
    apply bind_congr_on_support (posteriors entry)
    intro memories _possible
    exact tailGone actual.strategy (memberProfile memories) entry supported
  rw [first, second] at original
  exact original

end Vegas
