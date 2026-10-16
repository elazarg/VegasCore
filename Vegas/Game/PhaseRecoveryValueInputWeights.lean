/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueReplayPassage
import Vegas.Pending.PhaseAttemptFirstPassage
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

local instance phaseRecoveryValueInputWeightsPoolFintype : Fintype Pool := Fintype.ofFinite _

open Classical in
/-- Actual common Bayes atoms are the SAME selected original-memory entry law
followed by actual stopped input atoms, divided by its derived positive mass.
The actual common/selected own-reach factor and all entry tilt are retained. -/
theorem phaseTimingPlanPolicy_value_replay_input_weights
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
    (who : Player) (site : (N).InformationSite who)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (observed : site.1 = some (past, view)) (clear : view.application.2.excluded = ∅) :
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
      phaseAttemptEntryStop runtime leaks view.application.2.attempt history.state
    let segmentStop := fun history : ((menu).protocol initial horizon scheduler).History =>
      match history.state with
      | none => False
      | some current => current.execution.application.current.excluded ≠ ∅ ∨
          current.execution.application.attempt ≠ view.application.2.attempt ∨
          (N).infoOf who history.trace = site.1
    let hit := ((N).runBehavioralUntil certificate selected entryStop
      ((menu).protocol initial horizon scheduler).initHistory).bind fun entry =>
        (posteriors entry).bind fun memories =>
          (N).runBehavioralUntil certificate (fun owner => (menu).restrictPolicy initial horizon
            scheduler owner (changed owner (memories owner))) segmentStop entry
    ∃ ownFactor : ℝ, 0 < ownFactor ∧ 0 < (N).informationMass selected who site ∧
      ((N).informationMass actual.strategy who site).toReal =
        ownFactor * ((N).informationMass selected who site).toReal ∧
      (∑' atSite : (N).InformationHistory who site.1, hit atSite.1) =
        (N).informationMass selected who site ∧
      ∀ atSite : (N).InformationHistory who site.1,
        actual.belief who site atSite = hit atSite.1 / (N).informationMass selected who site := by
  intro replay selected priors members changed posteriors entryStop segmentStop hit
  let E := (menu).protocol initial horizon scheduler
  let Memory := (owner : Player) → ((p : Pool) → Parts p) ×
    (setup.informationModel (CommitmentInterface.forfeiture setup.program)).Policy owner
  let memberProfile := fun (memories : Memory) owner =>
    (menu).restrictPolicy initial horizon scheduler owner (changed owner (memories owner))
  let entryLaw := (N).runBehavioralUntil certificate selected entryStop E.initHistory
  let updated := entryLaw.bind fun entry => (posteriors entry).bind fun memories =>
    ((N).runBehavioralUntil certificate (memberProfile memories) segmentStop entry).map
      (site.ancestor? (N))
  let encountered := (independentProduct priors).bind fun memories =>
    ((N).runBehavioralUntil certificate (memberProfile memories) entryStop E.initHistory).bind
      fun entry => ((N).runBehavioralUntil certificate (memberProfile memories) segmentStop
        entry).map (site.ancestor? (N))
  obtain ⟨positive, _entryJoint, joined, mass, belief, ownFactor, ownPositive, factor⟩ :=
    phaseTimingPlanPolicy_value_replay_bayes_passage setup mode runtime leaks bounds runtimePlan
      horizon scheduler bound maximal fallback wellFormed assessment mixed finite weights noise
        noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded actual assembled
          actualMixed bayes certificate view.application.2.attempt who site past view observed
            clear rfl
  change encountered = updated at joined
  change (encountered.map Option.isSome) true = (N).informationMass selected who site at mass
  change (actual.belief who site).map some =
    fiberPosterior encountered Option.isSome true at belief
  change ((N).informationMass actual.strategy who site).toReal =
    ownFactor * ((encountered.map Option.isSome) true).toReal at factor
  rw [mass] at factor
  have point (atSite : (N).InformationHistory who site.1) :
      updated (some atSite) = hit atSite.1 := by
    change (entryLaw.bind fun entry => (posteriors entry).bind fun memories =>
      ((N).runBehavioralUntil certificate (memberProfile memories) segmentStop entry).map
        (site.ancestor? (N))) (some atSite) =
      (entryLaw.bind fun entry => (posteriors entry).bind fun memories =>
        (N).runBehavioralUntil certificate (memberProfile memories) segmentStop entry) atSite.1
    rw [PMF.bind_apply, PMF.bind_apply]
    apply tsum_congr
    intro entry
    by_cases supported : entry ∈ entryLaw.support
    · apply congrArg (entryLaw entry * ·)
      rw [PMF.bind_apply, PMF.bind_apply]
      apply tsum_congr
      intro memories
      apply congrArg ((posteriors entry) memories * ·)
      have atom := phase_attempt_first_passage_atom runtime leaks (menu) initial horizon scheduler
        certificate selected (memberProfile memories) site past view observed entry atSite supported
      convert atom using 1 <;> congr 2
      all_goals
        congr 1
        funext history
        rcases history with ⟨state, historyTrace⟩
        cases state <;> rfl
    · have zero := (PMF.apply_eq_zero_iff _ _).mpr supported
      simp only [zero, zero_mul]
  have total : (∑' atSite : (N).InformationHistory who site.1, hit atSite.1) =
      (N).informationMass selected who site := by
    rw [← mass, PMF.map_apply, ← (Equiv.optionEquivSumPUnit.{0} _).symm.tsum_eq,
      Summable.tsum_sum ENNReal.summable ENNReal.summable]
    simp only [Equiv.optionEquivSumPUnit_symm_inl, Equiv.optionEquivSumPUnit_symm_inr,
      Option.isSome_none, Bool.true_eq_false, ↓reduceIte, Option.isSome_some, tsum_zero, add_zero]
    apply tsum_congr
    intro atSite
    rw [joined, point]
  refine ⟨ownFactor, ownPositive, positive, factor, total, ?_⟩
  intro atSite
  have present : true ∈ (encountered.map Option.isSome).support := by
    rw [PMF.mem_support_iff, mass]
    exact positive.ne'
  have atom := congrArg (fun law => law (some atSite)) belief
  rw [pmf_map_apply_of_injective _ (Option.some_injective _) atSite,
    fiberPosterior_apply encountered Option.isSome true present] at atom
  simp only [Set.indicator, Set.mem_ofPred_eq, Option.isSome_some, ↓reduceIte] at atom
  rw [mass, joined, point] at atom
  simpa only [div_eq_mul_inv] using atom

end Vegas
