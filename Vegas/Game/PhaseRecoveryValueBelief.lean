/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueCallback
import Vegas.Game.PhaseClearProfileLocality

/-! # Actual clear-fiber Bayes weights of original global private policies -/

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

local instance phaseRecoveryValueBeliefPoolFintype : Fintype Pool := Fintype.ofFinite _

open Classical in
/-- The actual assembled assessment and the SAME original immutable global
member implementation agree at every genuine publicly clear complete input. -/
theorem phaseTimingPlanPolicy_value_clear_profile_agreement
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
              slotBounded agent))) who site.1) :
    let priors := fun who => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).map (Prod.mk plan)
    let members := fun who memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    let first := fun who => (menu).restrictPolicy initial horizon scheduler who
      (((app).policyMixture (priors who) (members who)).policy)
    ∀ who (site : (N).InformationSite who),
      ¬ PhasePublicExclusion setup mode runtime leaks site.1 →
        first who site.1 = actual.strategy who site.1 := by
  intro priors members first who site unflagged
  obtain ⟨⟨⟨state, trace⟩, seen⟩, _running, _choice⟩ := site.2
  have active := InformationSite.active (N) site ⟨⟨state, trace⟩, seen⟩
  cases state with
  | none =>
      change none = some who at active
      cases active
  | some control =>
      change control.actor = some who at active
      have info : (N).infoOf who trace = some (control.execution.recall who,
          control.execution.observe (app) who) :=
        ((menu).info initial horizon scheduler who trace).trans (by
          simp only [ReactiveApplication.observe, active, ite_true])
      have clear : control.execution.application.current.excluded = ∅ := by
        by_contra excluded
        apply unflagged
        exact ⟨control.execution.recall who, control.execution.observe (app) who,
          seen.symm.trans info, excluded⟩
      have law := phaseTimingPlanPolicy_value_callback_of_history setup mode runtime leaks bounds
        runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed finite
          weights noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded who
            control trace active clear
      let players := fun owner => ((app).policyMixture (priors owner) (members owner)).policy
      let target := (menu).decodeProfile initial horizon scheduler actual.strategy
      have inputLaw := (assembled who site unflagged).symm
      rw [← seen, info] at inputLaw
      have encoded := congrArg (PMF.map fun choice => choice.1.getD ⟨none⟩) inputLaw
      have decoded := law.trans (by
        simpa only [target, ReactiveApplication.ResponseMenu.decodeProfile,
          ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
          ReactiveApplication.ResponseMenu.rawChoice, PMF.map_comp, Function.comp_def]
            using encoded)
      have targetReadout : target who (control.execution.recall who)
          (control.execution.observe (app) who) = (actual.strategy who
            (some (control.execution.recall who, control.execution.observe (app) who))).map
              (fun choice => choice.1.getD ⟨none⟩) := by
        simp only [target, ReactiveApplication.ResponseMenu.decodeProfile,
          ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
          ReactiveApplication.ResponseMenu.rawChoice, PMF.map_comp, Function.comp_def]
      have finalLaw := decoded.trans targetReadout.symm
      change players who (control.execution.recall who)
          (control.execution.observe (app) who) =
        target who (control.execution.recall who) (control.execution.observe (app) who) at finalLaw
      rw [← seen, info]
      have targetCovered := (menu).decode_embedPolicy_covered initial horizon scheduler who
        (actual.strategy who) (control.execution.recall who) (control.execution.observe (app) who)
      have firstCovered : ∀ action ∈ (players who (control.execution.recall who)
          (control.execution.observe (app) who)).support,
          action ∈ (menu).actions who (control.execution.recall who)
            (control.execution.observe (app) who) := by
        rw [finalLaw]
        exact targetCovered
      have finiteLaw : (menu).restrictPolicy initial horizon scheduler who (players who)
          (some (control.execution.recall who, control.execution.observe (app) who)) =
        (menu).restrictPolicy initial horizon scheduler who (target who)
          (some (control.execution.recall who, control.execution.observe (app) who)) := by
        apply pmf_map_injective (f := Subtype.val) Subtype.val_injective
        rw [(menu).restrictPolicy_map_val initial horizon scheduler who (players who) _ _
          firstCovered, (menu).restrictPolicy_map_val initial horizon scheduler who (target who)
            _ _ targetCovered]
        exact congrArg (PMF.map some) finalLaw
      exact finiteLaw.trans (congrFun ((menu).restrict_decode_embedPolicy initial horizon
        scheduler who (actual.strategy who)) _)

open Classical in
/-- The SAME actual common Bayes belief on a publicly clear native information
fiber is exactly the normalized trace weight of the ORIGINAL global source-
policy and full timing-plan implementation. No reference entry is refreshed. -/
theorem phaseTimingPlanPolicy_value_bayes_of_clear
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
    (who : Player) (site : (N).InformationSite who)
    (unflagged : ¬ PhasePublicExclusion setup mode runtime leaks site.1) :
    let priors := fun who => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).map (Prod.mk plan)
    let members := fun who memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    let first := fun who => (menu).restrictPolicy initial horizon scheduler who
      (((app).policyMixture (priors who) (members who)).policy)
    (N).informationMass first who site = (N).informationMass actual.strategy who site ∧
      0 < (N).informationMass first who site ∧
      ∀ history : (N).InformationHistory who site.1,
        actual.belief who site history = (N).historyReachWeight first history.1 /
          (N).informationMass first who site := by
  intro priors members first
  have agree := phaseTimingPlanPolicy_value_clear_profile_agreement setup mode runtime leaks bounds
    runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed finite weights
      noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded actual assembled
  have each (history : (N).InformationHistory who site.1) :
      (N).historyReachWeight first history.1 =
        (N).historyReachWeight actual.strategy history.1 := by
    rcases history with ⟨⟨state, trace⟩, seen⟩
    have active := InformationSite.active (N) site ⟨⟨state, trace⟩, seen⟩
    cases state with
    | none =>
        change none = some who at active
        cases active
    | some control =>
        change control.actor = some who at active
        have info : (N).infoOf who trace = some (control.execution.recall who,
            control.execution.observe (app) who) :=
          ((menu).info initial horizon scheduler who trace).trans (by
            simp only [ReactiveApplication.observe, active, ite_true])
        have clear : control.execution.application.current.excluded = ∅ := by
          by_contra excluded
          apply unflagged
          exact ⟨control.execution.recall who, control.execution.observe (app) who,
            seen.symm.trans info, excluded⟩
        exact phase_clear_historyReach_eq setup mode runtime leaks bounds initial horizon scheduler
          first actual.strategy agree control trace clear
  have masses : (N).informationMass first who site =
      (N).informationMass actual.strategy who site := by
    unfold InformationModel.informationMass
    exact tsum_congr each
  have positive := (N).informationMass_pos_of_fullSupport actual.strategy actualMixed who site
  refine ⟨masses, masses.symm ▸ positive, ?_⟩
  intro history
  have rule := bayes who site positive history
  rw [← each history, ← masses] at rule
  exact rule

end Vegas
