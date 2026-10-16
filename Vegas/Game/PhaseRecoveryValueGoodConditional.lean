/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueGoodNative
import GameTheoryExtensions.Math.Probability.ProductTransport

/-! # Conditional native normalization of retained original-memory weights -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (runtimePlan : RuntimePhasePlan (serviceGraph setup mode))
  (initial : PMF (phaseApplication runtime leaks).State)
  (initialLaw : initial = setup.initialLaw.map
    (fun draw => PhaseRuntimeState.initial runtimePlan (encodeInputs draw)))
  (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information initial
    horizon scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "nativeInitial" => PMF.map
  (fun draw => PhaseRuntimeState.initial runtimePlan (encodeInputs draw)) setup.initialLaw
local notation "M" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) nativeInitial horizon scheduler
local notation "P" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) nativeInitial horizon scheduler
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "Pool" => FreeKeyedPool
  (fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
    (Subtype.val (Sigma.snd agent)))
  (fun agent : Agent => PhaseUnprotected runtime leaks bound (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
  (fun agent : Agent => phaseTimingKey runtime leaks (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound

local instance phaseRecoveryValueGoodConditionalPoolFintype : Fintype Pool := Fintype.ofFinite _

private abbrev GoodConditionalMemories := (who : Player) → ((p : Pool) → Parts p) ×
  (setup.informationModel (CommitmentInterface.forfeiture setup.program)).Policy who

local notation "Memory" => GoodConditionalMemories setup mode runtime leaks bounds initial horizon
  scheduler bound

open Classical in
/-- The retained ORIGINAL-memory weight of a full native history. Only foreign
binding-SEND RAW summands are deleted; all remaining physical atoms are literal. -/
def phaseTimingPlanPolicy_value_retainedWeight
    (fallback : ∀ who, (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slot : ℝ) (slotNonnegative : 0 ≤ slot) (slotBounded : slot ≤ 1)
    (focal : Player) (replay : (app).Policy) (history : (E).History) (chance : ℝ) : ℝ :=
  let original := fun who => (independentProduct weights).bind fun plan =>
    (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).map (Prod.mk plan)
  let source := fun (memory : Memory) who =>
    setup.commitRecoveryValueAssessment wellFormed assessment who (memory who).2
  let plain := fun (memory : Memory) who => phaseTimingPlanProfile setup mode runtime leaks bounds
    initial horizon scheduler bound fallback wellFormed (source memory who) noise nonnegative
      bounded slot slotNonnegative slotBounded (fun who => (memory who).1) who
  let zero := fun (memory : Memory) who => phaseTimingPlanProfile setup mode runtime leaks bounds
    initial horizon scheduler bound fallback wellFormed (source memory who) 0 (by norm_num)
      (by norm_num) slot slotNonnegative slotBounded (fun who => (memory who).1) who
  let members := fun memory => Function.update (plain memory) focal
    ((menu).restrictPolicy initial horizon scheduler focal replay)
  let records := fun who => (N).ownPlay who history.trace
  let Index := (who : Player) × Fin (records who).length
  let record := fun index : Index => (records index.1)[index.2.val]
  let marked := fun index : Index => index.1 ≠ focal ∧
    phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan horizon scheduler
      index.1 (record index)
  let atom := fun memory (index : Index) =>
    (((members memory index.1 (record index).1).map Subtype.val) (some (record index).2)).toReal
  let kept := fun memory (index : Index) => if marked index then (1 - noise) *
    (((zero memory index.1 (record index).1).map Subtype.val) (some (record index).2)).toReal
    else atom memory index
  expect (independentProduct original) (fun memory => chance * ∏ index, kept memory index)

open Classical in
/-- On an actual clear native input fiber, normalizing the explicit retained
ORIGINAL-memory weight changes the SAME noisy conditional law by at most twice
its intrinsic foreign binding RAW share. No uniform information-mass floor is used. -/
theorem phaseTimingPlanPolicy_value_good_conditional
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : ∀ who, (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (mixed : assessment.IsFullyMixed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slot : ℝ) (slotNonnegative : 0 ≤ slot) (slotBounded : slot ≤ 1)
    (focal : Player) (replay : (app).Policy)
    (replayCovered : ∀ past view response, response ∈ (replay past view).support →
      response ∈ (menu).actions focal past view)
    (site : (N).InformationSite focal)
    (unflagged : ¬ PhasePublicExclusion setup mode runtime leaks site.1)
    [Fintype ((N).InformationHistory focal site.1)] :
    let original := fun who => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).map (Prod.mk plan)
    let family := fun who memory => if who = focal then replay else
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who
          memory.2) noise nonnegative bounded slot slotNonnegative slotBounded memory.1 who
    let behavior := fun who => (menu).restrictPolicy initial horizon scheduler who
      ((app).policyMixture (original who) (family who)).policy
    let weight := fun history : (N).InformationHistory focal site.1 =>
      ((N).historyReachWeight behavior history.1).toReal
    let nativeBehavior : ∀ who, (M).BehavioralPolicy who := initialLaw ▸ behavior
    let marks := fun history : (N).InformationHistory focal site.1 =>
      ∑ owner ∈ Finset.univ.erase focal, ∑ index ∈ Finset.range (2 * horizon + 1),
        phaseRawBindingPositionWeight setup mode runtime leaks bounds runtimePlan horizon
          scheduler noise owner nativeBehavior (initialLaw ▸ history.1) index
    0 < ∑ history, weight history → (∑ history, marks history) < ∑ history, weight history →
    ∃ chance : (N).InformationHistory focal site.1 → ℝ,
      (∀ history, 0 ≤ chance history ∧
        ∀ players : ∀ who, (N).BehavioralPolicy who,
          ((N).historyReachWeight players history.1).toReal = chance history *
            ∏ who, (N).ownPlayReachProbability (players who) ((N).ownPlay who history.1.trace)) ∧
      let good := fun history : (N).InformationHistory focal site.1 =>
        phaseTimingPlanPolicy_value_retainedWeight setup mode runtime leaks bounds runtimePlan
          initial horizon scheduler bound fallback wellFormed assessment finite weights noise
            nonnegative bounded slot slotNonnegative slotBounded focal replay history.1
              (chance history)
      (∀ history, 0 ≤ good history ∧ good history ≤ weight history) ∧
        0 < ∑ history, good history ∧
        ∑ history, |weight history / ∑ next, weight next -
          good history / ∑ next, good next| ≤
            2 * (∑ history, marks history) / ∑ history, weight history := by
  intro original family behavior weight nativeBehavior marks positive small
  have each (history : (N).InformationHistory focal site.1) :
      ∃ chance : ℝ, 0 ≤ chance ∧
        (∀ players : ∀ who, (N).BehavioralPolicy who,
          ((N).historyReachWeight players history.1).toReal = chance *
            ∏ who, (N).ownPlayReachProbability (players who) ((N).ownPlay who history.1.trace)) ∧
        let good := phaseTimingPlanPolicy_value_retainedWeight setup mode runtime leaks bounds
          runtimePlan initial horizon scheduler bound fallback wellFormed assessment finite weights
            noise nonnegative bounded slot slotNonnegative slotBounded focal replay history.1 chance
        0 ≤ good ∧ good ≤ weight history ∧ weight history ≤ good + marks history := by
    rcases history with ⟨⟨state, trace⟩, seen⟩
    have active := InformationSite.active (N) site ⟨⟨state, trace⟩, seen⟩
    cases state with
    | none =>
        change none = some focal at active
        cases active
    | some control =>
        change control.actor = some focal at active
        have info : (N).infoOf focal trace = some (control.execution.recall focal,
            control.execution.observe (app) focal) :=
          ((menu).info initial horizon scheduler focal trace).trans (by
            simp only [ReactiveApplication.observe, active, ite_true])
        have clear : control.execution.application.current.excluded = ∅ := by
          by_contra excluded
          exact unflagged ⟨control.execution.recall focal, control.execution.observe (app) focal,
            seen.symm.trans info, excluded⟩
        have castHistory : (initialLaw ▸ (⟨some control, trace⟩ : (E).History) : (P).History) =
            ⟨some control, initialLaw ▸ trace⟩ := by
          cases initialLaw
          rfl
        have actual := phaseTimingPlanPolicy_value_good_history_native setup mode runtime leaks
          bounds runtimePlan initial initialLaw horizon scheduler bound maximal fallback wellFormed
            assessment mixed finite weights noise nonnegative bounded slot slotNonnegative
              slotBounded
              focal replay replayCovered control trace clear
        simpa only [phaseTimingPlanPolicy_value_retainedWeight, weight, marks, castHistory]
          using actual
  choose chance nonnegativeChance factor estimates using each
  let good := fun history : (N).InformationHistory focal site.1 =>
    phaseTimingPlanPolicy_value_retainedWeight setup mode runtime leaks bounds runtimePlan initial
      horizon scheduler bound fallback wellFormed assessment finite weights noise nonnegative
        bounded
        slot slotNonnegative slotBounded focal replay history.1 (chance history)
  refine ⟨chance, fun history => ⟨nonnegativeChance history, factor history⟩,
    fun history => ⟨(estimates history).1, (estimates history).2.1⟩, ?_⟩
  have gap : (∑ history, weight history) - ∑ history, good history ≤ ∑ history, marks history := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun history _ => by linarith [(estimates history).2.2]
  have goodPositive : 0 < ∑ history, good history := by linarith
  refine ⟨goodPositive, ?_⟩
  have goodNonnegative (history) : 0 ≤ good history := (estimates history).1
  have below (history) : good history ≤ weight history := (estimates history).2.1
  have totalBelow : (∑ history, good history) ≤ ∑ history, weight history :=
    Finset.sum_le_sum fun history _ => below history
  have pointwise (history) :
      |weight history / ∑ next, weight next - good history / ∑ next, good next| ≤
        (weight history - good history) / (∑ next, weight next) + good history *
          ((∑ next, weight next) - ∑ next, good next) /
            ((∑ next, weight next) * ∑ next, good next) := by
    have split : weight history / (∑ next, weight next) - good history / (∑ next, good next) =
        (weight history - good history) / (∑ next, weight next) + good history *
          ((∑ next, good next) - ∑ next, weight next) /
            ((∑ next, weight next) * ∑ next, good next) := by
      field_simp [ne_of_gt positive, ne_of_gt goodPositive]
      ring
    rw [split]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_div, abs_of_nonneg (sub_nonneg.mpr (below history)), abs_of_pos positive,
      abs_div, abs_mul, abs_of_nonneg (goodNonnegative history),
        abs_of_nonpos (sub_nonpos.mpr totalBelow), abs_of_pos (mul_pos positive goodPositive)]
    ring
  calc
    ∑ history, |weight history / ∑ next, weight next - good history / ∑ next, good next|
      ≤ ∑ history, ((weight history - good history) / (∑ next, weight next) + good history *
          ((∑ next, weight next) - ∑ next, good next) /
            ((∑ next, weight next) * ∑ next, good next)) :=
        Finset.sum_le_sum fun history _ => pointwise history
    _ = 2 * ((∑ history, weight history) - ∑ history, good history) /
        (∑ history, weight history) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib,
        ← Finset.sum_div, ← Finset.sum_mul]
      field_simp [ne_of_gt positive, ne_of_gt goodPositive]
      ring
    _ ≤ 2 * (∑ history, marks history) / ∑ history, weight history := by gcongr

end Vegas
