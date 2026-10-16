/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueGoodWeight
import Interaction.ReactiveMixtureLikelihood
import Interaction.ReactiveMenuLikelihood
import GameTheoryExtensions.Math.Probability.ProductExpectation

/-! # Original global-memory averaging of actual whole-history weights -/

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
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information initial
    horizon scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
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

local instance phaseRecoveryValueGoodDensityPoolFintype : Fintype Pool := Fintype.ofFinite _

private abbrev GoodValueMemories := (who : Player) → ((p : Pool) → Parts p) ×
  (setup.informationModel (CommitmentInterface.forfeiture setup.program)).Policy who

local notation "Memory" => GoodValueMemories setup mode runtime leaks bounds initial horizon
  scheduler bound

open Classical in
/-- Averaging the original once-sampled global value policies and full timing
plans gives exactly the literal whole native history weight of their behavioral
implementations. The focal replay is fixed; its raw past need not have a source
explanation. No entry distribution is resampled. -/
theorem phaseTimingPlanPolicy_value_history_average
    (fallback : ∀ who, (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slot : ℝ) (slotNonnegative : 0 ≤ slot) (slotBounded : slot ≤ 1)
    (focal : Player) (replay : (app).Policy)
    (replayCovered : ∀ past view response, response ∈ (replay past view).support →
      response ∈ (menu).actions focal past view)
    (final : (app).Control) (trace : (E).Trace (some final)) :
    let original := fun who => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).map (Prod.mk plan)
    let family := fun who memory => if who = focal then replay else
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who
          memory.2) noise nonnegative bounded slot slotNonnegative slotBounded memory.1 who
    let members := fun memories who => (menu).restrictPolicy initial horizon scheduler who
      (family who (memories who))
    let behavior := fun who => (menu).restrictPolicy initial horizon scheduler who
      ((app).policyMixture (original who) (family who)).policy
    expect (independentProduct original) (fun memories =>
      ((N).historyReachWeight (members memories) ⟨some final, trace⟩).toReal) =
        ((N).historyReachWeight behavior ⟨some final, trace⟩).toReal := by
  intro original family members behavior
  have covered (who memory past view response)
      (supported : response ∈ (family who memory past view).support) :
      response ∈ (menu).actions who past view := by
    by_cases same : who = focal
    · subst who
      exact replayCovered past view response (by simpa only [family, ↓reduceIte] using supported)
    · dsimp only [family] at supported
      rw [ite_eq_right same] at supported
      exact phaseTimingPlanPolicy_covered setup mode runtime leaks bounds initial horizon scheduler
        bound fallback wellFormed _ noise nonnegative bounded slot slotNonnegative slotBounded
          memory.1 who past view response supported
  have behaviorCovered (who past view response)
      (supported : response ∈ (((app).policyMixture (original who) (family who)).policy
        past view).support) : response ∈ (menu).actions who past view := by
    rw [(app).policyMixture_policy, PMF.support_bind] at supported
    obtain ⟨memory, _possible, supported⟩ := Set.mem_iUnion₂.mp supported
    exact covered who memory past view response supported
  have ownRecall (who) : (N).ownPlay who trace =
      (app).ownPlayFrom [] (final.execution.recall who) := by
    change ((menu).signals initial horizon scheduler).ownPlay who trace = _
    rw [← (menu).ownPlay_toRawTrace initial horizon scheduler who trace, (app).trace_ownPlay]
    rfl
  obtain ⟨records, recordsEq, _provenance, chance, _chanceNonnegative, factor⟩ :=
    (N).exists_continuation_ownPlay_factor (.start : (E).Trace (E).init) trace
      (TracePrefix.start trace)
  have recordEq (who) : records who = (app).ownPlayFrom [] (final.execution.recall who) := by
    simpa only [InfoSignals.ownPlay, List.append_nil, ownRecall] using (recordsEq who).symm
  let likelihood := fun who memory =>
    ((((app).privateTranscriptFrom [] (final.execution.recall who)).map (fun record =>
      family who memory record.1.1 record.1.2 record.2)).prod).toReal
  have likelihoodNonnegative (who memory) : 0 ≤ likelihood who memory := ENNReal.toReal_nonneg
  have likelihoodBounded (who memory) : likelihood who memory ≤ 1 := by
    dsimp only [likelihood]
    rw [(app).privateTranscriptFrom_product]
    exact Finset.prod_le_one₀ (fun _ _ => ENNReal.toReal_nonneg)
      (fun _ _ => pmf_toReal_apply_le_one _ _)
  have memberFactor (memories) :
      ((N).historyReachWeight (members memories) ⟨some final, trace⟩).toReal =
        chance * ∏ who, likelihood who (memories who) := by
    have equality := factor (members memories)
    simp only [Trace.length, Nat.sub_zero, recordEq] at equality
    change ((N).historyReachWeight (members memories) ⟨some final, trace⟩).toReal = _
    simpa only [members, (menu).ownPlayFrom_restrictPolicy initial horizon scheduler _ _
      (covered _ _), likelihood, historyReachWeight, runBehavioral, ExecutionProtocol.initHistory]
        using equality
  have behaviorFactor : ((N).historyReachWeight behavior ⟨some final, trace⟩).toReal =
      chance * ∏ who, ((((app).privateTranscriptFrom [] (final.execution.recall who)).map
        (fun record => ((app).policyMixture (original who) (family who)).policy
          record.1.1 record.1.2 record.2)).prod).toReal := by
    have equality := factor behavior
    simp only [Trace.length, Nat.sub_zero, recordEq] at equality
    simpa only [behavior, (menu).ownPlayFrom_restrictPolicy initial horizon scheduler _ _
      (behaviorCovered _), historyReachWeight, runBehavioral, ExecutionProtocol.initHistory]
        using equality
  rw [show (fun memories => ((N).historyReachWeight (members memories)
    ⟨some final, trace⟩).toReal) = (fun memories => chance * ∏ who, likelihood who (memories who))
      from funext memberFactor, expect_const_mul,
    expect_independentProduct_prod original likelihood likelihoodNonnegative likelihoodBounded,
    behaviorFactor]
  apply congrArg (chance * ·)
  apply Finset.prod_congr rfl
  intro who _member
  have average := (app).policyMixture_likelihood_expect (original who) (family who) []
    (final.execution.recall who) (fun _ => (1 : ℝ))
  have initialPosterior : ((app).policyMixture (original who) (family who)).posterior [] =
      original who := rfl
  rw [initialPosterior] at average
  simpa only [likelihood, mul_one, expect_constant] using average

open Classical in
/-- The ORIGINAL once-sampled memory law assigns an explicit nonnegative good
weight to a genuine whole history. Its loss from the SAME actual behavioral
history weight is bounded by original-memory averages of exact foreign binding
RAW marks. Every opening/WAIT factor stays noisy and the focal replay is fixed. -/
theorem phaseTimingPlanPolicy_value_good_history_average
    (fallback : ∀ who, (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slot : ℝ) (slotNonnegative : 0 ≤ slot) (slotBounded : slot ≤ 1)
    (focal : Player) (replay : (app).Policy)
    (replayCovered : ∀ past view response, response ∈ (replay past view).support →
      response ∈ (menu).actions focal past view)
    (final : (app).Control) (trace : (E).Trace (some final)) :
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
    let family := fun who memory => if who = focal then replay else
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who
          memory.2) noise nonnegative bounded slot slotNonnegative slotBounded memory.1 who
    let behavior := fun who => (menu).restrictPolicy initial horizon scheduler who
      ((app).policyMixture (original who) (family who)).policy
    let records := fun who => (N).ownPlay who trace
    let Index := (who : Player) × Fin (records who).length
    let record := fun index : Index => (records index.1)[index.2.val]
    let marked := fun index : Index => index.1 ≠ focal ∧
      phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan horizon scheduler
        index.1 (record index)
    let atom := fun memory (index : Index) =>
      (((members memory index.1 (record index).1).map Subtype.val) (some (record index).2)).toReal
    let raw := fun index : Index => if marked index then noise *
      ((((menu).uniformPolicy initial horizon scheduler index.1 (record index).1).map Subtype.val)
        (some (record index).2)).toReal else 0
    let kept := fun memory (index : Index) => if marked index then (1 - noise) *
      (((zero memory index.1 (record index).1).map Subtype.val) (some (record index).2)).toReal
      else atom memory index
    ∃ chance : ℝ, 0 ≤ chance ∧
      (∀ players : ∀ who, (N).BehavioralPolicy who,
        ((N).historyReachWeight players ⟨some final, trace⟩).toReal =
          chance * ∏ who, (N).ownPlayReachProbability (players who) (records who)) ∧
      let good := expect (independentProduct original) (fun memory =>
        chance * ∏ index, kept memory index)
      let error := expect (independentProduct original) (fun memory =>
        chance * ∑ index, raw index * ∏ other ∈ Finset.univ.erase index, atom memory other)
      0 ≤ good ∧ good ≤ ((N).historyReachWeight behavior ⟨some final, trace⟩).toReal ∧
        ((N).historyReachWeight behavior ⟨some final, trace⟩).toReal ≤ good + error := by
  intro original source plain zero members family behavior records Index record marked
    atom raw kept
  obtain ⟨suffixes, suffixEq, _provenance, chance, chanceNonnegative, factor⟩ :=
    (N).exists_continuation_ownPlay_factor (.start : (E).Trace (E).init) trace
      (TracePrefix.start trace)
  have suffixIdentity (who : Player) : suffixes who = records who := by
    simpa only [records, InfoSignals.ownPlay, List.append_nil] using (suffixEq who).symm
  have reach (players : ∀ who, (N).BehavioralPolicy who) :
      ((N).historyReachWeight players ⟨some final, trace⟩).toReal =
        chance * ∏ who, (N).ownPlayReachProbability (players who) (records who) := by
    simpa only [historyReachWeight, runBehavioral, Trace.length, Nat.sub_zero, suffixIdentity,
      ExecutionProtocol.initHistory] using factor players
  have memberReach (memory : Memory) :
      ((N).historyReachWeight (members memory) ⟨some final, trace⟩).toReal =
        chance * ∏ index, atom memory index := by
    rw [reach]
    congr 1
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro who _
    have array := (N).ownPlayReachProbability_ofFn who (members memory who)
      (fun index : Fin (records who).length => (records who)[index.val])
    simpa only [List.ofFn_getElem] using array
  have product (memory : Memory) :
      (∀ index, 0 ≤ kept memory index ∧ kept memory index ≤ atom memory index) ∧
      (∏ index, kept memory index) ≤ ∏ index, atom memory index ∧
      (∏ index, atom memory index) ≤ (∏ index, kept memory index) +
        ∑ index, raw index * ∏ other ∈ Finset.univ.erase index, atom memory other := by
    have localProduct := phaseTimingPlanPolicy_binding_good_product setup mode runtime leaks bounds
      runtimePlan initial horizon scheduler bound fallback wellFormed (source memory) noise
      nonnegative
        bounded slot slotNonnegative slotBounded (fun who => (memory who).1) focal
          ((menu).restrictPolicy initial horizon scheduler focal replay) trace
    exact ⟨fun index => ⟨(localProduct.1 index).1, (localProduct.1 index).2.1⟩,
      localProduct.2⟩
  have nativeMember (memory : Memory) :
      (fun who => (menu).restrictPolicy initial horizon scheduler who
        (family who (memory who))) = members memory := by
    funext who
    by_cases same : who = focal
    · subst who
      simp only [family, ↓reduceIte, members, Function.update_self]
    · simp only [family, ite_eq_right same, members, Function.update_of_ne same]
      exact (menu).restrict_decode_embedPolicy initial horizon scheduler who _
  have average := phaseTimingPlanPolicy_value_history_average setup mode runtime leaks bounds
      initial
    horizon scheduler bound fallback wellFormed assessment finite weights noise
      nonnegative bounded slot slotNonnegative slotBounded focal replay replayCovered final trace
  change expect (independentProduct original) (fun memory =>
    ((N).historyReachWeight (fun who => (menu).restrictPolicy initial horizon scheduler who
      (family who (memory who))) ⟨some final, trace⟩).toReal) =
      ((N).historyReachWeight behavior ⟨some final, trace⟩).toReal at average
  simp only [nativeMember] at average
  let prior := independentProduct original
  let good := fun memory : Memory => chance * ∏ index, kept memory index
  let error := fun memory : Memory => chance *
    ∑ index, raw index * ∏ other ∈ Finset.univ.erase index, atom memory other
  let actual := fun memory : Memory =>
    ((N).historyReachWeight (members memory) ⟨some final, trace⟩).toReal
  have rawNonnegative (index : Index) : 0 ≤ raw index := by
    dsimp only [raw]
    split_ifs
    · exact mul_nonneg nonnegative ENNReal.toReal_nonneg
    · exact le_rfl
  have rawBounded (index : Index) : raw index ≤ 1 := by
    dsimp only [raw]
    split_ifs
    · exact (mul_le_mul_of_nonneg_left (pmf_toReal_apply_le_one _ _) nonnegative).trans
        (by simpa only [mul_one] using bounded)
    · exact zero_le_one
  have goodNonnegative (memory) : 0 ≤ good memory :=
    mul_nonneg chanceNonnegative (Finset.prod_nonneg fun index _ => ((product memory).1 index).1)
  have goodBounded (memory) : good memory ≤ chance := by
    apply (mul_le_mul_of_nonneg_left (Finset.prod_le_one₀
      (fun index _ => ((product memory).1 index).1)
      (fun index _ => ((product memory).1 index).2.trans (pmf_toReal_apply_le_one _ _)))
        chanceNonnegative).trans
    rw [mul_one]
  have errorNonnegative (memory) : 0 ≤ error memory :=
    mul_nonneg chanceNonnegative (Finset.sum_nonneg fun index _ =>
      mul_nonneg (rawNonnegative index) (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg))
  have errorBounded (memory) : error memory ≤ chance * Fintype.card Index := by
    apply mul_le_mul_of_nonneg_left _ chanceNonnegative
    calc
      _ ≤ ∑ _index : Index, (1 : ℝ) := Finset.sum_le_sum fun index _ =>
        (mul_le_mul_of_nonneg_left (Finset.prod_le_one₀
          (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => pmf_toReal_apply_le_one _ _))
            (rawNonnegative index)).trans (by simpa only [mul_one] using rawBounded index)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have goodIntegrable : PayoffIntegrable prior good :=
    payoffIntegrable_of_bounded _ _ (fun memory => by
      rw [abs_of_nonneg (goodNonnegative memory)]
      exact goodBounded memory)
  have errorIntegrable : PayoffIntegrable prior error :=
    payoffIntegrable_of_bounded _ _ (fun memory => by
      rw [abs_of_nonneg (errorNonnegative memory)]
      exact errorBounded memory)
  have actualIntegrable : PayoffIntegrable prior actual :=
    payoffIntegrable_of_bounded _ _ (C := 1) (fun memory => by
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      exact pmf_toReal_apply_le_one _ _)
  refine ⟨chance, chanceNonnegative, reach, ?_⟩
  change 0 ≤ expect prior good ∧ expect prior good ≤ _ ∧
    _ ≤ expect prior good + expect prior error
  have lower (memory) : good memory ≤ actual memory := by
    rw [show actual memory = chance * ∏ index, atom memory index from memberReach memory]
    exact mul_le_mul_of_nonneg_left (product memory).2.1 chanceNonnegative
  have upper (memory) : actual memory ≤ good memory + error memory := by
    rw [show actual memory = chance * ∏ index, atom memory index from memberReach memory]
    simpa only [mul_add] using mul_le_mul_of_nonneg_left (product memory).2.2 chanceNonnegative
  have actualMean : expect prior actual =
      ((N).historyReachWeight behavior ⟨some final, trace⟩).toReal := average
  refine ⟨expect_nonneg prior good (fun memory _ => goodNonnegative memory), ?_, ?_⟩
  · rw [← actualMean]
    exact expect_mono (fun memory _ => lower memory) goodIntegrable actualIntegrable
  · rw [← actualMean, ← expect_add goodIntegrable errorIntegrable]
    exact expect_mono (fun memory _ => upper memory) actualIntegrable
      (payoffIntegrable_add goodIntegrable errorIntegrable)

end Vegas
