/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueGoodDensity
import Vegas.Game.PhaseRecoveryValueNativeMarkerSum

/-! # Intrinsic native errors of the original retained history weight -/

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

local instance phaseRecoveryValueGoodNativePoolFintype : Fintype Pool := Fintype.ofFinite _

private abbrev GoodNativeMemories := (who : Player) → ((p : Pool) → Parts p) ×
  (setup.informationModel (CommitmentInterface.forfeiture setup.program)).Policy who

local notation "Memory" => GoodNativeMemories setup mode runtime leaks bounds initial horizon
  scheduler bound

open Classical in
private abbrev nativeBindingMarker (noise : ℝ) (focal : Player) (chance : ℝ) :=
  fun (entries : ∀ who, List ((N).InfoState who × (E).Action who))
      (profile : ∀ who, (N).BehavioralPolicy who) => chance *
    ∑ index : (Σ who, Fin (entries who).length),
      if index.1 ≠ focal ∧ phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan
          horizon scheduler index.1 (entries index.1)[index.2.val] then
        phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler noise
          index.1 (entries index.1)[index.2.val] * ∏ other ∈ Finset.univ.erase index,
            (((profile other.1 (entries other.1)[other.2.val].1).map Subtype.val)
              (some (entries other.1)[other.2.val].2)).toReal
      else 0

include initialLaw in
open Classical in
private theorem whole_marker_average
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
    (final : (app).Control) (trace : (E).Trace (some final))
    (clear : final.execution.application.current.excluded = ∅) (chance : ℝ) :
    let original := fun who => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).map (Prod.mk plan)
    let source := fun (memory : Memory) who =>
      setup.commitRecoveryValueAssessment wellFormed assessment who (memory who).2
    let plain := fun (memory : Memory) who => phaseTimingPlanProfile setup mode runtime leaks bounds
      initial horizon scheduler bound fallback wellFormed (source memory who) noise nonnegative
        bounded slot slotNonnegative slotBounded (fun who => (memory who).1) who
    let members := fun memory => Function.update (plain memory) focal
      ((menu).restrictPolicy initial horizon scheduler focal replay)
    let family := fun who memory => if who = focal then replay else
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who
          memory.2) noise nonnegative bounded slot slotNonnegative slotBounded memory.1 who
    let behavior := fun who => (menu).restrictPolicy initial horizon scheduler who
      ((app).policyMixture (original who) (family who)).policy
    let records := fun who => (N).ownPlay who trace
    let marker := fun profile : ∀ who, (N).BehavioralPolicy who => chance *
      ∑ index : (Σ who, Fin (records who).length),
        if index.1 ≠ focal ∧ phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan
            horizon scheduler index.1 (records index.1)[index.2.val] then
          phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler noise
            index.1 (records index.1)[index.2.val] * ∏ other ∈ Finset.univ.erase index,
              (((profile other.1 (records other.1)[other.2.val].1).map Subtype.val)
                (some (records other.1)[other.2.val].2)).toReal
        else 0
    expect (independentProduct original) (fun memory => marker (members memory)) =
      marker behavior := by
  intro original source plain members family behavior records marker
  have ownRecall (who) : records who = (app).ownPlayFrom [] (final.execution.recall who) := by
    change ((menu).signals initial horizon scheduler).ownPlay who trace = _
    rw [← (menu).ownPlay_toRawTrace initial horizon scheduler who trace, (app).trace_ownPlay]
    rfl
  have nativeMember (memory : Memory) :
      (fun who => (menu).restrictPolicy initial horizon scheduler who
        (family who (memory who))) = members memory := by
    funext who
    by_cases same : who = focal
    · subst who
      simp only [family, ↓reduceIte, members, Function.update_self]
    · simp only [family, ite_eq_right same, members, Function.update_of_ne same]
      exact (menu).restrict_decode_embedPolicy initial horizon scheduler who _
  have lawEq : initial = (setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial runtimePlan) := initialLaw.trans (by
    simpa only [Function.comp_def] using
      (PMF.map_comp encodeInputs setup.initialLaw (PhaseRuntimeState.initial runtimePlan)).symm)
  have average := phaseTimingPlanPolicy_marker_sum_expect_of_history setup mode runtime leaks
    bounds runtimePlan initial lawEq horizon scheduler bound maximal fallback wellFormed assessment
      mixed finite weights noise nonnegative bounded slot slotNonnegative slotBounded focal replay
        replayCovered final trace clear (fun _ => []) final.execution.recall
          (fun _ => (List.nil_append _).symm) chance
  let markerFor := nativeBindingMarker setup mode runtime leaks bounds runtimePlan initial
    horizon scheduler noise focal chance
  change expect (independentProduct fun who =>
      ((app).policyMixture (original who) (family who)).posterior [])
      (fun memory => markerFor (fun who => (app).ownPlayFrom [] (final.execution.recall who))
        (fun who => (menu).restrictPolicy initial horizon scheduler who
          (family who (memory who)))) =
    markerFor (fun who => (app).ownPlayFrom [] (final.execution.recall who)) behavior at average
  have recallsEq : (fun who => (app).ownPlayFrom [] (final.execution.recall who)) = records :=
    funext fun who => (ownRecall who).symm
  rw [recallsEq] at average
  have posteriorZero (who) : ((app).policyMixture (original who) (family who)).posterior [] =
      original who := rfl
  simpa only [posteriorZero, nativeMember] using average

open Classical in
/-- The ORIGINAL retained global-memory history weight loses at most the
intrinsic native FOREIGN binding RAW-position mass. This consumes exact
member-marker averaging, not an unlabeled kernel equality. Opening RAW WAIT
and every other original nonbinding factor remain in the retained weight. -/
theorem phaseTimingPlanPolicy_value_good_history_native
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
    (final : (app).Control) (trace : (E).Trace (some final))
    (clear : final.execution.application.current.excluded = ∅) :
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
    let kept := fun memory (index : Index) => if marked index then (1 - noise) *
      (((zero memory index.1 (record index).1).map Subtype.val) (some (record index).2)).toReal
      else atom memory index
    let nativeTrace : (P).Trace (some final) := initialLaw ▸ trace
    let nativeBehavior : ∀ who, (M).BehavioralPolicy who := initialLaw ▸ behavior
    ∃ chance : ℝ, 0 ≤ chance ∧
      (∀ players : ∀ who, (N).BehavioralPolicy who,
        ((N).historyReachWeight players ⟨some final, trace⟩).toReal =
          chance * ∏ who, (N).ownPlayReachProbability (players who) (records who)) ∧
      let good := expect (independentProduct original) (fun memory =>
        chance * ∏ index, kept memory index)
      0 ≤ good ∧ good ≤ ((N).historyReachWeight behavior ⟨some final, trace⟩).toReal ∧
        ((N).historyReachWeight behavior ⟨some final, trace⟩).toReal ≤ good +
          ∑ owner ∈ Finset.univ.erase focal, ∑ index ∈ Finset.range (2 * horizon + 1),
            phaseRawBindingPositionWeight setup mode runtime leaks bounds runtimePlan horizon
              scheduler noise owner nativeBehavior ⟨some final, nativeTrace⟩ index := by
  intro original source plain zero members family behavior records Index record marked atom kept
    nativeTrace nativeBehavior
  let raw := fun index : Index => if marked index then noise *
    ((((menu).uniformPolicy initial horizon scheduler index.1 (record index).1).map Subtype.val)
      (some (record index).2)).toReal else 0
  obtain ⟨chance, nonnegativeChance, factor, goodBounds⟩ :=
    phaseTimingPlanPolicy_value_good_history_average setup mode runtime leaks bounds runtimePlan
      initial horizon scheduler bound fallback wellFormed assessment finite weights noise
        nonnegative bounded slot slotNonnegative slotBounded focal replay replayCovered final trace
  refine ⟨chance, nonnegativeChance, factor, goodBounds.1, goodBounds.2.1, ?_⟩
  let markerFor := nativeBindingMarker setup mode runtime leaks bounds runtimePlan initial
    horizon scheduler noise focal chance
  have average := whole_marker_average setup mode runtime leaks bounds runtimePlan initial
    initialLaw horizon scheduler bound maximal fallback wellFormed assessment mixed finite weights
      noise nonnegative bounded slot slotNonnegative slotBounded focal replay replayCovered final
        trace clear chance
  let marker := markerFor records
  have uniformAtom (who : Player) (input : (app).Info) (action : (app).Action) :
      ((((menu).uniformPolicy initial horizon scheduler who input).map Subtype.val)
        (some action)).toReal =
      ((((menu).uniformPolicy nativeInitial horizon scheduler who input).map Subtype.val)
        (some action)).toReal := by
    cases initialLaw
    rfl
  have errorEq (memory : Memory) :
      chance * (∑ index, raw index * ∏ other ∈ Finset.univ.erase index, atom memory other) =
        marker (members memory) := by
    apply congrArg (chance * ·)
    apply Finset.sum_congr rfl
    intro index _
    change raw index * (∏ other ∈ Finset.univ.erase index, atom memory other) =
      if marked index then phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan
        horizon scheduler noise index.1 (record index) *
          ∏ other ∈ Finset.univ.erase index, atom memory other else 0
    by_cases selected : marked index
    · simp only [raw, ite_eq_left selected, phaseRawMixtureAtom]
      rw [uniformAtom]
    · simp only [raw, ite_eq_right selected, zero_mul]
  have averageEq : expect (independentProduct original) (fun memory =>
      chance * ∑ index, raw index * ∏ other ∈ Finset.univ.erase index, atom memory other) =
        marker behavior := by
    rw [show (fun memory => chance * ∑ index, raw index *
      ∏ other ∈ Finset.univ.erase index, atom memory other) =
        (fun memory => marker (members memory)) from funext errorEq]
    exact average
  have positions := phase_binding_marker_sum_eq_position setup mode runtime leaks bounds
    runtimePlan horizon scheduler initial initialLaw noise focal final trace chance factor behavior
  have nativePosition : marker behavior =
      ∑ owner ∈ Finset.univ.erase focal, ∑ index ∈ Finset.range (2 * horizon + 1),
        phaseRawBindingPositionWeight setup mode runtime leaks bounds runtimePlan horizon scheduler
          noise owner nativeBehavior ⟨some final, nativeTrace⟩ index := positions
  exact goodBounds.2.2.trans_eq (congrArg (_ + ·) (averageEq.trans nativePosition))

end Vegas
