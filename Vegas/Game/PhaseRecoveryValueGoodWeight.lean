/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingTaggedNoise
import Vegas.Game.PhaseRecoveryValueStrategy
import Vegas.Game.PhaseTimingCommitmentProduct
import Vegas.Game.PhaseRepairMarkedRecords
import GameTheoryExtensions.Protocol.OwnPlayPrefix

/-! # Whole-history weights retaining every nonbinding raw contribution -/

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

private theorem recorded_plan_atom_split
    (fallback : ∀ who, (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slot : ℝ) (slotNonnegative : 0 ≤ slot) (slotBounded : slot ≤ 1)
    (parts : Player → (p : Pool) → Parts p) (who : Player)
    {state : (E).State} (trace : (E).Trace state)
    (record : (N).InfoState who × (E).Action who)
    (member : record ∈ (N).ownPlay who trace) :
    ((((phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
      fallback wellFormed source noise nonnegative bounded slot slotNonnegative slotBounded
        parts who record.1).map Subtype.val) (some record.2)).toReal) =
      noise * ((((menu).uniformPolicy initial horizon scheduler who record.1).map Subtype.val)
        (some record.2)).toReal +
      (1 - noise) * ((((phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon
        scheduler bound fallback wellFormed source 0 (by norm_num) (by norm_num) slot
          slotNonnegative slotBounded parts who record.1).map Subtype.val)
            (some record.2)).toReal) := by
  classical
  obtain ⟨before, after, prior, joint, legal, realized, _prefix, info, _selected⟩ :=
    (N).exists_tracePrefix_of_mem_ownPlay trace member
  have played : record.1 ∈ (N).playedInformation who := by
    rw [← info]
    exact (N).mem_playedInformation (history := ⟨before, prior⟩) legal.1
  let agent : Agent := ⟨who, ⟨record.1, played⟩⟩
  have law (level : ℝ) (positive : 0 ≤ level) (small : level ≤ 1) :
      phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed source level positive small slot slotNonnegative slotBounded parts
          who record.1 =
      phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
        wellFormed source level positive small slot slotNonnegative slotBounded agent
          (parts who (pool agent)) := by
    exact (N).agentBehavior_at (N).playedInformation fallback _ agent
  rw [law noise nonnegative bounded, law 0 (by norm_num) (by norm_num),
    phaseTimingComponent_raw_mixture, mix_map, mix_apply_toReal]

open Classical in
/-- On an actual complete native history, removing only foreign binding SEND
raw summands leaves a nonnegative weight below the original response product.
Its deficit is bounded by the exact single-mark products. All other noisy
atoms remain literal, including prior opening WAIT and source omission. -/
theorem phaseTimingPlanPolicy_binding_good_product
    (fallback : ∀ who, (N).Policy who) (wellFormed : setup.WellFormed)
    (source : Player → setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slot : ℝ) (slotNonnegative : 0 ≤ slot) (slotBounded : slot ≤ 1)
    (parts : Player → (p : Pool) → Parts p)
    (focal : Player) (intervention : (N).BehavioralPolicy focal)
    {state : (E).State} (trace : (E).Trace state) :
    let profile := fun who => phaseTimingPlanProfile setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed (source who) noise nonnegative bounded slot
        slotNonnegative slotBounded parts who
    let zero := fun who => phaseTimingPlanProfile setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed (source who) 0 (by norm_num) (by norm_num) slot
        slotNonnegative slotBounded parts who
    let actual := Function.update profile focal intervention
    let records := fun who => (N).ownPlay who trace
    let Index := (who : Player) × Fin (records who).length
    let record := fun index : Index => (records index.1)[index.2.val]
    let marked := fun index : Index => index.1 ≠ focal ∧
      phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan horizon scheduler
        index.1 (record index)
    let atom := fun index : Index =>
      (((actual index.1 (record index).1).map Subtype.val) (some (record index).2)).toReal
    let raw := fun index : Index => if marked index then noise *
      ((((menu).uniformPolicy initial horizon scheduler index.1 (record index).1).map Subtype.val)
        (some (record index).2)).toReal else 0
    let retained := fun index : Index => if marked index then (1 - noise) *
      (((zero index.1 (record index).1).map Subtype.val) (some (record index).2)).toReal
      else atom index
    (∀ index, 0 ≤ retained index ∧ retained index ≤ atom index ∧
      atom index = raw index + retained index) ∧
      (∏ index, retained index) ≤ ∏ index, atom index ∧
      (∏ index, atom index) ≤ (∏ index, retained index) +
        ∑ index, raw index * ∏ other ∈ Finset.univ.erase index, atom other := by
  intro profile zero actual records Index record marked atom raw retained
  have split (index : Index) : atom index = raw index + retained index := by
    by_cases selected : marked index
    · have foreign : index.1 ≠ focal := selected.1
      dsimp only [atom, raw, retained]
      rw [ite_eq_left selected, ite_eq_left selected]
      dsimp only [actual]
      rw [Function.update_of_ne foreign]
      exact recorded_plan_atom_split setup mode runtime leaks bounds initial horizon scheduler
        bound fallback wellFormed (source index.1) noise nonnegative bounded slot slotNonnegative
          slotBounded parts index.1 trace (record index) (List.getElem_mem index.2.isLt)
    · simp only [raw, retained, ite_eq_right selected, zero_add]
  have rawNonnegative (index : Index) : 0 ≤ raw index := by
    dsimp only [raw]
    split_ifs
    · exact mul_nonneg nonnegative ENNReal.toReal_nonneg
    · exact le_rfl
  have retainedNonnegative (index : Index) : 0 ≤ retained index := by
    dsimp only [retained]
    split_ifs
    · exact mul_nonneg (sub_nonneg.mpr bounded) ENNReal.toReal_nonneg
    · exact ENNReal.toReal_nonneg
  have lower (index : Index) : retained index ≤ atom index := by
    rw [split index]
    exact le_add_of_nonneg_left (rawNonnegative index)
  refine ⟨fun index => ⟨retainedNonnegative index, lower index, split index⟩,
    Finset.prod_le_prod₀ (fun index _ => retainedNonnegative index)
      (fun index _ => lower index), ?_⟩
  have upper := prod_le_trimmed_add_marked Finset.univ atom raw
    (fun index _ => rawNonnegative index) (fun index _ => by
      rw [split index]
      exact le_add_of_nonneg_right (retainedNonnegative index))
  have subtracted : (fun index => atom index - raw index) = retained := by
    funext index
    rw [split index]
    ring
  simpa only [subtracted] using upper

open Classical in
/-- Every ORIGINAL immutable source-policy/full-plan member gives a whole-history
weight retaining all nonbinding noisy atoms. The actual initialized runtime
reach weight lies between that weight and its exact foreign RAW-binding marked
sum, with the SAME scheduler/chance factor derived from the genuine trace. -/
theorem phaseTimingPlanPolicy_binding_good_weight
    (fallback : ∀ who, (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (members : (who : Player) → (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slot : ℝ) (slotNonnegative : 0 ≤ slot) (slotBounded : slot ≤ 1)
    (parts : Player → (p : Pool) → Parts p)
    (focal : Player) (intervention : (N).BehavioralPolicy focal)
    {state : (E).State} (trace : (E).Trace state) :
    let source := fun who =>
      setup.commitRecoveryValueAssessment wellFormed assessment who (members who)
    let profile := fun who => phaseTimingPlanProfile setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed (source who) noise nonnegative bounded slot
        slotNonnegative slotBounded parts who
    let zero := fun who => phaseTimingPlanProfile setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed (source who) 0 (by norm_num) (by norm_num) slot
        slotNonnegative slotBounded parts who
    let actual := Function.update profile focal intervention
    let records := fun who => (N).ownPlay who trace
    let Index := (who : Player) × Fin (records who).length
    let record := fun index : Index => (records index.1)[index.2.val]
    let marked := fun index : Index => index.1 ≠ focal ∧
      phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan horizon scheduler
        index.1 (record index)
    let atom := fun index : Index =>
      (((actual index.1 (record index).1).map Subtype.val) (some (record index).2)).toReal
    let raw := fun index : Index => if marked index then noise *
      ((((menu).uniformPolicy initial horizon scheduler index.1 (record index).1).map Subtype.val)
        (some (record index).2)).toReal else 0
    let retained := fun index : Index => if marked index then (1 - noise) *
      (((zero index.1 (record index).1).map Subtype.val) (some (record index).2)).toReal
      else atom index
    ∃ chance : ℝ, 0 ≤ chance ∧
      (∀ players : ∀ who, (N).BehavioralPolicy who,
        ((N).historyReachWeight players ⟨state, trace⟩).toReal =
          chance * ∏ who, (N).ownPlayReachProbability (players who) (records who)) ∧
      0 ≤ chance * ∏ index, retained index ∧
      chance * (∏ index, retained index) ≤
        ((N).historyReachWeight actual ⟨state, trace⟩).toReal ∧
      ((N).historyReachWeight actual ⟨state, trace⟩).toReal ≤
        chance * (∏ index, retained index) +
          chance * ∑ index, raw index * ∏ other ∈ Finset.univ.erase index, atom other := by
  intro source profile zero actual records Index record marked atom raw retained
  have product := phaseTimingPlanPolicy_binding_good_product setup mode runtime leaks bounds
    runtimePlan initial horizon
    scheduler bound fallback wellFormed source noise nonnegative bounded slot slotNonnegative
      slotBounded parts focal intervention trace
  obtain ⟨suffixes, suffixEq, _provenance, chance, chanceNonnegative, factor⟩ :=
    (N).exists_continuation_ownPlay_factor (.start : (E).Trace (E).init) trace
      (TracePrefix.start trace)
  have suffixIdentity (who : Player) : suffixes who = records who := by
    simpa only [records, InfoSignals.ownPlay, List.append_nil] using (suffixEq who).symm
  have reach (players : ∀ who, (N).BehavioralPolicy who) :
      ((N).historyReachWeight players ⟨state, trace⟩).toReal =
        chance * ∏ who, (N).ownPlayReachProbability (players who) (records who) := by
    simpa only [historyReachWeight, runBehavioral, Trace.length, Nat.sub_zero, suffixIdentity,
      ExecutionProtocol.initHistory]
      using factor players
  have whole : ((N).historyReachWeight actual ⟨state, trace⟩).toReal =
      chance * ∏ index, atom index := by
    rw [reach]
    congr 1
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro who _
    have array := (N).ownPlayReachProbability_ofFn who (actual who)
      (fun index : Fin (records who).length => (records who)[index.val])
    simpa only [List.ofFn_getElem] using array
  refine ⟨chance, chanceNonnegative, reach, ?_, ?_, ?_⟩
  · exact mul_nonneg chanceNonnegative (Finset.prod_nonneg fun index _ => (product.1 index).1)
  · rw [whole]
    exact mul_le_mul_of_nonneg_left product.2.1 chanceNonnegative
  · rw [whole]
    simpa only [mul_add] using mul_le_mul_of_nonneg_left product.2.2 chanceNonnegative

end Vegas
