/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingPoolPlan
import Vegas.Game.PhaseTimingRawMixture
import GameTheoryExtensions.Analysis.Protocol.SupportedChoiceContinuation
import GameTheory.Math.Probability.ConditionalObservation

/-! # Same-profile raw-noise comparison with original entry and plan tags -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
      scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
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
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

/-- The finite strategy underlying the existing physical plan policy, with
one full original timing plan retained separately for every owner. -/
def phaseTimingPlanProfile
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : Player → (p : Pool) → Parts p) : ∀ who, (N).BehavioralPolicy who :=
  fun who => ((N).agentBehavior (N).playedInformation fallback fun agent =>
    phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
      wellFormed source noise nonnegative bounded slotWeight slotNonnegative slotBounded
        agent (parts who (pool agent))) who

/-- Decoding this finite profile is literally the existing original-plan
physical policy. No source or native response-law hypothesis is needed. -/
theorem phaseTimingPlanProfile_decode
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : Player → (p : Pool) → Parts p) (who : Player) :
    (menu).decodeProfile initial horizon scheduler
        (phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed source noise nonnegative bounded slotWeight slotNonnegative
            slotBounded parts) who =
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed source noise nonnegative bounded slotWeight slotNonnegative
          slotBounded (parts who) who := rfl

open Classical in
/-- Every original-plan choice retains its exact zero-noise summand. This
includes opening, waiting, free and inactive choices, not just binding sends. -/
theorem phaseTimingPlanProfile_noise_lower
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : Player → (p : Pool) → Parts p)
    (who : Player) (input : (N).InfoState who) (choice : (N).Choice who input) :
    (1 - noise) * ((phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed source 0 (by norm_num) (by norm_num) slotWeight
        slotNonnegative slotBounded parts who input) choice).toReal ≤
      ((phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed source noise nonnegative bounded slotWeight slotNonnegative
          slotBounded parts who input) choice).toReal := by
  dsimp only [phaseTimingPlanProfile, InformationModel.agentBehavior]
  by_cases present : input ∈ (N).playedInformation who
  · simp only [dite_eq_left present]
    rw [phaseTimingComponent_raw_mixture setup mode runtime leaks bounds initial horizon
      scheduler bound wellFormed source noise nonnegative bounded slotWeight slotNonnegative
        slotBounded ⟨who, ⟨input, present⟩⟩ (parts who (pool ⟨who, ⟨input, present⟩⟩)),
      mix_apply_toReal]
    exact le_add_of_nonneg_left (mul_nonneg nonnegative ENNReal.toReal_nonneg)
  · simp only [dite_eq_right present]
    exact mul_le_of_le_one_left ENNReal.toReal_nonneg (by linarith)

open Classical in
/-- A common original joint entry/plan prior retains all its correlations.
At arbitrary full entry histories, the existing finite-fuel continuation with
raw noise dominates the SAME zero-noise continuation. The focal intervention
is identical in both laws, so no explanation of its recorded RAW past is used. -/
theorem phaseTimingPlanProfile_tagged_noise_domination
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    {Entry : Type} (original : PMF Entry)
    (parts : Entry → Player → (p : Pool) → Parts p) (start : Entry →
      ((menu).protocol initial horizon scheduler).History)
    (focal : Player) (intervention : Entry → (N).BehavioralPolicy focal) (fuel : Nat) :
    let zero := fun index => Function.update
      (phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed source 0 (by norm_num) (by norm_num) slotWeight slotNonnegative
          slotBounded (parts index)) focal (intervention index)
    let noisy := fun index => Function.update
      (phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed source noise nonnegative bounded slotWeight slotNonnegative
          slotBounded (parts index)) focal (intervention index)
    let reference := original.bind fun index =>
      ((N).runBehavioralFrom (zero index) fuel (start index)).map (Prod.mk index)
    let actual := original.bind fun index =>
      ((N).runBehavioralFrom (noisy index) fuel (start index)).map (Prod.mk index)
    let factor := (1 - noise) ^ (Fintype.card Player * fuel)
    (∀ row, factor * (reference row).toReal ≤ (actual row).toReal) ∧
      PMF.WithinTV (1 - factor) reference actual := by
  intro zero noisy reference actual factor
  have choices (index : Entry) (who : Player) (input : (N).InfoState who)
      (choice : (N).Choice who input) :
      (1 - noise) * ((zero index who input) choice).toReal ≤
        ((noisy index who input) choice).toReal := by
    by_cases same : who = focal
    · subst who
      simp only [zero, noisy, Function.update_self]
      exact mul_le_of_le_one_left ENNReal.toReal_nonneg (by linarith)
    · simp only [zero, noisy, Function.update_of_ne same]
      exact phaseTimingPlanProfile_noise_lower setup mode runtime leaks bounds initial horizon
        scheduler bound fallback wellFormed source noise nonnegative bounded slotWeight
          slotNonnegative slotBounded (parts index) who input choice
  have continuation (index : Entry) (next : ((menu).protocol initial horizon scheduler).History) :
      factor * (((N).runBehavioralFrom (zero index) fuel (start index)) next).toReal ≤
        (((N).runBehavioralFrom (noisy index) fuel (start index)) next).toReal :=
    (N).runBehavioralFrom_domination_of_supported_choices (zero index) (noisy index)
      (1 - noise) (sub_nonneg.mpr bounded) (start index)
        (fun _ history _ who choice => choices index who ((N).infoOf who history.trace) choice)
          fuel next
  have tagged (index : Entry) (row : Entry ×
      ((menu).protocol initial horizon scheduler).History) :
      factor * ((((N).runBehavioralFrom (zero index) fuel (start index)).map
        (Prod.mk index)) row).toReal ≤
        ((((N).runBehavioralFrom (noisy index) fuel (start index)).map
          (Prod.mk index)) row).toReal := by
    have compared := prob_bind_ge_mul _ _ factor (continuation index)
      (fun history => PMF.pure (index, history)) row
    simpa only [← PMF.bind_pure_comp, Function.comp_def] using compared
  have lower (row : Entry × ((menu).protocol initial horizon scheduler).History) :
      factor * (reference row).toReal ≤ (actual row).toReal := by
    have compared := bind_supported_domination original original
      (fun index => ((N).runBehavioralFrom (zero index) fuel (start index)).map (Prod.mk index))
      (fun index => ((N).runBehavioralFrom (noisy index) fuel (start index)).map (Prod.mk index))
      1 factor zero_le_one (fun _ => by simp only [one_mul, le_refl])
        (fun index _ row => tagged index row) row
    simpa only [one_mul] using compared
  exact ⟨lower, PMF.WithinTV.of_domination reference actual factor
    (pow_le_one₀ (sub_nonneg.mpr bounded) (by linarith)) lower⟩


open Classical in
/-- Conditioning the actual tagged noisy continuation is close to the SAME
zero-noise continuation when that exact zero-noise native input has positive
mass. The denominator is retained; no binding-only RAW limit is used to erase
opening, waiting, preparation or original entry/plan likelihoods. -/
theorem phaseTimingPlanProfile_tagged_noise_input_bound
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (small : noise < 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    {Entry : Type} (original : PMF Entry)
    (parts : Entry → Player → (p : Pool) → Parts p) (start : Entry →
      ((menu).protocol initial horizon scheduler).History)
    (focal : Player) (intervention : Entry → (N).BehavioralPolicy focal) (fuel : Nat)
    (observed : (N).InfoState focal) :
    let zero := fun index => Function.update
      (phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed source 0 (by norm_num) (by norm_num) slotWeight slotNonnegative
          slotBounded (parts index)) focal (intervention index)
    let noisy := fun index => Function.update
      (phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed source noise nonnegative small.le slotWeight slotNonnegative
          slotBounded (parts index)) focal (intervention index)
    let reference := original.bind fun index =>
      ((N).runBehavioralFrom (zero index) fuel (start index)).map (Prod.mk index)
    let actual := original.bind fun index =>
      ((N).runBehavioralFrom (noisy index) fuel (start index)).map (Prod.mk index)
    let observe := fun row : Entry × ((menu).protocol initial horizon scheduler).History =>
      (N).infoOf focal row.2.trace
    let factor := (1 - noise) ^ (Fintype.card Player * fuel)
    observed ∈ (reference.map observe).support →
      observed ∈ (actual.map observe).support ∧
      ∀ row, |((fiberPosterior actual observe observed) row).toReal -
          ((fiberPosterior reference observe observed) row).toReal| ≤
        (1 - factor) / (factor * ((reference.map observe) observed).toReal) := by
  intro zero noisy reference actual observe factor present
  have lower := (phaseTimingPlanProfile_tagged_noise_domination setup mode runtime leaks bounds
    initial horizon scheduler bound fallback wellFormed source noise nonnegative small.le
      slotWeight slotNonnegative slotBounded original parts start focal intervention fuel).1
  have factorPositive : 0 < factor := pow_pos (sub_pos.mpr small) _
  have factorBounded : factor ≤ 1 :=
    pow_le_one₀ (sub_nonneg.mpr small.le) (by linarith)
  obtain ⟨witness, supported, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp present
  have referenceMeet : ∃ row ∈ observe ⁻¹' {observed}, row ∈ reference.support :=
    ⟨witness, equal, supported⟩
  have witnessPositive : 0 < (reference witness).toReal :=
    ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp supported) (PMF.apply_ne_top _ _)
  have actualPositive : 0 < (actual witness).toReal :=
    (mul_pos factorPositive witnessPositive).trans_le (lower witness)
  have actualSupported : witness ∈ actual.support :=
    (PMF.mem_support_iff _ _).mpr (ENNReal.toReal_pos_iff.mp actualPositive).1.ne'
  have actualMeet : ∃ row ∈ observe ⁻¹' {observed}, row ∈ actual.support :=
    ⟨witness, equal, actualSupported⟩
  constructor
  · exact (PMF.mem_support_map_iff _ _ _).mpr ⟨witness, actualSupported, equal⟩
  intro row
  have compared := conditional_domination_bound reference actual (observe ⁻¹' {observed})
    referenceMeet actualMeet factor factorPositive factorBounded lower row
  have mass : reference.toOuterMeasure (observe ⁻¹' {observed}) =
      (reference.map observe) observed := by
    rw [← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton]
  rw [mass] at compared
  rw [fiberPosterior_eq_filter _ _ actualMeet, fiberPosterior_eq_filter _ _ referenceMeet]
  simpa only [Set.preimage, Set.mem_singleton_iff] using compared

end Vegas
