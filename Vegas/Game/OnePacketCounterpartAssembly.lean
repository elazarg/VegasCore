/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketBeliefPartsWiring
import Vegas.Game.OnePacketCertificateCounterpart
import Vegas.Game.OnePacketCounterpartRatio

/-! # Honest counterparts from domination

The honest-counterpart inputs at a site follow from a regular counterpart of
every irregular history whose reach dominates the history's reach up to
`slack * scale n / floor n ^ depth`, at the tremble scale over the combined floor
of the source sequence to the depth: the common weight is the reach over the
cube of the scale (`Vegas.OnePacketCounterpartInputs.ofDomination`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  [Finite setup.intendedProtocol.History]

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

/-- **The honest-counterpart inputs from domination.** At the tremble scale over
the combined floor of the source sequence to a depth, a regular counterpart of
every irregular history whose reach is at least the history's reach over
`slack * scale n / floor n ^ depth` gives the honest-counterpart inputs, with the
reach over the cube of the scale as the common weight. -/
def OnePacketCounterpartInputs.ofDomination
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    {who : Player} {site : (onePacketN).InformationSite who}
    {scale : ℕ → ℝ} (scale_pos : ∀ n, 0 < scale n) (depth : ℕ)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup leaks bounds horizon scheduler (sequence n)) depth n)
    (slack : ℝ) (slack_nonneg : 0 ≤ slack)
    (counterpart : ℕ → (onePacketN).InformationHistory who site.1 →
      (onePacketN).InformationHistory who site.1)
    (counterpart_regular : ∀ n history, ¬ RegularTrace setup leaks bounds horizon scheduler
        (sequence n) who history.1.trace →
      RegularTrace setup leaks bounds horizon scheduler (sequence n) who
        (counterpart n history).1.trace)
    (dominated : ∀ n history, ¬ RegularTrace setup leaks bounds horizon scheduler (sequence n)
        who history.1.trace →
      ((onePacketN).historyReachWeight (targetSequence n).strategy history.1).toReal ≤
        slack * scale n / combinedFloor setup leaks bounds horizon scheduler (sequence n) ^ depth *
          ((onePacketN).historyReachWeight (targetSequence n).strategy
            (counterpart n history).1).toReal) :
    OnePacketCounterpartInputs setup leaks bounds horizon scheduler sequence targetSequence
      site :=
  have fields := fun n => counterpart_fields_of_domination
    (fun history : (onePacketN).InformationHistory who site.1 =>
      ((onePacketN).historyReachWeight (targetSequence n).strategy history.1).toReal)
    (counterpart n) (scale_pos n) (combinedFloor_pos setup leaks bounds horizon scheduler
      (sequence n))
    (fun history => ¬ RegularTrace setup leaks bounds horizon scheduler (sequence n) who
      history.1.trace) (dominated n)
  OnePacketCounterpartInputs.ofCertificate scale_pos depth scaleEq slack slack_nonneg counterpart
    (fun n history => ((onePacketN).historyReachWeight (targetSequence n).strategy
      history.1).toReal / scale n ^ 3)
    counterpart_regular (fun n => (fields n).1) (fun n => (fields n).2)

variable [DecidableEq (CellTy Player L)]

omit [Finite setup.intendedProtocol.History] [DecidableEq (CellTy Player L)]
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- A history at a decision input is initialized and decodes. -/
theorem decoded_of_decision {who : Player} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (history : (onePacketN).InformationHistory who (some (past, view))) :
    ∃ current p, history.1.state = some current ∧
      decodedPoint setup current.execution.application.config = some p := by
  obtain ⟨⟨state, trace⟩, seen⟩ := history
  cases state with
  | none =>
      rw [onePacket_infoOf] at seen
      cases seen
  | some current =>
      obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
        (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler trace current rfl
      exact ⟨current, _, rfl, decodedPoint_eq residual⟩

omit [Finite setup.intendedProtocol.History] [DecidableEq (CellTy Player L)] in
/-- **A debt-free witness.** At a site whose agent is forced and owes no failure,
some history of the site decodes to a point at which nobody owes a failure. -/
theorem exists_debtFree_witness {who : Player} {site : (onePacketN).InformationSite who}
    (forced : ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
    (notOwing : ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site)) :
    ∃ (witness : (onePacketN).InformationHistory who site.1)
      (control : (application setup leaks).Control) (w : ProtocolState setup.program),
      witness.1.state = some control ∧
        decodedPoint setup control.execution.application.config = some w ∧
        ∀ player, ¬ ProtocolState.OwesFailure player setup.program w := by
  have isForced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup)
      horizon scheduler who site.1 := not_not.mp forced
  obtain ⟨history, info, forcedState⟩ := isForced
  obtain ⟨state, trace⟩ := history
  cases state with
  | none => exact forcedState.elim
  | some control =>
      obtain ⟨point, decoded, forcedPoint⟩ := (forcedState_iff_decodedPoint control).mp forcedState
      refine ⟨⟨⟨some control, trace⟩, info⟩, control, point, rfl, decoded, fun player owes => ?_⟩
      by_cases same : player = who
      · subst same
        exact notOwing ⟨⟨⟨some control, trace⟩, info⟩, point, decoded, owes⟩
      · exact (forcedPoint.2 player same).2 owes

variable [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History]

omit [Finite setup.intendedProtocol.History] [DecidableEq (CellTy Player L)]
  [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History] in
/-- Along a vanishing error, the factorization error of a history length is
eventually at most a half, and the error at most one. -/
theorem eventually_error_small {error : ℕ → ℝ} (tendsto : Tendsto error atTop (nhds 0))
    (power : ℕ) :
    ∃ bound, ∀ n, bound ≤ n → (1 + error n) ^ power - 1 ≤ 1 / 2 ∧ error n ≤ 1 := by
  have limit : Tendsto (fun n => (1 + error n) ^ power - 1) atTop (nhds ((1 + 0) ^ power - 1)) :=
    ((tendsto_const_nhds.add tendsto).pow power).sub tendsto_const_nhds
  rw [add_zero, one_pow, sub_self] at limit
  have half := limit.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have one := tendsto.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨bound, holds⟩ := Filter.eventually_atTop.mp (half.and one)
  exact ⟨bound, holds⟩

/-- Certificate reach comparisons at the combined-floor tremble scale yield
uniform counterpart inputs. The eventual ratio estimate bounds the tail;
finite fully mixed early stages supply the remaining uniform slack. -/
def OnePacketCounterpartInputs.ofReachComparisons
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {scale : ℕ → ℝ} (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup leaks bounds horizon scheduler (sequence n)) (2 * horizon + 2) n)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    {who : Player} {site : (onePacketN).InformationSite who}
    (comparisons :
      let floor := fun n => combinedFloor setup leaks bounds horizon scheduler (sequence n)
      ∀ n (history : (onePacketN).InformationHistory who site.1),
      ∃ counterpart : (onePacketN).InformationHistory who site.1,
        ¬ RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace →
        RegularTrace setup leaks bounds horizon scheduler (sequence n) who counterpart.1.trace ∧
        ((1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) ^
            (2 * horizon + 1) - 1 < 1 →
        ((onePacketN).historyReachWeight
            (certificateProfile setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one weights n) history.1).toReal ≤
          (1 + ((1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) ^
              (2 * horizon + 1) - 1)) /
            (1 - ((1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) ^
              (2 * horizon + 1) - 1)) *
            (slotError (scale n) (floor n) (trembleSlots setup bounds).card *
              (1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) *
              counterpartFactor setup leaks bounds horizon scheduler sequence scale floor n ^
                (2 * horizon + 1)) *
          ((onePacketN).historyReachWeight
            (certificateProfile setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one weights n) counterpart.1).toReal)) :
    OnePacketCounterpartInputs setup leaks bounds horizon scheduler sequence targetSequence
      site :=
  let floor := fun n => combinedFloor setup leaks bounds horizon scheduler (sequence n)
  have floor_pos : ∀ n, 0 < floor n := fun n => combinedFloor_pos setup leaks bounds horizon
    scheduler (sequence n)
  have floor_le_one : ∀ n, floor n ≤ 1 := fun n => combinedFloor_le_one setup leaks bounds horizon
    scheduler (sequence n)
  have floored : ∀ n, floor n ≤ contentFloor setup leaks bounds horizon scheduler (sequence n) :=
    fun n => combinedFloor_le_contentFloor setup leaks bounds horizon scheduler (sequence n)
  have error_tendsto : Tendsto (fun n => slotError (scale n) (floor n)
      (trembleSlots setup bounds).card) atTop (nhds 0) := by
    have tendsto := tendsto_slotError floor floor_pos floor_le_one (2 * horizon + 2)
      (trembleSlots setup bounds).card
    convert tendsto using 1
    funext n
    rw [scaleEq n]
  have strategyEq : ∀ n, (targetSequence n).strategy = certificateProfile setup leaks bounds
      horizon scheduler sequence scale scale_pos scale_le_one weights n := assembled
  let counterpart := fun n history => Classical.choose (comparisons n history)
  let reach := fun n (history : (onePacketN).InformationHistory who site.1) =>
    ((onePacketN).historyReachWeight (targetSequence n).strategy history.1).toReal
  let power := 2 * horizon + 1
  let constant := 3 * (2 * (2 * ((trembleSlots setup bounds).card : ℝ) + 2) *
    max (1 / initialFloor setup leaks bounds horizon scheduler) 4 ^ power)
  have bound := Classical.choose_spec (eventually_error_small error_tendsto power)
  let start := Classical.choose (eventually_error_small error_tendsto power)
  let early := ∑ n ∈ Finset.range start, ∑ history ∈
    (Set.toFinite (Set.univ : Set ((onePacketN).InformationHistory who site.1))).toFinset,
      reach n history * floor n ^ (2 * horizon + 2) /
        (scale n * reach n (counterpart n history))
  have reachPos : ∀ n history, 0 < reach n history := fun n history =>
    ENNReal.toReal_pos (historyReachWeight_pos_of_fullSupport (onePacketN)
      (targetSequence n).strategy (mixed n) history.1).ne' (PMF.apply_ne_top _ _)
  have termNonneg : ∀ n history, 0 ≤ reach n history * floor n ^ (2 * horizon + 2) /
      (scale n * reach n (counterpart n history)) := fun n history =>
    div_nonneg (mul_nonneg (reachPos n history).le (pow_nonneg (floor_pos n).le _))
      (mul_nonneg (scale_pos n).le (reachPos n _).le)
  have constantNonneg : 0 ≤ constant := by positivity
  OnePacketCounterpartInputs.ofDomination scale_pos (2 * horizon + 2) scaleEq
    (max constant early) (le_trans constantNonneg (le_max_left _ _)) counterpart
    (fun n history irregular =>
      ((Classical.choose_spec (comparisons n history)) irregular).1)
    (fun n history irregular => by
      have spec := (Classical.choose_spec (comparisons n history)) irregular
      change reach n history ≤ max constant early * scale n / floor n ^ (2 * horizon + 2) *
        reach n (counterpart n history)
      have positiveCounterpart := reachPos n (counterpart n history)
      have powerPos : 0 < floor n ^ (2 * horizon + 2) := pow_pos (floor_pos n) _
      by_cases late : start ≤ n
      · obtain ⟨errorHalf, errorLe⟩ := bound n late
        have errorNonneg : 0 ≤ slotError (scale n) (floor n) (trembleSlots setup bounds).card :=
          slotError_nonneg (scale_pos n).le (floor_pos n) _
        have factorNonneg : 0 ≤ (1 + slotError (scale n) (floor n)
            (trembleSlots setup bounds).card) ^ power - 1 := by
          have := one_le_pow₀ (n := power) (show (1 : ℝ) ≤ 1 + slotError (scale n) (floor n)
            (trembleSlots setup bounds).card by linarith)
          linarith
        have dominatedNative := spec.2 (by linarith)
        have reachEq : ∀ found : (onePacketN).InformationHistory who site.1,
            ((onePacketN).historyReachWeight (certificateProfile setup leaks bounds horizon
              scheduler sequence scale scale_pos scale_le_one weights n) found.1).toReal =
              reach n found := fun found => congrArg (fun profile =>
                ((onePacketN).historyReachWeight profile found.1).toReal) (strategyEq n).symm
        have dominated := (reachEq history).symm.trans_le
          (dominatedNative.trans_eq (congrArg (fun mass =>
            (1 + ((1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) ^
                (2 * horizon + 1) - 1)) /
              (1 - ((1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) ^
                (2 * horizon + 1) - 1)) *
              (slotError (scale n) (floor n) (trembleSlots setup bounds).card *
                (1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) *
                counterpartFactor setup leaks bounds horizon scheduler sequence scale floor n ^
                  (2 * horizon + 1)) * mass) (reachEq (counterpart n history))))
        have ratio := counterpartRatio_le (scale_pos n) (scale_le_one n) (floor_pos n)
          (floor_le_one n) (floored n) (initialFloor_pos setup leaks bounds horizon scheduler)
          (trembleSlots setup bounds).card errorNonneg errorLe errorLe power
        have factorLe : (1 + ((1 + slotError (scale n) (floor n)
            (trembleSlots setup bounds).card) ^ power - 1)) /
            (1 - ((1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) ^
              power - 1)) ≤ 3 := by
          rw [div_le_iff₀ (by linarith)]
          linarith
        have factorPos : 0 ≤ (1 + ((1 + slotError (scale n) (floor n)
            (trembleSlots setup bounds).card) ^ power - 1)) /
            (1 - ((1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) ^
              power - 1)) := div_nonneg (by linarith) (by linarith)
        have ratioNonneg : 0 ≤ slotError (scale n) (floor n) (trembleSlots setup bounds).card *
            (1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) *
            counterpartFactor setup leaks bounds horizon scheduler sequence scale floor n ^
              power :=
          mul_nonneg (mul_nonneg errorNonneg (by linarith))
            (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
        calc reach n history ≤ _ := dominated
          _ ≤ 3 * (2 * (2 * ((trembleSlots setup bounds).card : ℝ) + 2) *
                max (1 / initialFloor setup leaks bounds horizon scheduler) 4 ^ power *
                (scale n / floor n ^ (power + 1))) * reach n (counterpart n history) :=
            mul_le_mul_of_nonneg_right (mul_le_mul factorLe ratio ratioNonneg (by norm_num))
              positiveCounterpart.le
          _ = constant * scale n / floor n ^ (2 * horizon + 2) *
                reach n (counterpart n history) := by
            simp only [constant, power]
            ring
          _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right _ positiveCounterpart.le
            apply div_le_div_of_nonneg_right _ powerPos.le
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (scale_pos n).le
      · have inRange : n ∈ Finset.range start := Finset.mem_range.mpr (not_le.mp late)
        have inUniverse : history ∈ (Set.toFinite (Set.univ :
            Set ((onePacketN).InformationHistory who site.1))).toFinset := by
          simp
        have termLe : reach n history * floor n ^ (2 * horizon + 2) /
            (scale n * reach n (counterpart n history)) ≤ max constant early :=
          le_trans (le_trans (Finset.single_le_sum (fun history _ => termNonneg n history)
            inUniverse) (Finset.single_le_sum (fun n _ => Finset.sum_nonneg
              fun history _ => termNonneg n history) inRange)) (le_max_right _ _)
        rw [div_le_iff₀ (mul_pos (scale_pos n) positiveCounterpart)] at termLe
        rw [div_mul_eq_mul_div, le_div_iff₀ powerPos]
        simpa only [mul_assoc] using termLe)


end Vegas
