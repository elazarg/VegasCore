/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueMarkedSuffix
import GameTheoryExtensions.Math.Probability.ProductExpectation
import Vegas.Game.PhaseRawBindingContribution
import Interaction.ReactiveMixtureLikelihood
import Vegas.Game.PhaseRecoveryValueFutureProduct
import Vegas.Game.PhaseRecoveryValueFuture
import Interaction.ReactiveMixtureExtraCoordinate
import Vegas.Game.CommitRecoveryValuePlan
import Interaction.ReactiveMixtureAtoms
import Vegas.Game.PhaseSourceRecordedPosition
import Vegas.Pending.PhaseBindingMenuShape
import Vegas.Pending.PhaseBindingIdleMenu
import Interaction.ReactiveRecordedResponse

/-! # Original per-owner memory averaging of an actual marked path -/

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

local instance markedProfilePoolFintype : Fintype Pool := Fintype.ofFinite _

omit [Fintype Player] in
private theorem likelihood_bounds (policy : (app).Policy)
    (past records : List (app).PlayerEntry) :
    0 ≤ ((((app).privateTranscriptFrom past records).map (fun record =>
      policy record.1.1 record.1.2 record.2)).prod).toReal ∧
    ((((app).privateTranscriptFrom past records).map (fun record =>
      policy record.1.1 record.1.2 record.2)).prod).toReal ≤ 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · rw [(app).privateTranscriptFrom_product]
    exact Finset.prod_le_one₀ (fun _ _ => ENNReal.toReal_nonneg)
      (fun _ _ => pmf_toReal_apply_le_one _ _)

open Classical in
/-- The genuine original posterior of EVERY owner averages a marked foreign
binding-send path to the intrinsic RAW atom and the same behavioral path factors.
The focal intervention ignores its unused memory; all original owner tags and
old full recalls remain in the independent posterior at the actual entry. -/
theorem phaseTimingPlanPolicy_marked_profile_expect_of_history
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (active : control.actor = some who)
    (clear : control.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (final : (app).Control)
    (finalTrace : ((menu).protocol initial horizon scheduler).Trace (some final))
    (finalClear : final.execution.application.current.excluded = ∅)
    (sentRecord : (app).PlayerEntry) (suffix : List (app).PlayerEntry)
    (recalled : final.execution.recall who = control.execution.recall who ++ sentRecord :: suffix)
    (viewed : sentRecord.beforeView = control.execution.observe (app) who)
    (material : WitnessedSubmission (serviceGraph setup mode))
    (transmitted : sentRecord.action.transmission = some material)
    (candidate : Handle (serviceGraph setup mode))
    (named : material.call.packet = .commitment event candidate)
    (entryRecall : Player → List (app).PlayerEntry) (before : List (app).PlayerEntry)
    (callbackRecall : control.execution.recall who = entryRecall who ++ before)
    (focal : Player) (foreign : who ≠ focal) (replay : (app).Policy)
    (otherSuffix : Player → List (app).PlayerEntry) :
    let original := fun observer => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy observer).map
        (Prod.mk plan)
    let family := fun observer memory => if observer = focal then replay else
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed
          (setup.commitRecoveryValueAssessment wellFormed assessment observer memory.2)
            noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
              memory.1 observer
    let behavior := fun observer => ((app).policyMixture (original observer)
      (family observer)).policy
    let raw := phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler
      noise who (some (control.execution.recall who, control.execution.observe (app) who),
        sentRecord.action)
    let likelihood := fun observer memory => if observer = who then
      ((((app).privateTranscriptFrom (entryRecall observer) before).map (fun record =>
        family observer memory record.1.1 record.1.2 record.2)).prod).toReal * raw *
          ((((app).privateTranscriptFrom
            (control.execution.recall who ++ [sentRecord]) suffix).map
            (fun record => family observer memory record.1.1 record.1.2 record.2)).prod).toReal
      else ((((app).privateTranscriptFrom (entryRecall observer) (otherSuffix observer)).map
        (fun record => family observer memory record.1.1 record.1.2 record.2)).prod).toReal
    expect (independentProduct fun observer =>
      ((app).policyMixture (original observer) (family observer)).posterior
        (entryRecall observer))
        (fun memories => ∏ observer, likelihood observer (memories observer)) =
      ∏ observer, if observer = who then
        ((((app).privateTranscriptFrom (entryRecall observer) before).map (fun record =>
          behavior observer record.1.1 record.1.2 record.2)).prod).toReal * raw *
            ((((app).privateTranscriptFrom
            (control.execution.recall who ++ [sentRecord]) suffix).map
              (fun record => behavior observer record.1.1 record.1.2 record.2)).prod).toReal
        else ((((app).privateTranscriptFrom (entryRecall observer) (otherSuffix observer)).map
          (fun record => behavior observer record.1.1 record.1.2 record.2)).prod).toReal := by
  intro original family behavior raw likelihood
  have rawNonnegative : 0 ≤ raw := mul_nonneg noiseNonnegative ENNReal.toReal_nonneg
  have mulBound {first second : ℝ} (firstNonnegative : 0 ≤ first)
      (firstBounded : first ≤ 1) (secondBounded : second ≤ 1) : first * second ≤ 1 :=
    (mul_le_mul_of_nonneg_left secondBounded firstNonnegative).trans
      (by simpa only [mul_one] using firstBounded)
  have rawBounded : raw ≤ 1 := mulBound noiseNonnegative noiseBounded
    (pmf_toReal_apply_le_one _ _)
  have nonnegative (observer memory) : 0 ≤ likelihood observer memory := by
    dsimp only [likelihood]
    split
    · exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg rawNonnegative)
        ENNReal.toReal_nonneg
    · exact ENNReal.toReal_nonneg
  have bounded (observer memory) : likelihood observer memory ≤ 1 := by
    dsimp only [likelihood]
    split
    · exact mulBound (mul_nonneg ENNReal.toReal_nonneg rawNonnegative)
        (mulBound ENNReal.toReal_nonneg
          (likelihood_bounds setup mode runtime leaks (family observer memory) _ _).2 rawBounded)
            (likelihood_bounds setup mode runtime leaks (family observer memory) _ _).2
    · exact (likelihood_bounds setup mode runtime leaks (family observer memory) _ _).2
  rw [expect_independentProduct_prod _ likelihood nonnegative bounded]
  apply Finset.prod_congr rfl
  intro observer _member
  by_cases selected : observer = who
  · subst observer
    simp only [likelihood, ↓reduceIte]
    have average := phaseTimingPlanPolicy_marked_suffix_expect_of_history setup mode runtime
      leaks bounds runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed
        finite weights noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
          who control trace active clear event payload binding request unsent final finalTrace
            finalClear sentRecord suffix recalled viewed material transmitted candidate named
              (entryRecall who) before callbackRecall
    simpa only [family, ite_eq_right foreign, original, behavior, ↓reduceIte] using average
  · simp only [likelihood, ite_eq_right selected]
    have average := (app).policyMixture_likelihood_expect (original observer) (family observer)
      (entryRecall observer) (otherSuffix observer) (fun _ => (1 : ℝ))
    simpa only [mul_one, expect_constant] using average

end Vegas
