/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueMarkedProfile
import Interaction.ReactiveMenuLikelihood
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

/-! # Intrinsic finite-native raw marks from the original owner posteriors -/

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
  (initial : PMF (PhaseRuntimeState (serviceGraph setup mode)))
  (initialLaw : initial =
    (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    initial horizon
      scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    initial horizon
      scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs
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

local instance nativeMarkPoolFintype : Fintype Pool := Fintype.ofFinite _

include initialLaw

open Classical in
/-- The SAME actual transition coefficient and original per-owner posterior
average a foreign binding RAW mark to its intrinsic finite native path factors.
The focal intervention, pre-entry RAW recall and every original memory tag are
retained. Only the marked SEND atom is replaced; accepted source failures remain
in all other exact noisy response factors. -/
theorem phaseTimingPlanPolicy_native_mark_expect_of_history
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
    (otherSuffix : Player → List (app).PlayerEntry)
    (replayCovered : ∀ past view response, response ∈ (replay past view).support →
      response ∈ (menu).actions focal past view) (chance : ℝ) :
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
    let profile := fun observer => (menu).restrictPolicy initial horizon scheduler observer
      (behavior observer)
    let raw := phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler
      noise who (some (control.execution.recall who, control.execution.observe (app) who),
        sentRecord.action)
    let likelihood := fun observer memory =>
      let native := (menu).restrictPolicy initial horizon scheduler observer
        (family observer memory)
      if observer = who then
        (N).ownPlayReachProbability native ((app).ownPlayFrom (entryRecall observer) before) * raw *
          (N).ownPlayReachProbability native
            ((app).ownPlayFrom (control.execution.recall who ++ [sentRecord]) suffix)
      else (N).ownPlayReachProbability native
        ((app).ownPlayFrom (entryRecall observer) (otherSuffix observer))
    expect (independentProduct fun observer =>
      ((app).policyMixture (original observer) (family observer)).posterior
        (entryRecall observer))
          (fun memories => chance * ∏ observer, likelihood observer (memories observer)) =
      chance * ∏ observer, if observer = who then
        (N).ownPlayReachProbability (profile observer)
            ((app).ownPlayFrom (entryRecall observer) before) * raw *
          (N).ownPlayReachProbability (profile observer)
            ((app).ownPlayFrom (control.execution.recall who ++ [sentRecord]) suffix)
        else (N).ownPlayReachProbability (profile observer)
          ((app).ownPlayFrom (entryRecall observer) (otherSuffix observer)) := by
  subst initial
  let initial := (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)
  intro original family behavior profile raw likelihood
  let physicalLikelihood := fun observer memory => if observer = who then
      ((((app).privateTranscriptFrom (entryRecall observer) before).map (fun record =>
        family observer memory record.1.1 record.1.2 record.2)).prod).toReal * raw *
          ((((app).privateTranscriptFrom
            (control.execution.recall who ++ [sentRecord]) suffix).map
            (fun record => family observer memory record.1.1 record.1.2 record.2)).prod).toReal
      else ((((app).privateTranscriptFrom (entryRecall observer) (otherSuffix observer)).map
        (fun record => family observer memory record.1.1 record.1.2 record.2)).prod).toReal
  have memberCovered (observer memory past view response)
      (supported : response ∈ (family observer memory past view).support) :
      response ∈ (menu).actions observer past view := by
    dsimp only [family] at supported
    by_cases same : observer = focal
    · subst observer
      simp only [↓reduceIte] at supported
      exact replayCovered past view response supported
    · rw [ite_eq_right same] at supported
      exact phaseTimingPlanPolicy_covered setup mode runtime leaks bounds initial horizon scheduler
        bound fallback wellFormed _ noise noiseNonnegative noiseBounded slotWeight slotNonnegative
          slotBounded memory.1 observer past view response supported
  have likelihoodEq : likelihood = physicalLikelihood := by
    funext observer memory
    dsimp only [likelihood, physicalLikelihood]
    split
    · rw [(menu).ownPlayFrom_restrictPolicy initial horizon scheduler observer
        (family observer memory) (memberCovered observer memory),
      (menu).ownPlayFrom_restrictPolicy initial horizon scheduler observer
        (family observer memory) (memberCovered observer memory)]
    · exact (menu).ownPlayFrom_restrictPolicy initial horizon scheduler observer
        (family observer memory) (memberCovered observer memory) _ _
  have covered (observer past view response)
      (supported : response ∈ (behavior observer past view).support) :
      response ∈ (menu).actions observer past view := by
    dsimp only [behavior] at supported
    rw [(app).policyMixture_policy, PMF.support_bind] at supported
    obtain ⟨memory, _possible, supported⟩ := Set.mem_iUnion₂.mp supported
    exact memberCovered observer memory past view response supported
  have average := phaseTimingPlanPolicy_marked_profile_expect_of_history setup mode runtime leaks
    bounds runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed finite
      weights noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded who
        control trace active clear event payload binding request unsent final finalTrace finalClear
          sentRecord suffix recalled viewed material transmitted candidate named entryRecall before
            callbackRecall focal foreign replay otherSuffix
  rw [likelihoodEq, expect_const_mul, average]
  apply congrArg (chance * ·)
  apply Finset.prod_congr rfl
  intro observer _member
  by_cases selected : observer = who
  · rw [ite_eq_left selected, ite_eq_left selected]
    rw [(menu).ownPlayFrom_restrictPolicy initial horizon scheduler observer
        (behavior observer) (covered observer),
      (menu).ownPlayFrom_restrictPolicy initial horizon scheduler observer
        (behavior observer) (covered observer)]
  · rw [ite_eq_right selected, ite_eq_right selected]
    exact ((menu).ownPlayFrom_restrictPolicy initial horizon scheduler observer
      (behavior observer) (covered observer) _ _).symm

end Vegas
