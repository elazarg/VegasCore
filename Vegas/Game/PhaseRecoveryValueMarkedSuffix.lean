/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueSendPosterior
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

/-! # Averaged original-member raw-send likelihood at an actual callback -/

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

local instance markedSuffixPoolFintype : Fintype Pool := Fintype.ofFinite _

open Classical in
/-- Averaging the actual marked own-response suffix over its ORIGINAL private
members gives exactly the intrinsic native RAW atom times the SAME behavioral
prefix and suffix likelihoods. No member-origin interpretation or future-law
identity is supplied: the actual recorded send derives the needed posterior law. -/
theorem phaseTimingPlanPolicy_marked_suffix_expect_of_history
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
    (entryPast before : List (app).PlayerEntry)
    (callbackRecall : control.execution.recall who = entryPast ++ before) :
    let sourcePrior := setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who
    let original := (independentProduct weights).bind fun plan => sourcePrior.map (Prod.mk plan)
    let family := fun memory => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who memory.2) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded memory.1 who
    let raw := phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler
      noise who (some (control.execution.recall who, control.execution.observe (app) who),
        sentRecord.action)
    expect (((app).policyMixture original family).posterior entryPast) (fun memory =>
        ((((app).privateTranscriptFrom entryPast before).map (fun record =>
          family memory record.1.1 record.1.2 record.2)).prod).toReal * raw *
            ((((app).privateTranscriptFrom
              (control.execution.recall who ++ [sentRecord]) suffix).map
              (fun record => family memory record.1.1 record.1.2 record.2)).prod).toReal) =
      ((((app).privateTranscriptFrom entryPast before).map (fun record =>
        ((app).policyMixture original family).policy record.1.1 record.1.2 record.2)).prod).toReal *
          raw * ((((app).privateTranscriptFrom (control.execution.recall who ++ [sentRecord])
            suffix).map (fun record => ((app).policyMixture original family).policy
              record.1.1 record.1.2 record.2)).prod).toReal := by
  intro sourcePrior original family raw
  let future := fun memory =>
    ((((app).privateTranscriptFrom (control.execution.recall who ++ [sentRecord]) suffix).map
      (fun record => family memory record.1.1 record.1.2 record.2)).prod).toReal
  let indexed := fun memory => ∏ index : Fin suffix.length,
    (family memory (control.execution.recall who ++ sentRecord :: suffix.take index.val)
      suffix[index.val].beforeView suffix[index.val].action).toReal
  have futureEq : future = indexed := by
    funext memory
    have product := (app).privateTranscriptFrom_product (family memory)
      (control.execution.recall who ++ [sentRecord]) suffix
    simpa only [List.append_assoc, List.singleton_append] using product
  have same := phaseTimingPlanPolicy_send_future_posterior_of_history setup mode runtime leaks
    bounds runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed finite
      weights noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded who
        control
        trace active clear event payload binding request unsent final finalTrace finalClear
          sentRecord
          suffix recalled viewed material transmitted candidate named
  have unchanged :
      (((app).policyMixture original family).posterior (entryPast ++ before)).map
          (fun memory => ((((app).privateTranscriptFrom ((entryPast ++ before) ++ [sentRecord])
            suffix).map (fun record =>
              family memory record.1.1 record.1.2 record.2)).prod).toReal) =
        (((app).policyMixture original family).posterior
          ((entryPast ++ before) ++ [sentRecord])).map
          (fun memory => ((((app).privateTranscriptFrom ((entryPast ++ before) ++ [sentRecord])
            suffix).map (fun record => family memory record.1.1 record.1.2
              record.2)).prod).toReal) := by
    have translated : (((app).policyMixture original family).posterior
        (control.execution.recall who)).map future =
          (((app).policyMixture original family).posterior
            (control.execution.recall who ++ [sentRecord])).map future := by
      rw [futureEq]
      exact same.symm
    simpa only [future, callbackRecall] using translated
  have averaged := (app).policyMixture_marked_likelihood_expect original family entryPast before
    sentRecord suffix raw unchanged
  simpa only [← callbackRecall] using averaged

end Vegas
