/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCounterpartAssembly
import Vegas.Game.OnePacketRepairCertificateCounterpart

/-! # Counterpart inputs from actual private-binding repairs

Actual binding repair supplies the certificate reach comparisons. The existing
uniform ratio estimate then assembles counterpart inputs at the canonical
combined-floor tremble scale.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  [Finite setup.intendedProtocol.History]

local instance bindingRepairAssemblyHistoryFintype :
    Fintype ((bounds.onePacketMenu (runtime setup) leaks).protocol
    (initialLaw setup) horizon scheduler).History :=
  (bounds.onePacketMenu (runtime setup) leaks).historyFintype (initialLaw setup) horizon scheduler

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

omit [Finite setup.intendedProtocol.History] in
/-- At every debt-free forced own-turn site, actual repairs give the
certificate's quantitative regular counterpart for every irregular history. -/
theorem exists_counterpart_certificate_of_repairs (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependent) (covered : BindingFieldsCovered bounds)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (small : ∀ n, scale n ≤ 1 / 4) (floor : ℕ → ℝ) (floor_pos : ∀ n, 0 < floor n)
    (floored : ∀ n, floor n ≤ contentFloor setup leaks bounds horizon scheduler (sequence n))
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (error_tendsto : Tendsto (fun n => slotError (scale n) (floor n)
      (trembleSlots setup bounds).card) atTop (nhds 0))
    (n : ℕ) (mixed : (sequence n).IsFullyMixed)
    {who : Player} {site : (onePacketN).InformationSite who}
    (forced : ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
    (notOwing : ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (history : (onePacketN).InformationHistory who site.1) :
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
            scale_le_one weights n) counterpart.1).toReal) := by
  classical
  by_cases regular : RegularTrace setup leaks bounds horizon scheduler (sequence n) who
    history.1.trace
  · exact ⟨history, fun irregular => (irregular regular).elim⟩
  obtain ⟨witness, witnessControl, w, witnessState, decodedW, freeW⟩ :=
    exists_debtFree_witness forced notOwing
  let toDecision : (onePacketN).InformationHistory who site.1 →
      (onePacketN).InformationHistory who (some (past, view)) :=
    fun found => ⟨found.1, found.2.trans atSite⟩
  obtain ⟨current, p, historyState, decodedP⟩ := decoded_of_decision (toDecision history)
  obtain ⟨counterpart, counterpartRegular, dominated⟩ := reach_le_counterpart_certificate_of_repairs
    wellFormed independent covered sequence scale scale_pos scale_le_one small floor floor_pos
    floored covers capacity weights error_tendsto n mixed atSite
    (forcedAgent_of_not_free setup leaks bounds horizon scheduler forced) turn
    (toDecision history)
    (toDecision witness) historyState witnessState decodedP decodedW freeW
    regular
  exact ⟨⟨counterpart.1, counterpart.2.trans atSite.symm⟩, fun _ =>
    ⟨counterpartRegular, dominated⟩⟩

/-- Actual private-binding repairs assemble counterpart inputs with no
successful-cell or external counterpart-construction premise. -/
def OnePacketCounterpartInputs.ofBindingRepairs (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependent)
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    (mixedSource : ∀ n, (sequence n).IsFullyMixed)
    {scale : ℕ → ℝ} (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup leaks bounds horizon scheduler (sequence n)) (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    {who : Player} {site : (onePacketN).InformationSite who}
    (forced : ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
    (notOwing : ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event) :
    OnePacketCounterpartInputs setup leaks bounds horizon scheduler sequence targetSequence
      site := by
  classical
  let floor := fun n => combinedFloor setup leaks bounds horizon scheduler (sequence n)
  have floor_pos : ∀ n, 0 < floor n := fun n => combinedFloor_pos setup leaks bounds horizon
    scheduler (sequence n)
  have floor_le_one : ∀ n, floor n ≤ 1 := fun n => combinedFloor_le_one setup leaks bounds horizon
    scheduler (sequence n)
  have floored : ∀ n, floor n ≤ contentFloor setup leaks bounds horizon scheduler (sequence n) :=
    fun n => combinedFloor_le_contentFloor setup leaks bounds horizon scheduler (sequence n)
  have small : ∀ n, scale n ≤ 1 / 4 := fun n => by
    rw [scaleEq n]
    exact trembleScale_le_quarter (floor_pos n).le (floor_le_one n)
  have error_tendsto : Tendsto (fun n => slotError (scale n) (floor n)
      (trembleSlots setup bounds).card) atTop (nhds 0) := by
    have tendsto := tendsto_slotError floor floor_pos floor_le_one (2 * horizon + 2)
      (trembleSlots setup bounds).card
    convert tendsto using 1
    funext n
    rw [scaleEq n]
  have covered : BindingFieldsCovered bounds := bindingFieldsCovered_of_covers covers coversInputs
  exact OnePacketCounterpartInputs.ofReachComparisons scale_pos scale_le_one scaleEq
    weights assembled mixed (fun n history => exists_counterpart_certificate_of_repairs
      wellFormed independent covered
      sequence scale scale_pos scale_le_one small floor floor_pos floored covers
      capacity weights error_tendsto n (mixedSource n) forced notOwing atSite turn history)


end Vegas
