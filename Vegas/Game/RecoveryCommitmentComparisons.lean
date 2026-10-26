/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryIntendedCommitmentValue
import Vegas.Game.OnePacketCommitmentSourcePolicy
import Vegas.Game.OnePacketValueTransport

/-! # A single source deviation for all histories of a nonlate commitment -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon (NativeScheduler)
local notation "Menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

open Classical in
/-- One original source commitment compares with the native pure commitment
at every regular history of the same complete nonlate input. -/
theorem nativeComparison_intendedCommitment_history_comparisons_of_counted_service [Fintype
  (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p)) (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).Trace (some control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      OpportunityAt (runtime setup) leaks control.execution delay)
    (inclusion : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).Trace (some control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      ProtectedInclusionAt (runtime setup) leaks control.execution bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).Trace (some control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      (application setup leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    {who : Player} (site : (N).InformationSite who) (choice : (N).Choice who site.1)
    (notFree : ¬ Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site))
    (notOwing : ¬ Vegas.OwingAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site))
    (nonlate : ¬ LateDelivery setup leaks who site.1)
    (atTurn : CommitsAtTurn setup leaks bounds horizon (NativeScheduler) who site choice)
    (intendedChoice : IntendedCommitment setup leaks bounds horizon (NativeScheduler) site choice)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (upper : ℝ) (le_upper : ∀ outcome, utility outcome who ≤ upper)
    {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let common := nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale
      positive le_one weights n
    let certificate := ((Menu).bounded (initialLaw setup) horizon
      (NativeScheduler)).wellFoundedHistories
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup parameter utility excludedPayoff leaks final.state who
    ∃ sourceChoice : setup.intendedModel.Choice who (projectView setup leaks who site.1),
      ∀ history : (N).InformationHistory who site.1,
      RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) who history.1.trace →
      expect ((N).runBehavioralUntil certificate
          (Profile.update (sig := (N).behavioralSignature) common who
            ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
        expect ((N).runBehavioralUntil certificate common stopped history.1) payoff ≤
        setup.intendedModel.historyGain
          (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
          (intendedReadoutExclusion setup parameter utility excludedPayoff) (payoffComponent setup)
          (sequence n) (projectedSite setup leaks decision,
            ((sequence n).strategy who).commit (projectView setup leaks who site.1) sourceChoice)
          (replayProjection setup leaks bounds horizon (NativeScheduler)
            (projectedSite setup leaks decision) site atSite rfl history) +
        2 * ((2 * payoffBound * (1 - slotRetention (scale n))) *
          (2 * horizon + 1)) + 2 * payoffBound * (1 - slotRetention (scale n)) := by
  intro common certificate stopped payoff
  obtain ⟨sourceChoice, event, payload, outputEq, value, sourceAction,
    ⟨response, material, serial, selected, sends, packet, after, turn⟩, _sourceGain⟩ :=
    intendedCommitment_sourcePolicy_gain setup leaks bounds horizon (NativeScheduler) wellFormed
      (sequence n) parameter utility excludedPayoff site choice atTurn intendedChoice decision
      atSite readoutBounded
  refine ⟨sourceChoice, ?_⟩
  intro history regular
  have forced := forcedAgent_of_not_free setup leaks bounds horizon (NativeScheduler) notFree
  have debtFree := siteDebtFree_of_not_owing setup leaks bounds horizon (NativeScheduler) notOwing
  have ownIntended := ownCompletionsIntended_of_siteNotOwes wellFormed debtFree history
  have allDebtFree := not_owesFailure_of_regular wellFormed (sequence n) atSite forced history
    regular ownIntended
  have stateForced := forcedState_of_regular wellFormed (sequence n) atSite forced history regular
    ownIntended
  have submitted : (runtime setup).submittedEvent? leaks response = some event := by
    unfold EventGraphRuntime.submittedEvent?
    simp only [sends, packet, Payload.event?]
  have pending := pendingEvent_of_turnSubmission setup leaks bounds horizon (NativeScheduler) site
    atSite turn choice selected submitted
  obtain ⟨remaining, execution, point, current, actualAt, never, ordered, decoded, intended,
    _reached⟩ := firstActivation_history_facts setup leaks bounds horizon (NativeScheduler)
      wellFormed site pending nonlate history stateForced allDebtFree
  have member : response ∈ bounds.onePacketActions (runtime setup) leaks who past view := by
    obtain ⟨other, otherChosen, offered⟩ := choice_response setup leaks bounds horizon
      (NativeScheduler) site atSite choice
    have same := Option.some.inj (selected.symm.trans otherChosen)
    subst other
    exact offered
  obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj (Option.some.inj (atSite.symm.trans actualAt))
  subst past view
  obtain ⟨_owner, _slot, foundPayload, foundOutput, codeEq, _rest⟩ :=
    onePacket_commitment_facts bounds member sends packet
  have payloadEq : foundPayload = payload := by
    exact (EventGraph.EventField.binding.inj (foundOutput.symm.trans outputEq)).2
  subst foundPayload
  have code : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload := by
    exact codeEq
  let key := LateKey.ofView setup leaks who (execution.recall who)
    (execution.observe (application setup leaks) who)
  have pendingHere := pending
  rw [actualAt] at pendingHere
  have decided := decidedEvent_eq_of_pending setup leaks horizon (NativeScheduler) pendingHere
    ((Menu).toRawTrace (initialLaw setup) horizon (NativeScheduler) (current ▸ history.1.trace)) rfl
    (lateKey_some who (execution.recall who)
      (execution.observe (application setup leaks) who))
  obtain ⟨replay, replayed⟩ := intendedHistory?_isSome_of_debtFree wellFormed history.1.trace
    _ current (by
      intro found foundDecoded
      exact allDebtFree found (by rw [current]; exact foundDecoded))
  have projection := replayProjection_eq (setup := setup) (leaks := leaks) (bounds := bounds)
    (horizon := horizon) (scheduler := NativeScheduler)
    (sourceSite := projectedSite setup leaks decision) actualAt rfl history replayed
  have replayState := intendedHistory?_state history.1.trace replayed
  rw [current] at replayState
  have sourceState : (replayProjection setup leaks bounds horizon (NativeScheduler)
      (projectedSite setup leaks decision) site actualAt rfl history).1.state = some point := by
    rw [projection, replayState]
    exact (decodedPoint_eq_of_isPrefix ordered).trans decoded
  exact nativeComparison_firstActivation_commitment_gain_le_of_counted_service setup leaks bounds
    horizon scheduler
    wellFormed covers capacity sequence scale positive le_one weights n opportunity inclusion timely
    completes site choice response selected history current actualAt member material sends event
    packet pending never key decided outputEq code after ordered decoded intended
    (projectedSite setup leaks decision) sourceChoice sourceAction _ sourceState parameter utility
    excludedPayoff below upper le_upper boundNonneg readoutBounded excludedBounded

open Classical in
theorem nativeComparison_intendedCommitment_history_comparisons [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p)) (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    {who : Player} (site : (N).InformationSite who) (choice : (N).Choice who site.1)
    (notFree : ¬ Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site))
    (notOwing : ¬ Vegas.OwingAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site))
    (nonlate : ¬ LateDelivery setup leaks who site.1)
    (atTurn : CommitsAtTurn setup leaks bounds horizon (NativeScheduler) who site choice)
    (intendedChoice : IntendedCommitment setup leaks bounds horizon (NativeScheduler) site choice)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (upper : ℝ) (le_upper : ∀ outcome, utility outcome who ≤ upper)
    {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let common := nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale
      positive le_one weights n
    let certificate := ((Menu).bounded (initialLaw setup) horizon
      (NativeScheduler)).wellFoundedHistories
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup parameter utility excludedPayoff leaks final.state who
    ∃ sourceChoice : setup.intendedModel.Choice who (projectView setup leaks who site.1),
      ∀ history : (N).InformationHistory who site.1,
      RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) who history.1.trace →
      expect ((N).runBehavioralUntil certificate
          (Profile.update (sig := (N).behavioralSignature) common who
            ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
        expect ((N).runBehavioralUntil certificate common stopped history.1) payoff ≤
        setup.intendedModel.historyGain
          (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
          (intendedReadoutExclusion setup parameter utility excludedPayoff) (payoffComponent setup)
          (sequence n) (projectedSite setup leaks decision,
            ((sequence n).strategy who).commit (projectView setup leaks who site.1) sourceChoice)
          (replayProjection setup leaks bounds horizon (NativeScheduler)
            (projectedSite setup leaks decision) site atSite rfl history) +
        2 * ((2 * payoffBound * (1 - slotRetention (scale n))) *
          (2 * horizon + 1)) + 2 * payoffBound * (1 - slotRetention (scale n)) := by
  exact nativeComparison_intendedCommitment_history_comparisons_of_counted_service setup leaks
    bounds horizon scheduler wellFormed covers capacity sequence scale positive le_one weights
    n (Recovery.Opportunity.clear_counted_native bounds (initialLaw_initialized setup)
      (initialLaw_native setup) opportunity)
    (Recovery.ProtectedInclusion.clear_counted_native bounds (initialLaw_initialized setup)
      (initialLaw_native setup) inclusion) timely
    (Recovery.CompletesPlay.clear_counted_native bounds (initialLaw_initialized setup)
      (initialLaw_native setup) completes) site choice notFree notOwing nonlate atTurn
    intendedChoice atSite decision parameter utility excludedPayoff below upper le_upper
    boundNonneg readoutBounded excludedBounded

end Vegas.RecoveryOnePacket
