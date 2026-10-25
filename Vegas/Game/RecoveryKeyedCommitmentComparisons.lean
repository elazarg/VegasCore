/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryCommittedValueAffine
import Vegas.Game.RecoveryKeyedValueBounds
import Vegas.Game.RecoverySourceBeliefBounds
import Vegas.Game.OnePacketCommitmentSourcePolicy

/-! # Uniform source incentive bounds for keyed commitments -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

variable {Public : Type*} {signal : State L setup.context → Public}

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

private theorem affine_commitment_gain_le {chosen option excluded committed baseline gain
    failure otherFailure chosenError optionError failureError transportError bound : ℝ}
    (chosenNear : |chosen - (excluded + (1 - failure) * (committed - excluded))| ≤ chosenError)
    (optionNear : |option - (excluded + (1 - otherFailure) * (baseline - excluded))| ≤ optionError)
    (failureNear : |failure - otherFailure| ≤ failureError)
    (transportNear : |committed - baseline - gain| ≤ transportError)
    (baselineBounded : |baseline - excluded| ≤ bound)
    (failureNonneg : 0 ≤ failure) (failureLe : failure ≤ 1) :
    chosen - option ≤ (1 - failure) * gain +
      (chosenError + optionError + bound * failureError + transportError) := by
  have failureProduct : |(otherFailure - failure) * (baseline - excluded)| ≤
      bound * failureError := by
    rw [abs_mul, abs_sub_comm]
    exact (mul_le_mul failureNear baselineBounded (abs_nonneg _)
      ((abs_nonneg _).trans failureNear)).trans (le_of_eq (mul_comm _ _))
  have transportNonneg := (abs_nonneg _).trans transportNear
  have transportProduct : (1 - failure) * (committed - baseline - gain) ≤ transportError := by
    have scaled := mul_le_mul_of_nonneg_left (abs_le.mp transportNear).2
      (sub_nonneg.mpr failureLe)
    nlinarith
  have algebra : chosen - option - (1 - failure) * gain =
      (chosen - (excluded + (1 - failure) * (committed - excluded))) +
      ((excluded + (1 - otherFailure) * (baseline - excluded)) - option) +
      (otherFailure - failure) * (baseline - excluded) +
      (1 - failure) * (committed - baseline - gain) := by ring
  have first := (abs_le.mp chosenNear).2
  have second := (abs_le.mp optionNear).1
  have third := (abs_le.mp failureProduct).2
  linarith

open Classical in
/-- Every intended keyed commitment compares with its same-slot option and a
success-weighted deviation in the original source assessment. -/
theorem nativeComparison_keyed_commitment_comparisons [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [Finite setup.intendedProtocol.History]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (slots_pos : 0 < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup leaks bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds Initial horizon scheduler bounds.candidateCount p))
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (N).InformationSite who) (choice : (N).Choice who site.1),
        ¬ Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
        ¬ Vegas.OwingAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
        ownedKeyed (Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler))
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon (NativeScheduler))
          ((N).agentAt site) →
        CommitsAtTurn setup leaks bounds horizon (NativeScheduler) who site choice →
        IntendedCommitment setup leaks bounds horizon (NativeScheduler) site choice →
        ∃ (option : LateOption bounds.candidateCount)
          (sourceDeviation : setup.intendedModel.AssessmentDeviation who) (success : ℝ),
          0 ≤ success ∧ success ≤ 1 ∧
          let common := nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale
            positive le_one weights n
          let certificate := ((Menu).bounded (initialLaw setup) horizon
            (NativeScheduler)).wellFoundedHistories
          let stopped := fun final : (NP).History => ¬ Clear final.state ∨
            DecodedState setup leaks (failureProfile setup.program)
              (ProtocolState.OwesFailure who setup.program) final.state
          let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
            exclusionBase setup parameter utility excludedPayoff leaks final.state who
          expect ((nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
            positive le_one weights n).belief who site) (fun history =>
              expect ((N).runBehavioralUntil certificate
                (Profile.update (sig := (N).behavioralSignature) common who
                  ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
              expect ((N).runBehavioralUntil certificate
                (Profile.update (sig := (N).behavioralSignature) common who
                  ((common who).withLaw site.1 (onePacketLate setup leaks bounds horizon
                    (NativeScheduler) sequence scale positive le_one n ((N).agentAt site) option)))
                stopped history.1) payoff) ≤
            success * intendedSiteGain setup parameter utility excludedPayoff (sequence n)
              sourceDeviation + error n := by
  let inputs := nativeBaseInputs setup leaks bounds horizon scheduler wellFormed independent
    observable
    sequence sourceMixed covers coversInputs capacity slots_pos
  have sameScale : scale = inputs.scale := funext scaleEq
  subst scale
  let target := nativeComparisonSequence setup leaks bounds horizon scheduler sequence inputs.scale
    positive le_one weights
  have assembled := nativeComparisonSequence_assembled setup leaks bounds horizon scheduler sequence
    inputs.scale positive le_one weights
  have mixed := nativeComparisonSequence_fullyMixed setup leaks bounds horizon scheduler sequence
    inputs.scale positive le_one weights
  have bayes := nativeComparisonSequence_bayes setup leaks bounds horizon scheduler sequence
    inputs.scale positive le_one weights
  obtain ⟨unforced, unforcedLimit, unforcedBound⟩ := inputs.lateUnforced setup leaks bounds horizon
    (NativeScheduler) wellFormed
    (fun n => nativeComparisonWeights setup leaks bounds horizon scheduler (weights n))
    target assembled mixed bayes
  obtain ⟨gamma, gammaLimit, decorrelated⟩ := inputs.lateDecorrelated setup leaks bounds horizon
    (NativeScheduler) wellFormed sourceMixed
    (fun n => nativeComparisonWeights setup leaks bounds horizon scheduler (weights n))
    target assembled mixed bayes
  obtain ⟨distance, distanceLimit, posterior⟩ := nativeComparison_source_belief_bounds setup leaks
    bounds horizon scheduler wellFormed independent observable sequence sourceMixed sourceBayes
    inputs.scale
    positive le_one (fun _ => rfl) covers coversInputs capacity weights
  let depth : ℝ := 2 * horizon + 1
  let path := fun n => depth * (inputs.scale n ^ 3 + inputs.scale n ^ 3)
  let retention := fun n =>
    (2 * payoffBound * (Fintype.card Player * (1 - slotRetention (inputs.scale n)))) * depth
  let optionError := fun n => retention n +
    (2 * (inputs.scale n ^ 3 + path n) * depth + inputs.scale n ^ 3 * depth) * (2 * payoffBound) +
      2 * payoffBound * (inputs.scale n ^ 3 * depth)
  let choiceError := fun n => retention n + 2 * payoffBound * |unforced n| +
    4 * payoffBound * (path n + |unforced n|) + 4 * payoffBound * |gamma n|
  let referenceError := fun n => optionError n + 2 * payoffBound * |unforced n| +
    4 * payoffBound * (path n + |unforced n|) + 4 * payoffBound * |gamma n|
  let failureError := fun n => 2 * path n + |unforced n| + 3 * inputs.scale n
  let transportError := fun n => 2 * payoffBound * |distance n| +
    4 * payoffBound * |unforced n|
  let error := fun n => choiceError n + referenceError n +
    2 * payoffBound * failureError n + transportError n
  have cube := inputs.scale_vanishing.pow 3
  have retained := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_slotRetention inputs.scale_vanishing)
  have pathLimit : Tendsto path atTop (nhds 0) := by
    simpa [path] using (cube.add cube).const_mul depth
  have retentionLimit : Tendsto retention atTop (nhds 0) := by
    simpa [retention, mul_assoc] using
      ((retained.const_mul (2 * payoffBound * Fintype.card Player)).mul_const depth)
  have optionLimit : Tendsto optionError atTop (nhds 0) := by
    have second := ((((cube.add pathLimit).const_mul 2).mul_const depth).add
      (cube.mul_const depth)).mul_const (2 * payoffBound)
    have third := (cube.mul_const depth).const_mul (2 * payoffBound)
    simpa [optionError] using (retentionLimit.add second).add third
  have commonLimit := ((unforcedLimit.abs.const_mul (2 * payoffBound)).add
    ((pathLimit.add unforcedLimit.abs).const_mul (4 * payoffBound))).add
      (gammaLimit.abs.const_mul (4 * payoffBound))
  have choiceLimit : Tendsto choiceError atTop (nhds 0) := by
    simpa [choiceError, add_assoc] using retentionLimit.add commonLimit
  have referenceLimit : Tendsto referenceError atTop (nhds 0) := by
    simpa [referenceError, add_assoc] using optionLimit.add commonLimit
  have failureLimit : Tendsto failureError atTop (nhds 0) := by
    simpa [failureError] using ((pathLimit.const_mul 2).add unforcedLimit.abs).add
      (inputs.scale_vanishing.const_mul 3)
  have transportLimit : Tendsto transportError atTop (nhds 0) := by
    simpa [transportError] using (distanceLimit.abs.const_mul (2 * payoffBound)).add
      (unforcedLimit.abs.const_mul (4 * payoffBound))
  refine ⟨error, ?_, ?_⟩
  · simpa [error] using ((choiceLimit.add referenceLimit).add
      (failureLimit.const_mul (2 * payoffBound))).add transportLimit
  intro n who site choice notFree notOwing keyed atTurn intendedChoice
  obtain ⟨past, view, turnResponse, turnEvent, atSite, turnSelected, turnSubmitted, turn⟩ := atTurn
  have forced := forcedAgent_of_not_free setup leaks bounds horizon (NativeScheduler) notFree
  have debtFree := siteDebtFree_of_not_owing setup leaks bounds horizon (NativeScheduler) notOwing
  have decision := projectedDecision_of_forcedAgent wellFormed forced atSite turn debtFree
  obtain ⟨sourceChoice, event, payload, outputEq, value, sourceAction,
    ⟨response, material, serial, selected, sends, packet, after, ownTurn⟩, _sourceGain⟩ :=
    intendedCommitment_sourcePolicy_gain setup leaks bounds horizon (NativeScheduler) wellFormed
      (sequence n) parameter utility excludedPayoff site choice
      ⟨past, view, turnResponse, turnEvent, atSite, turnSelected, turnSubmitted, turn⟩
      intendedChoice decision atSite (readoutBounded who)
  have member : response ∈ bounds.onePacketActions (runtime setup) leaks who past view := by
    obtain ⟨other, chosen, offered⟩ := choice_response setup leaks bounds horizon
      (NativeScheduler) site atSite choice
    cases Option.some.inj (selected.symm.trans chosen)
    exact offered
  have submitted : (runtime setup).submittedEvent? leaks response = some event := by
    unfold EventGraphRuntime.submittedEvent?
    simp only [sends, packet, Payload.event?]
  have pending := pendingEvent_of_turnSubmission setup leaks bounds horizon (NativeScheduler) site
    atSite ownTurn choice selected submitted
  have sourceOffered : sourceOfValue setup event outputEq value ∈
      setup.intendedMenu who (projectView setup leaks who site.1) := sourceAction ▸ sourceChoice.2
  obtain ⟨_owner, _slot, foundPayload, foundOutput, codeEq, _rest⟩ :=
    onePacket_commitment_facts bounds member sends packet
  have payloadEq : foundPayload = payload :=
    (EventGraph.EventField.binding.inj (foundOutput.symm.trans outputEq)).2
  subst foundPayload
  have code : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload := codeEq
  have node := nodeView_eq_bind outputEq code
  let key := LateKey.ofView setup leaks who past view
  have siteKey : lateKey setup leaks who site.1 = some key := by rw [atSite]; rfl
  have inRange := onePacket_commitment_serial_lt setup leaks bounds member sends packet
  let option : LateOption bounds.candidateCount := some ⟨serial, inRange⟩
  let reference := onePacketLate setup leaks bounds horizon (NativeScheduler) sequence inputs.scale
    positive le_one n ((N).agentAt site) option
  let failed : Set (NP).History := {final | DecisionFailed key final.state}
  let failure := localFailure (2 * horizon + 1) (target n) site failed (PMF.pure choice)
  let otherFailure := localFailure (2 * horizon + 1) (target n) site failed reference
  let deviation : setup.intendedModel.AssessmentDeviation who :=
    (projectedSite setup leaks decision,
      ((sequence n).strategy who).commit (projectView setup leaks who site.1) sourceChoice)
  have unit : 0 ≤ failure ∧ failure ≤ 1 :=
    ⟨localFailure_nonneg _ _ _ _ _, localFailure_le_one _ _ _ _ _⟩
  refine ⟨option, deviation, 1 - failure, by linarith [unit.2], by linarith [unit.1], ?_⟩
  intro common certificate stopped payoff
  have strategyEq : (target n).strategy = common := rfl
  have unforcedMass := (unforcedBound n who site notFree notOwing keyed).trans (le_abs_self _)
  have decorrelation := (decorrelated n who site notFree notOwing keyed).mono (le_abs_self _)
  have chosenNear := nativeComparison_committed_value_sub_le setup leaks bounds horizon scheduler
    wellFormed covers capacity sequence inputs.scale positive le_one weights n opportunity inclusion
    timely completes site keyed.1 debtFree siteKey pending atSite unforcedMass decorrelation choice
    response selected sends packet node after sourceOffered parameter utility excludedPayoff
    boundNonneg (readoutBounded who) (excludedBounded who)
  have optionNear := nativeComparison_keyed_value_sub_le setup leaks bounds horizon scheduler
    wellFormed covers capacity sequence inputs.scale positive le_one weights n opportunity inclusion
    timely completes site keyed.1 debtFree siteKey pending atSite unforcedMass decorrelation option
    parameter utility excludedPayoff boundNonneg (readoutBounded who) (excludedBounded who)
  dsimp only at chosenNear optionNear
  rw [strategyEq] at chosenNear optionNear
  have failNear := certificate_lateCommit_siteDecisionFailure setup leaks bounds horizon
    (NativeScheduler) sequence inputs.scale positive le_one
    (fun n => nativeComparisonWeights setup leaks bounds horizon scheduler (weights n)) target
    assembled n covers (Nat.succ_le_of_lt slots_pos) (le_refl _) site keyed.1 debtFree siteKey
    pending node atSite unforcedMass choice response selected sends packet after inRange
  have transported := abs_siteCommitValue_sub_le setup leaks bounds horizon (NativeScheduler)
    parameter utility excludedPayoff wellFormed (target n) (sequence n) site atSite ownTurn decision
    sourceChoice debtFree (readoutBounded who) (excludedBounded who)
  have distanceBound := (posterior n who site notFree notOwing atSite ownTurn decision).trans
    (le_abs_self _)
  have transportBound : |siteCommitValue setup leaks bounds horizon (NativeScheduler) parameter
      utility excludedPayoff (target n) (setup.intendedOpeningProfile (sequence n).strategy) site
        sourceChoice.1 -
      siteValue setup leaks bounds horizon (NativeScheduler) parameter utility excludedPayoff
        (target n) (setup.intendedOpeningProfile (sequence n).strategy) site -
      intendedSiteGain setup parameter utility excludedPayoff (sequence n) deviation| ≤
        transportError n := by
    exact transported.trans (add_le_add
      (mul_le_mul_of_nonneg_left distanceBound (by positivity))
      (mul_le_mul_of_nonneg_left unforcedMass (by positivity)))
  have baselineBounded : |siteValue setup leaks bounds horizon (NativeScheduler) parameter utility
      excludedPayoff (target n) (setup.intendedOpeningProfile (sequence n).strategy) site -
        excludedPayoff who| ≤ 2 * payoffBound := by
    have sourceBound : |siteValue setup leaks bounds horizon (NativeScheduler) parameter utility
        excludedPayoff (target n) (setup.intendedOpeningProfile (sequence n).strategy) site| ≤
          payoffBound := expect_abs_le_of_bounded boundNonneg (fun history =>
      abs_decodedPointValue_le setup leaks bounds horizon (NativeScheduler) parameter utility
        excludedPayoff _ who _ history.1 (readoutBounded who) (excludedBounded who))
    exact (abs_sub _ _).trans (by linarith [excludedBounded who])
  have choiceBound : |expect ((target n).belief who site) (fun history =>
      expect ((N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature) common who
          ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff) -
      (excludedPayoff who + (1 - failure) *
        (siteCommitValue setup leaks bounds horizon (NativeScheduler) parameter utility
          excludedPayoff (target n) (setup.intendedOpeningProfile (sequence n).strategy) site
            sourceChoice.1 - excludedPayoff who))| ≤ choiceError n := by
    rw [sourceAction]
    simpa only [target, common, certificate, stopped, payoff, failure, failed,
      choiceError, retention, path, depth, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one, Nat.cast_ofNat] using chosenNear
  have referenceBound : |expect ((target n).belief who site) (fun history =>
      expect ((N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature) common who
          ((common who).withLaw site.1 reference)) stopped history.1) payoff) -
      (excludedPayoff who + (1 - otherFailure) *
        (siteValue setup leaks bounds horizon (NativeScheduler) parameter utility excludedPayoff
          (target n) (setup.intendedOpeningProfile (sequence n).strategy) site -
            excludedPayoff who))| ≤ referenceError n := by
    simpa only [target, common, certificate, stopped, payoff, reference, otherFailure, failed,
      referenceError, optionError, retention, path, depth, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one, Nat.cast_ofNat] using optionNear
  have failureBound : |failure - otherFailure| ≤ failureError n := by
    simpa only [failureError, path, depth, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat] using failNear
  rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
  exact affine_commitment_gain_le choiceBound referenceBound failureBound transportBound
    baselineBounded unit.1 unit.2

end Vegas.RecoveryOnePacket
