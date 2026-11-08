/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketKeyedValueBounds
import Vegas.Game.OnePacketCommittedValueAffine
import Vegas.Game.OnePacketLateCommitFailure
import Vegas.Game.OnePacketLateCommitments
import Vegas.Game.OnePacketSourceBeliefBounds
import Vegas.Game.OnePacketCommitmentSourcePolicy

/-! # Intended keyed commitments on the actual native assessment sequence -/

noncomputable section

namespace Vegas.OnePacketComparison

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)
  {Public : Type*} {signal : State L setup.context → Public}

local notation "N" => onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
  scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu timeouts leaks) (initialLaw setup) horizon scheduler
local notation "Menu" => bounds.onePacketMenu timeouts leaks
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup timeouts leaks)
    (fun native : EventGraphRuntime.State (graph setup) =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config native) = ∅)

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
theorem assembled_keyed_commitment_comparisons
    [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
    [Finite setup.intendedProtocol.History]
    [∀ who, DecidableEq ((N).InfoState who)]
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
      (combinedFloor setup timeouts leaks bounds horizon scheduler (sequence n))
      (2 * horizon + 2) n)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler bounds.candidateCount p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence scale
      positive le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (N) (targetSequence n)
      ((Menu).decisionRecall (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup timeouts leaks).Control,
      (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some
        control) →
      control.execution.application.config.defaulted = ∅ →
      OpportunityAt timeouts leaks control.execution delay)
    (inclusion : ∀ control : (application setup timeouts leaks).Control,
      (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some
        control) →
      control.execution.application.config.defaulted = ∅ →
      ProtectedInclusionAt timeouts leaks control.execution bound)
    (timely : (AsyncTimely timeouts) delay bound)
    (completes : ∀ control : (application setup timeouts leaks).Control,
      (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some
        control) →
      control.execution.application.config.defaulted = ∅ →
      (application setup timeouts leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (N).InformationSite who) (choice : (N).Choice who site.1),
        ¬ Vegas.FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
        ((N).agentAt site) →
        ¬ Vegas.OwingAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
        ((N).agentAt site) →
        ownedKeyed (Vegas.FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon
          scheduler)
          (LateDeliveryAgent setup timeouts leaks bounds (initialLaw setup) horizon
            scheduler)
          ((N).agentAt site) →
        CommitsAtTurn setup timeouts leaks bounds horizon scheduler who site choice →
        IntendedCommitment setup timeouts leaks bounds horizon scheduler site choice →
        ∃ (option : LateOption bounds.candidateCount)
          (sourceDeviation : setup.intendedModel.AssessmentDeviation who) (success : ℝ),
          0 ≤ success ∧ success ≤ 1 ∧
          let common := (targetSequence n).strategy
          let certificate := ((Menu).bounded (initialLaw setup) horizon
            scheduler).wellFoundedHistories
          let stopped := fun final : (NP).History => ¬ Clear final.state ∨
            DecodedState setup timeouts leaks (failureProfile setup.program)
              (ProtocolState.OwesFailure who setup.program) final.state
          let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
            exclusionBase setup timeouts parameter utility excludedPayoff leaks final.state who
          expect ((targetSequence n).belief who site) (fun history =>
              expect ((N).runBehavioralUntil certificate
                (Profile.update (sig := (N).behavioralSignature) common who
                  ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
              expect ((N).runBehavioralUntil certificate
                (Profile.update (sig := (N).behavioralSignature) common who
                  ((common who).withLaw site.1 (onePacketLate setup timeouts leaks bounds horizon
                    scheduler sequence scale positive le_one n ((N).agentAt site) option)))
                stopped history.1) payoff) ≤
            success * intendedSiteGain setup parameter utility excludedPayoff (sequence n)
              sourceDeviation + error n := by
  let inputs := OnePacketBaseInputs.ofSetup setup timeouts leaks bounds horizon scheduler
        wellFormed independent
    observable
    sequence sourceMixed covers coversInputs capacity slots_pos
  have sameScale : scale = inputs.scale := funext scaleEq
  subst scale
  let target := targetSequence
  obtain ⟨unforced, unforcedLimit, unforcedBound⟩ := inputs.lateUnforced setup timeouts leaks
    bounds horizon
    scheduler wellFormed
    weights
    target assembled mixed bayes
  obtain ⟨gamma, gammaLimit, decorrelated⟩ := inputs.lateDecorrelated setup timeouts leaks bounds
    horizon
    scheduler wellFormed sourceMixed
    weights
    target assembled mixed bayes
  obtain ⟨distance, distanceLimit, posterior⟩ := source_belief_bounds_of_assembled setup
    timeouts leaks
    bounds horizon scheduler wellFormed independent observable sequence sourceMixed sourceBayes
    inputs.scale
    positive le_one (fun _ => rfl) covers coversInputs capacity weights target
    assembled mixed bayes
  let depth : ℝ := 2 * horizon + 1
  let path := fun n => depth * (inputs.scale n ^ 3 + inputs.scale n ^ 3)
  let retention := fun n =>
    (2 * payoffBound * (1 - slotRetention (inputs.scale n))) * depth
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
      ((retained.const_mul (2 * payoffBound)).mul_const depth)
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
  have forced := forcedAgent_of_not_free setup timeouts leaks bounds (initialLaw setup) horizon
        scheduler
    notFree
  have debtFree := siteDebtFree_of_not_owing setup timeouts leaks bounds horizon scheduler
    notOwing
  have decision := projectedDecision_of_forcedAgent (timeouts := timeouts) wellFormed forced atSite
    turn debtFree
  obtain ⟨sourceChoice, event, payload, outputEq, value, sourceAction,
    ⟨response, material, serial, selected, sends, packet, after, ownTurn⟩, _sourceGain⟩ :=
    intendedCommitment_sourcePolicy_gain setup timeouts leaks bounds horizon scheduler
      wellFormed
      (sequence n) parameter utility excludedPayoff site choice
      ⟨past, view, turnResponse, turnEvent, atSite, turnSelected, turnSubmitted, turn⟩
      intendedChoice decision atSite (readoutBounded who)
  have member : response ∈ bounds.onePacketActions timeouts leaks who past view := by
    obtain ⟨other, chosen, offered⟩ := choice_response setup timeouts leaks bounds horizon
      scheduler site atSite choice
    cases Option.some.inj (selected.symm.trans chosen)
    exact offered
  have submitted : (submittedEvent? timeouts) leaks response = some event := by
    unfold EventGraphRuntime.submittedEvent?
    simp only [sends, packet, Payload.event?]
  have pending : pendingEvent setup timeouts leaks who site.1 = some event := by
    by_cases unrecorded : (eventRecorded timeouts) leaks past event = false
    · rw [atSite]
      exact pendingEvent_of_spec (timeouts := timeouts) ownTurn unrecorded
    · have recorded := Bool.eq_true_of_not_eq_false unrecorded
      have unpending : pendingEvent setup timeouts leaks who site.1 = none := by
        rw [atSite]
        simp [pendingEvent, ownTurn, recorded]
      have quiet := choice_eq_silence_of_unpending_notOwing (timeouts := timeouts) wellFormed
        site notOwing atSite unpending choice
      rw [selected, Option.some.injEq] at quiet
      rw [quiet] at sends
      cases sends
  have sourceOffered : sourceOfValue setup event outputEq value ∈
      setup.intendedMenu who (projectView setup timeouts leaks who site.1) := sourceAction ▸
        sourceChoice.2
  obtain ⟨_owner, _slot, foundPayload, foundOutput, codeEq, _rest⟩ :=
    onePacket_commitment_facts (timeouts := timeouts) bounds member sends packet
  have payloadEq : foundPayload = payload :=
    (EventGraph.EventField.binding.inj (foundOutput.symm.trans outputEq)).2
  subst foundPayload
  have code : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload := codeEq
  have node := nodeView_eq_bind outputEq code
  let key := LateKey.ofView setup timeouts leaks who past view
  have siteKey : lateKey setup timeouts leaks who site.1 = some key := by rw [atSite]; rfl
  have inRange := onePacket_commitment_serial_lt setup timeouts leaks bounds member sends packet
  let option : LateOption bounds.candidateCount := some ⟨serial, inRange⟩
  let reference := onePacketLate setup timeouts leaks bounds horizon scheduler sequence
    inputs.scale
    positive le_one n ((N).agentAt site) option
  let failed : Set (NP).History := {final | DecisionFailed (timeouts := timeouts) key final.state}
  let failure := localFailure (2 * horizon + 1) (target n) site failed (PMF.pure choice)
  let otherFailure := localFailure (2 * horizon + 1) (target n) site failed reference
  let deviation : setup.intendedModel.AssessmentDeviation who :=
    (projectedSite setup timeouts leaks decision,
      ((sequence n).strategy who).commit (projectView setup timeouts leaks who site.1) sourceChoice)
  have unit : 0 ≤ failure ∧ failure ≤ 1 :=
    ⟨localFailure_nonneg _ _ _ _ _, localFailure_le_one _ _ _ _ _⟩
  refine ⟨option, deviation, 1 - failure, by linarith [unit.2], by linarith [unit.1], ?_⟩
  intro common certificate stopped payoff
  have strategyEq : (target n).strategy = common := rfl
  have unforcedMass := (unforcedBound n who site notFree notOwing keyed).trans (le_abs_self _)
  have decorrelation := (decorrelated n who site notFree notOwing keyed).mono (le_abs_self _)
  have chosenNear := assembled_committed_value_sub_le setup timeouts
    leaks bounds
    horizon scheduler
    wellFormed covers capacity sequence inputs.scale positive le_one weights target assembled
      n opportunity inclusion
    timely completes site keyed.1 debtFree siteKey pending atSite unforcedMass decorrelation choice
    response selected sends packet node after sourceOffered parameter utility excludedPayoff
    boundNonneg (readoutBounded who) (excludedBounded who)
  have optionNear := assembled_keyed_value_sub_le setup timeouts leaks
    bounds
    horizon scheduler
    wellFormed covers capacity sequence inputs.scale positive le_one weights target assembled
      n opportunity inclusion
    timely completes site keyed.1 debtFree siteKey pending atSite unforcedMass decorrelation option
    parameter utility excludedPayoff boundNonneg (readoutBounded who) (excludedBounded who)
  dsimp only at chosenNear optionNear
  rw [strategyEq] at chosenNear optionNear
  have failNear := certificate_lateCommit_siteDecisionFailure setup timeouts leaks bounds horizon
    scheduler sequence inputs.scale positive le_one
    weights
      target
    assembled n covers (Nat.succ_le_of_lt slots_pos) (le_refl _) site keyed.1 debtFree siteKey
    pending node atSite unforcedMass choice response selected sends packet after inRange
  have transported := abs_siteCommitValue_sub_le setup timeouts leaks bounds horizon
    scheduler
    parameter utility excludedPayoff wellFormed (target n) (sequence n) site atSite ownTurn decision
    sourceChoice debtFree (readoutBounded who) (excludedBounded who)
  have distanceBound := (posterior n who site notFree notOwing atSite ownTurn decision).trans
    (le_abs_self _)
  have transportBound : |siteCommitValue setup timeouts leaks bounds horizon scheduler
    parameter
      utility excludedPayoff (target n) (setup.intendedOpeningProfile (sequence n).strategy) site
        sourceChoice.1 -
      siteValue setup timeouts leaks bounds horizon scheduler parameter utility
        excludedPayoff
        (target n) (setup.intendedOpeningProfile (sequence n).strategy) site -
      intendedSiteGain setup parameter utility excludedPayoff (sequence n) deviation| ≤
        transportError n := by
    exact transported.trans (add_le_add
      (mul_le_mul_of_nonneg_left distanceBound (by positivity))
      (mul_le_mul_of_nonneg_left unforcedMass (by positivity)))
  have baselineBounded : |siteValue setup timeouts leaks bounds horizon scheduler parameter
    utility
      excludedPayoff (target n) (setup.intendedOpeningProfile (sequence n).strategy) site -
        excludedPayoff who| ≤ 2 * payoffBound := by
    have sourceBound : |siteValue setup timeouts leaks bounds horizon scheduler parameter
      utility
        excludedPayoff (target n) (setup.intendedOpeningProfile (sequence n).strategy) site| ≤
          payoffBound := expect_abs_le_of_bounded boundNonneg (fun history =>
      abs_decodedPointValue_le setup timeouts leaks bounds horizon scheduler parameter
        utility
        excludedPayoff _ who _ history.1 (readoutBounded who) (excludedBounded who))
    exact (abs_sub _ _).trans (by linarith [excludedBounded who])
  have choiceBound : |expect ((target n).belief who site) (fun history =>
      expect ((N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature) common who
          ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff) -
      (excludedPayoff who + (1 - failure) *
        (siteCommitValue setup timeouts leaks bounds horizon scheduler parameter utility
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
        (siteValue setup timeouts leaks bounds horizon scheduler parameter utility
          excludedPayoff
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


end Vegas.OnePacketComparison
