module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketIntendedCommitmentComparison
public import Vegas.Game.OnePacketCommitmentSourcePolicy
public import Vegas.Game.OnePacketValueTransport
public import Vegas.Game.OnePacketOwnIntended
public import Vegas.Game.OnePacketPrescribedSites
public import Vegas.Game.OnePacketRecordedSilence
public import Vegas.Game.IntendedChoiceReach
public import Vegas.Game.OnePacketSourceBeliefBounds
public import Vegas.Game.OnePacketIrregularBeliefBounds
public import GameTheoryExtensions.Analysis.Protocol.SourceGainTransport
public import GameTheoryExtensions.Math.Probability.TotalVariation

@[expose] public section

/-! # Source incentive comparisons for intended native commitments -/

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

local notation "N" => onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
  scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu timeouts leaks) (initialLaw setup) horizon scheduler
local notation "Menu" => bounds.onePacketMenu timeouts leaks
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup timeouts leaks)
    (fun native : EventGraphRuntime.State (graph setup) =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config native) = ∅)

open Classical in
/-- One original source commitment bounds the native gain at every regular
history of the same complete nonlate input. -/
theorem assembled_intendedCommitment_history_comparisons
    [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence scale
      positive le_one weights targetSequence) (n : ℕ)
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
    {who : Player} (site : (N).InformationSite who) (choice : (N).Choice who site.1)
    (notFree : ¬ Vegas.FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt site))
    (notOwing : ¬ Vegas.OwingAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt site))
    (nonlate : ¬ LateDelivery setup timeouts leaks who site.1)
    (atTurn : CommitsAtTurn setup timeouts leaks bounds horizon scheduler who site choice)
    (intendedChoice : IntendedCommitment setup timeouts leaks bounds horizon scheduler site
      choice)
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} (atSite : site.1 = some (past, view))
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup timeouts leaks who
      site.1))
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
    let common := (targetSequence n).strategy
    let certificate := ((Menu).bounded (initialLaw setup) horizon
      scheduler).wellFoundedHistories
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup timeouts leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup timeouts parameter utility excludedPayoff leaks final.state who
    ∃ sourceChoice : setup.intendedModel.Choice who (projectView setup timeouts leaks who site.1),
      ∀ history : (N).InformationHistory who site.1,
      RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
        history.1.trace →
      expect ((N).runBehavioralUntil certificate
          (Profile.update (sig := (N).behavioralSignature) common who
            ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
        expect ((N).runBehavioralUntil certificate common stopped history.1) payoff ≤
        setup.intendedModel.historyGain
          (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
          (intendedReadoutExclusion setup parameter utility excludedPayoff) (payoffComponent setup)
          (sequence n) (projectedSite setup timeouts leaks decision,
            ((sequence n).strategy who).commit (projectView setup timeouts leaks who site.1)
              sourceChoice)
          (replayProjection setup timeouts leaks bounds horizon scheduler
            (projectedSite setup timeouts leaks decision) site atSite rfl history) +
        2 * ((2 * payoffBound * (1 - slotRetention (scale n))) *
          (2 * horizon + 1)) + 2 * payoffBound * (1 - slotRetention (scale n)) := by
  intro common certificate stopped payoff
  obtain ⟨sourceChoice, event, payload, outputEq, value, sourceAction,
    ⟨response, material, serial, selected, sends, packet, after, turn⟩, _sourceGain⟩ :=
    intendedCommitment_sourcePolicy_gain setup timeouts leaks bounds horizon scheduler
      wellFormed
      (sequence n) parameter utility excludedPayoff site choice atTurn intendedChoice decision
      atSite readoutBounded
  refine ⟨sourceChoice, ?_⟩
  intro history regular
  have forced := forcedAgent_of_not_free setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler notFree
  have debtFree := siteDebtFree_of_not_owing setup timeouts leaks bounds horizon scheduler
    notOwing
  have ownIntended := ownCompletionsIntended_of_siteNotOwes (timeouts := timeouts) wellFormed
    debtFree history
  have allDebtFree := not_owesFailure_of_regular (timeouts := timeouts) wellFormed (sequence n)
    atSite forced history
    regular ownIntended
  have stateForced := forcedState_of_regular (timeouts := timeouts) wellFormed (sequence n) atSite
    forced history regular
    ownIntended
  have submitted : (submittedEvent? timeouts) leaks response = some event := by
    unfold EventGraphRuntime.submittedEvent?
    simp only [sends, packet, Payload.event?]
  have pending : pendingEvent setup timeouts leaks who site.1 = some event := by
    by_cases unrecorded : (eventRecorded timeouts) leaks past event = false
    · rw [atSite]
      exact pendingEvent_of_spec (timeouts := timeouts) turn unrecorded
    · have recorded := Bool.eq_true_of_not_eq_false unrecorded
      have unpending : pendingEvent setup timeouts leaks who site.1 = none := by
        rw [atSite]
        simp [pendingEvent, turn, recorded]
      have quiet := choice_eq_silence_of_unpending_notOwing (timeouts := timeouts) wellFormed
        site notOwing atSite unpending choice
      rw [selected, Option.some.injEq] at quiet
      rw [quiet] at sends
      cases sends
  obtain ⟨remaining, execution, point, current, actualAt, never, ordered, decoded, intended,
    _reached⟩ := firstActivation_history_facts setup timeouts leaks bounds horizon scheduler
      wellFormed site pending nonlate history stateForced allDebtFree
  have member : response ∈ bounds.onePacketActions timeouts leaks who past view := by
    obtain ⟨other, otherChosen, offered⟩ := choice_response setup timeouts leaks bounds horizon
      scheduler site atSite choice
    have same := Option.some.inj (selected.symm.trans otherChosen)
    subst other
    exact offered
  obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj (Option.some.inj (atSite.symm.trans actualAt))
  subst past view
  obtain ⟨_owner, _slot, foundPayload, foundOutput, codeEq, _rest⟩ :=
    onePacket_commitment_facts (timeouts := timeouts) bounds member sends packet
  have payloadEq : foundPayload = payload := by
    exact (EventGraph.EventField.binding.inj (foundOutput.symm.trans outputEq)).2
  subst foundPayload
  have code : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload := by
    exact codeEq
  let key := LateKey.ofView setup timeouts leaks who (execution.logs who)
    (execution.observe (application setup timeouts leaks) who)
  have pendingHere := pending
  rw [actualAt] at pendingHere
  have decided := decidedEvent_eq_of_pending setup timeouts leaks horizon scheduler
    pendingHere
    ((Menu).toRawTrace (initialLaw setup) horizon scheduler (current ▸ history.1.trace)) rfl
    (lateKey_some (timeouts := timeouts) who (execution.logs who)
      (execution.observe (application setup timeouts leaks) who))
  obtain ⟨replay, replayed⟩ := intendedHistory?_isSome_of_debtFree (timeouts := timeouts) wellFormed
    history.1.trace
    _ current (by
      intro found foundDecoded
      exact allDebtFree found (by rw [current]; exact foundDecoded))
  have projection := replayProjection_eq (timeouts := timeouts) (setup := setup) (leaks := leaks)
    (bounds := bounds)
    (horizon := horizon) (scheduler := scheduler)
    (sourceSite := projectedSite setup timeouts leaks decision) actualAt rfl history replayed
  have replayState := intendedHistory?_state (timeouts := timeouts) history.1.trace replayed
  rw [current] at replayState
  have sourceState : (replayProjection setup timeouts leaks bounds horizon scheduler
      (projectedSite setup timeouts leaks decision) site actualAt rfl history).1.state = some point
        := by
    rw [projection, replayState]
    exact (decodedPoint_eq_of_isPrefix ordered).trans decoded
  exact OnePacketComparison.assembled_firstActivation_commitment_gain_le setup timeouts leaks
    bounds
    horizon scheduler
    wellFormed covers capacity sequence scale positive le_one weights targetSequence assembled n
    opportunity inclusion timely
    completes site choice response selected history current actualAt member material sends event
    packet pending never key decided outputEq code after ordered decoded intended
    (projectedSite setup timeouts leaks decision) sourceChoice sourceAction _ sourceState parameter
      utility
    excludedPayoff below upper le_upper boundNonneg readoutBounded excludedBounded


open Classical in
/-- Averaging the common-history comparison adds only the bounded mass of
irregular histories. -/
theorem assembled_intendedCommitment_belief_comparison
    [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence scale
      positive le_one weights targetSequence) (n : ℕ)
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
    {who : Player} (site : (N).InformationSite who) (choice : (N).Choice who site.1)
    (notFree : ¬ Vegas.FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt site))
    (notOwing : ¬ Vegas.OwingAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt site))
    (nonlate : ¬ LateDelivery setup timeouts leaks who site.1)
    (atTurn : CommitsAtTurn setup timeouts leaks bounds horizon scheduler who site choice)
    (intendedChoice : IntendedCommitment setup timeouts leaks bounds horizon scheduler site
      choice)
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} (atSite : site.1 = some (past, view))
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup timeouts leaks who
      site.1))
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
    (excludedBounded : |excludedPayoff who| ≤ payoffBound)
    :
    let common := (targetSequence n).strategy
    let certificate := ((Menu).bounded (initialLaw setup) horizon
      scheduler).wellFoundedHistories
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup timeouts leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup timeouts parameter utility excludedPayoff leaks final.state who
    let belief := (targetSequence n).belief who site
    ∃ sourceChoice : setup.intendedModel.Choice who (projectView setup timeouts leaks who site.1),
      expect belief (fun history =>
        expect ((N).runBehavioralUntil certificate
            (Profile.update (sig := (N).behavioralSignature) common who
              ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
          expect ((N).runBehavioralUntil certificate common stopped history.1) payoff) ≤
        expect (belief.map (replayProjection setup timeouts leaks bounds horizon scheduler
            (projectedSite setup timeouts leaks decision) site atSite rfl))
          (setup.intendedModel.historyGain
            (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
            (intendedReadoutExclusion setup parameter utility excludedPayoff)
            (payoffComponent setup)
            (sequence n) (projectedSite setup timeouts leaks decision,
              ((sequence n).strategy who).commit
                (projectView setup timeouts leaks who site.1) sourceChoice)) +
        (2 * ((2 * payoffBound * (1 - slotRetention (scale n))) *
          (2 * horizon + 1)) + 2 * payoffBound * (1 - slotRetention (scale n))) +
        4 * payoffBound * expect belief (fun history =>
          if RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
            history.1.trace then (0 : ℝ) else 1) := by
  intro common certificate stopped payoff belief
  obtain ⟨sourceChoice, perHistory⟩ :=
    assembled_intendedCommitment_history_comparisons setup timeouts leaks
      bounds
      horizon scheduler
      wellFormed covers capacity sequence scale positive le_one weights targetSequence assembled n
      opportunity inclusion
      timely completes site choice notFree notOwing nonlate atTurn intendedChoice atSite decision
      parameter utility excludedPayoff below upper le_upper boundNonneg readoutBounded
      excludedBounded
  refine ⟨sourceChoice, ?_⟩
  let source := setup.intendedModel.historyGain
    (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
    (intendedReadoutExclusion setup parameter utility excludedPayoff) (payoffComponent setup)
    (sequence n) (projectedSite setup timeouts leaks decision,
      ((sequence n).strategy who).commit (projectView setup timeouts leaks who site.1) sourceChoice)
  let replay := replayProjection setup timeouts leaks bounds horizon scheduler
    (projectedSite setup timeouts leaks decision) site atSite rfl
  let native := fun history : (N).InformationHistory who site.1 =>
    expect ((N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature) common who
          ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
      expect ((N).runBehavioralUntil certificate common stopped history.1) payoff
  let error := 2 * ((2 * payoffBound *
      (1 - slotRetention (scale n))) * (2 * horizon + 1)) +
    2 * payoffBound * (1 - slotRetention (scale n))
  let irregular := fun history : (N).InformationHistory who site.1 =>
    if RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
      history.1.trace then (0 : ℝ) else 1
  have errorNonneg : 0 ≤ error := by
    have retention := slotRetention_le_one (positive n).le (le_one n)
    dsimp only [error]
    positivity
  have payoffBounded : ∀ final, |payoff final| ≤ payoffBound := by
    intro final
    dsimp only [payoff]
    split
    · exact excludedBounded
    · cases final.state with
      | none =>
          simpa only [exclusionBase, abs_zero] using (abs_nonneg _).trans excludedBounded
      | some control =>
          change |if who ∈ control.execution.application.config.defaulted then excludedPayoff who
            else exclusionReadoutUtility setup parameter utility excludedPayoff
              (sourceReadout setup timeouts leaks (some control)) who| ≤ payoffBound
          split
          · exact excludedBounded
          · exact readoutBounded _
  have nativeBounded : ∀ history, |native history| ≤ 2 * payoffBound := by
    intro history
    have first := expect_abs_le_of_bounded (μ := (N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) common who
        ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1)
      boundNonneg payoffBounded
    have second := expect_abs_le_of_bounded
      (μ := (N).runBehavioralUntil certificate common stopped history.1)
      boundNonneg payoffBounded
    dsimp only [native]
    exact (abs_sub _ _).trans (by linarith)
  have sourceBounded : ∀ history, |source history| ≤ 2 * payoffBound := by
    intro history
    exact intended_historyGain_abs_le_of_readoutBounded (sequence n) parameter utility
      excludedPayoff boundNonneg readoutBounded _ history
  have pointwise : ∀ history, native history ≤
      (source (replay history) + error) + 4 * payoffBound * irregular history := by
    intro history
    by_cases regular : RegularTrace setup timeouts leaks bounds horizon scheduler (sequence
      n) who
        history.1.trace
    · simp only [irregular, regular, ↓reduceIte, mul_zero, add_zero]
      simpa only [native, source, replay, error, add_assoc] using perHistory history regular
    · simp only [irregular, regular, ↓reduceIte, mul_one]
      linarith [(abs_le.mp (nativeBounded history)).2,
        (abs_le.mp (sourceBounded (replay history))).1]
  rw [expect_map]
  calc expect belief native ≤ expect belief
        (fun history => (source (replay history) + error) +
          4 * payoffBound * irregular history) :=
      expect_mono (fun history _ => pointwise history) (payoffIntegrable_of_finite _ _)
        (payoffIntegrable_of_finite _ _)
    _ = _ := by
      rw [expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
        expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
        expect_constant, expect_const_mul]
      rfl




variable {Public : Type*} {signal : State L setup.context → Public}

open Classical in
/-- The exact assembled native sequence has a uniformly vanishing error for
nonlate intended commitments against one original source deviation. -/
theorem assembled_intendedCommitment_gain_bounds
    [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
    [Finite setup.intendedProtocol.History]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup timeouts leaks bounds horizon scheduler (sequence n))
      (2 * horizon + 2) n)
    (weights : ℕ → ∀ p,
      PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup) horizon scheduler
        bounds.candidateCount p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence scale
      positive le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (N) (targetSequence n)
      ((bounds.onePacketMenu timeouts leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain)
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
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (upper : Player → ℝ) (le_upper : ∀ outcome who, utility outcome who ≤ upper who)
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
        ¬ LateDelivery setup timeouts leaks who site.1 →
        CommitsAtTurn setup timeouts leaks bounds horizon scheduler who site choice →
        IntendedCommitment setup timeouts leaks bounds horizon scheduler site choice →
        ∃ sourceDeviation : setup.intendedModel.AssessmentDeviation who,
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
                expect ((N).runBehavioralUntil certificate common stopped history.1) payoff) ≤
            intendedSiteGain setup parameter utility excludedPayoff (sequence n) sourceDeviation +
              error n := by
  obtain ⟨distance, distanceLimit, posterior⟩ := source_belief_bounds_of_assembled setup
    timeouts leaks
    bounds horizon scheduler wellFormed independent observable sequence sourceMixed sourceBayes
    scale positive
    le_one scaleEq covers coversInputs capacity weights targetSequence assembled mixed bayes
  obtain ⟨drift, driftLimit, irregular⟩ := irregular_belief_bounds_of_assembled setup timeouts leaks
    bounds
    horizon scheduler wellFormed independent observable sequence sourceMixed scale positive
    le_one scaleEq
    covers coversInputs capacity weights targetSequence assembled mixed bayes
  let retentionError := fun n => 1 - slotRetention (scale n)
  let error := fun n =>
    (2 * ((2 * payoffBound * retentionError n)) *
      (2 * horizon + 1) + 2 * payoffBound * retentionError n) +
    4 * payoffBound * drift n + 2 * payoffBound * distance n
  have scaleLimit : Tendsto scale atTop (nhds 0) := by
    have identity : scale = fun n => trembleScale
        (combinedFloor setup timeouts leaks bounds horizon scheduler (sequence n))
        (2 * horizon + 2) n := funext scaleEq
    rw [identity]
    exact tendsto_trembleScale _
      (fun n => combinedFloor_pos setup timeouts leaks bounds horizon scheduler (sequence n))
      (fun n => combinedFloor_le_one setup timeouts leaks bounds horizon scheduler
        (sequence n))
  have retentionLimit : Tendsto retentionError atTop (nhds 0) := by
    simpa only [retentionError, sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_slotRetention scaleLimit)
  have errorLimit : Tendsto error atTop (nhds 0) := by
    have first := (retentionLimit.const_mul (2 * payoffBound)).const_mul 2
    have limit := ((first.mul_const (2 * horizon + 1 : ℝ)).add
      (retentionLimit.const_mul (2 * payoffBound))).add
      (driftLimit.const_mul (4 * payoffBound))
    simpa only [zero_mul, mul_zero, zero_add, add_zero] using
      limit.add (distanceLimit.const_mul (2 * payoffBound))
  refine ⟨error, errorLimit, ?_⟩
  intro n who site choice notFree notOwing nonlate atTurn intendedChoice
  obtain ⟨past, view, response, event, atSite, selected, submitted, turn⟩ := atTurn
  have forced := forcedAgent_of_not_free setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler notFree
  have debtFree := siteDebtFree_of_not_owing setup timeouts leaks bounds horizon scheduler
    notOwing
  have decision := projectedDecision_of_forcedAgent (timeouts := timeouts) wellFormed forced atSite
    turn debtFree
  obtain ⟨sourceChoice, averaged⟩ :=
    assembled_intendedCommitment_belief_comparison setup timeouts leaks
      bounds
      horizon scheduler
      wellFormed covers capacity sequence scale positive le_one weights targetSequence assembled n
      opportunity inclusion
      timely completes site choice notFree notOwing nonlate
      ⟨past, view, response, event, atSite, selected, submitted, turn⟩ intendedChoice atSite
      decision
      parameter utility excludedPayoff below (upper who) (fun outcome => le_upper outcome who)
      boundNonneg (readoutBounded who) (excludedBounded who)
  let sourceSite := projectedSite setup timeouts leaks decision
  let deviation : setup.intendedModel.AssessmentDeviation who :=
    (sourceSite, ((sequence n).strategy who).commit sourceSite.1 sourceChoice)
  refine ⟨deviation, ?_⟩
  intro common certificate stopped payoff
  let sourceGain := setup.intendedModel.historyGain
    (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
    (intendedReadoutExclusion setup parameter utility excludedPayoff) (payoffComponent setup)
    (sequence n) deviation
  have sourceBounded : ∀ history, |sourceGain history| ≤ 2 * payoffBound :=
    intended_historyGain_abs_le_of_readoutBounded (sequence n) parameter utility excludedPayoff
      boundNonneg (readoutBounded who) deviation
  have transported := expect_sub_le_of_bounded
    (((targetSequence n).belief who site).map
        (replayProjection setup timeouts leaks bounds horizon scheduler sourceSite site
          atSite rfl))
    ((sequence n).belief who sourceSite) sourceGain sourceBounded
  have near := posterior n who site notFree notOwing atSite turn decision
  have rare := irregular n who site notFree notOwing atSite turn
  have sourceEq := setup.intendedModel.gain_eq_expect_historyGain
    (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
    (intendedReadoutExclusion setup parameter utility excludedPayoff) (payoffComponent setup)
    (sequence n) deviation
  have scaled := mul_le_mul_of_nonneg_left near (by positivity : 0 ≤ 2 * payoffBound)
  have scaledRare := mul_le_mul_of_nonneg_left rare (by positivity : 0 ≤ 4 * payoffBound)
  dsimp only at averaged
  let nativeGain := expect
    ((targetSequence n).belief who site) (fun history =>
        expect ((N).runBehavioralUntil certificate
          (Profile.update (sig := (N).behavioralSignature) common who
            ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
        expect ((N).runBehavioralUntil certificate common stopped history.1) payoff)
  let replayedMean := expect
    (((targetSequence n).belief who site).map
        (replayProjection setup timeouts leaks bounds horizon scheduler sourceSite site
          atSite rfl))
    sourceGain
  let sourceMean := expect ((sequence n).belief who sourceSite) sourceGain
  let irregularMass := expect
    ((targetSequence n).belief who site) (fun history =>
        if RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
          history.1.trace then (0 : ℝ) else 1)
  have compared : nativeGain ≤ replayedMean +
      (2 * ((2 * payoffBound * (1 - slotRetention (scale n))) *
        (2 * horizon + 1)) + 2 * payoffBound * (1 - slotRetention (scale n))) +
      4 * payoffBound * irregularMass := averaged
  have transferred : replayedMean - sourceMean ≤ 2 * payoffBound * distance n :=
    transported.trans scaled
  have rareBound : 4 * payoffBound * irregularMass ≤ 4 * payoffBound * drift n := scaledRare
  change intendedSiteGain setup parameter utility excludedPayoff (sequence n) deviation =
    sourceMean at sourceEq
  change nativeGain ≤ intendedSiteGain setup parameter utility excludedPayoff (sequence n)
    deviation + error n
  rw [sourceEq]
  dsimp only [error, retentionError]
  linarith only [compared, transferred, rareBound]


end Vegas.OnePacketComparison
