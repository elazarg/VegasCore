module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketCommitmentComparisons
public import Vegas.Game.OnePacketSilenceComparison
public import Vegas.Game.OnePacketDisclosureComparison
public import Vegas.Game.OnePacketUnintendedComparison
public import Vegas.Game.OnePacketNonLateChoices
public import Vegas.Game.OnePacketStoppedValueComparison

@[expose] public section

/-! # Uniform source incentive bounds at nonlate native inputs -/

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

open Classical in
/-- All pure nonlate pending responses have vanishing gain or compare with one
original source deviation under the same assembled native assessment sequence. -/
theorem assembled_nonlate_pending_comparisons
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
        ∀ {event : (graph setup).EventId}, pendingEvent setup timeouts leaks who site.1 = some
          event →
        let common := (targetSequence n).strategy
        let certificate := ((Menu).bounded (initialLaw setup) horizon
          scheduler).wellFoundedHistories
        let stopped := fun final : (NP).History => ¬ Clear final.state ∨
          DecodedState setup timeouts leaks (failureProfile setup.program)
            (ProtocolState.OwesFailure who setup.program) final.state
        let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
          exclusionBase setup timeouts parameter utility excludedPayoff leaks final.state who
        let gain := expect ((targetSequence n).belief who site) (fun history =>
            expect ((N).runBehavioralUntil certificate
                (Profile.update (sig := (N).behavioralSignature) common who
                  ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
              expect ((N).runBehavioralUntil certificate common stopped history.1) payoff)
        gain ≤ error n ∨ ∃ sourceDeviation : setup.intendedModel.AssessmentDeviation who,
          gain ≤ intendedSiteGain setup parameter utility excludedPayoff (sequence n)
            sourceDeviation + error n := by
  obtain ⟨commitError, commitLimit, commitments⟩ :=
    OnePacketComparison.assembled_intendedCommitment_gain_bounds setup timeouts leaks bounds
      horizon
      scheduler
      wellFormed independent observable covers coversInputs capacity sequence sourceMixed
      sourceBayes scale
      positive le_one scaleEq weights targetSequence assembled mixed bayes opportunity inclusion
      timely completes parameter utility
      excludedPayoff below upper le_upper boundNonneg readoutBounded excludedBounded
  obtain ⟨drift, driftLimit, irregular⟩ := irregular_belief_bounds_of_assembled setup timeouts leaks
    bounds
    horizon scheduler wellFormed independent observable sequence sourceMixed scale positive
    le_one scaleEq
    covers coversInputs capacity weights targetSequence assembled mixed bayes
  let rowError := fun n =>
    2 * ((2 * payoffBound * (1 - slotRetention (scale n))) *
      (2 * horizon + 1)) + 2 * payoffBound * (1 - slotRetention (scale n)) +
    2 * payoffBound * (scale n ^ 3 * (2 * horizon + 1)) +
    (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
      (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * payoffBound)
  let error := fun n => |commitError n| + rowError n + 2 * payoffBound * |drift n|
  have scaleLimit : Tendsto scale atTop (nhds 0) := by
    have identity : scale = fun n => trembleScale
        (combinedFloor setup timeouts leaks bounds horizon scheduler (sequence n))
        (2 * horizon + 2) n := funext scaleEq
    rw [identity]
    exact tendsto_trembleScale _
      (fun n => combinedFloor_pos setup timeouts leaks bounds horizon scheduler (sequence n))
      (fun n => combinedFloor_le_one setup timeouts leaks bounds horizon scheduler
        (sequence n))
  have retentionLimit : Tendsto (fun n => 1 - slotRetention (scale n)) atTop (nhds 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_slotRetention scaleLimit)
  have cubeLimit : Tendsto (fun n => scale n ^ 3) atTop (nhds 0) := by
    simpa using scaleLimit.pow 3
  have rowLimit : Tendsto rowError atTop (nhds 0) := by
    have first := ((retentionLimit.const_mul (2 * payoffBound)).mul_const
      (2 * horizon + 1 : ℝ)).const_mul 2
    have physical := (((cubeLimit.add ((cubeLimit.add cubeLimit).const_mul
      (2 * horizon + 1 : ℝ))).const_mul 2).mul_const (2 * horizon + 1 : ℝ)).add
      (cubeLimit.mul_const (2 * horizon + 1 : ℝ))
    convert (((first.add (retentionLimit.const_mul (2 * payoffBound))).add
      ((cubeLimit.mul_const (2 * horizon + 1 : ℝ)).const_mul (2 * payoffBound))).add
      (physical.mul_const (2 * payoffBound))) using 1 <;> norm_num [rowError]
  have errorLimit : Tendsto error atTop (nhds 0) := by
    simpa only [abs_zero, zero_mul, mul_zero, add_zero, zero_add] using
      ((commitLimit.abs.add rowLimit).add ((driftLimit.abs).const_mul (2 * payoffBound)))
  refine ⟨error, errorLimit, ?_⟩
  intro n who site choice notFree notOwing nonlate event pending common certificate stopped payoff
    gain
  have rowNonneg : 0 ≤ rowError n := by
    have retention := slotRetention_le_one (positive n).le (le_one n)
    have := (positive n).le
    dsimp only [rowError]
    positivity
  have errorCovers : commitError n ≤ error n := by
    dsimp only [error]
    have : 0 ≤ 2 * payoffBound * |drift n| := by positivity
    linarith [le_abs_self (commitError n)]
  by_cases intendedChoice : IntendedCommitment setup timeouts leaks bounds horizon
    scheduler site
      choice
  · right
    obtain ⟨past, view, response, material, named, serial, payload, outputEq, value,
      atSite, selected, sends, packet, _after, _legal⟩ := intendedChoice
    have submitted : (submittedEvent? timeouts) leaks response = some named := by
      unfold EventGraphRuntime.submittedEvent?
      simp only [sends, packet, Payload.event?]
    have atTurn := commitsAtTurn_of_notOwing (timeouts := timeouts) wellFormed site notOwing choice
      selected submitted
    obtain ⟨deviation, bounded⟩ := commitments n who site choice notFree notOwing nonlate atTurn
      ⟨past, view, response, material, named, serial, payload, outputEq, value,
        atSite, selected, sends, packet, _after, _legal⟩
    exact ⟨deviation, bounded.trans (by linarith only [errorCovers])⟩
  left
  obtain ⟨past, view, atSite⟩ : ∃ past view, site.1 = some (past, view) := by
    cases observed : site.1 with
    | none => rw [observed] at pending; cases pending
    | some pair => exact ⟨pair.1, pair.2, rfl⟩
  obtain ⟨response, selected, member⟩ := choice_response setup timeouts leaks bounds horizon
    scheduler site atSite choice
  have regularRows : ∀ history : (N).InformationHistory who site.1,
      RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
        history.1.trace →
      expect ((N).runBehavioralUntil certificate
          (Profile.update (sig := (N).behavioralSignature) common who
            ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
        expect ((N).runBehavioralUntil certificate common stopped history.1) payoff ≤ rowError n :=
      by
    intro history regular
    cases sends : response.transmission with
    | none =>
        have silent : choice.1 = some ⟨none⟩ := by
          rw [selected]
          congr 1
          exact congrArg (fun transmission =>
            (⟨transmission⟩ : (application setup timeouts leaks).Action)) sends
        exact OnePacketComparison.assembled_silence_history_comparison setup timeouts leaks
          bounds
          horizon scheduler
          wellFormed covers capacity sequence scale positive le_one weights targetSequence assembled
          n opportunity inclusion
          timely completes site choice notFree notOwing nonlate event pending silent atSite
          parameter utility excludedPayoff below (upper who) (fun outcome => le_upper outcome who)
          boundNonneg (readoutBounded who) (excludedBounded who) history regular
    | some material =>
        obtain ⟨named, submitted⟩ := submittedEvent_of_transmits setup timeouts leaks bounds member
          sends
        have atTurn := commitsAtTurn_of_notOwing (timeouts := timeouts) wellFormed site notOwing
          choice selected submitted
        cases packet : material.call.packet with
        | malformed raw => exact (onePacket_not_malformed (timeouts := timeouts) bounds member sends
          raw packet).elim
        | commitment named candidate =>
            have near :=
              OnePacketComparison.assembled_unintendedCommitment_history_comparison setup
                timeouts
              leaks
              bounds horizon scheduler wellFormed covers capacity sequence scale positive le_one
              weights targetSequence assembled n opportunity inclusion timely completes site choice
              notFree notOwing nonlate
              atTurn intendedChoice atSite response selected material sends named candidate packet
              parameter utility excludedPayoff below (upper who)
              (fun outcome => le_upper outcome who) boundNonneg (readoutBounded who)
              (excludedBounded who) history regular
            have := (positive n).le
            have retention := slotRetention_le_one (positive n).le (le_one n)
            dsimp only [rowError]
            exact near.trans (by
              have retained : 0 ≤ 2 * payoffBound *
                  (1 - slotRetention (scale n)) *
                  (2 * horizon + 1) := by positivity
              have extra : 0 ≤ 2 * payoffBound * (scale n ^ 3 * (2 * horizon + 1)) +
                  (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
                    (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * payoffBound) := by
                positivity
              linarith)
        | opening named handle raw =>
            have forced := forcedAgent_of_not_free setup timeouts leaks bounds (initialLaw setup)
              horizon scheduler
              notFree
            have debtFree := siteDebtFree_of_not_owing setup timeouts leaks bounds horizon
              scheduler
              notOwing
            have ownIntended := ownCompletionsIntended_of_siteNotOwes (timeouts := timeouts)
              wellFormed debtFree history
            have allDebtFree := not_owesFailure_of_regular (timeouts := timeouts) wellFormed
              (sequence n) atSite forced
              history regular ownIntended
            have stateForced := forcedState_of_regular (timeouts := timeouts) wellFormed (sequence
              n) atSite forced
              history regular ownIntended
            obtain ⟨remaining, execution, point, current, actualAt, never, ordered, decoded,
              intended, reached⟩ := firstActivation_history_facts setup timeouts leaks bounds
                horizon
                scheduler
                wellFormed site pending nonlate history stateForced allDebtFree
            have namedEq : named = event := by
              have fromPacket : (submittedEvent? timeouts) leaks response = some named := by
                unfold EventGraphRuntime.submittedEvent?
                simp only [sends, packet, Payload.event?]
              obtain ⟨p, v, r, e, seen, chosen, submittedAt, turn⟩ := atTurn
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (atSite.symm.trans seen))
              have rEq := Option.some.inj (selected.symm.trans chosen)
              subst r
              have eEq := Option.some.inj (fromPacket.symm.trans submittedAt)
              subst e
              have pendingAt := pending
              rw [atSite] at pendingAt
              exact Option.some.inj
                (turn.symm.trans (pendingEvent_spec (timeouts := timeouts) pendingAt).1)
            subst named
            obtain ⟨payload, binding, checks, outputEq, codeEq, _node⟩ :=
              onePacket_opening_node (timeouts := timeouts) member sends packet
            let key := LateKey.ofView setup timeouts leaks who (execution.logs who)
              (execution.observe (application setup timeouts leaks) who)
            have pendingHere := pending
            rw [actualAt] at pendingHere
            have decided := decidedEvent_eq_of_pending setup timeouts leaks horizon scheduler
              pendingHere ((Menu).toRawTrace (initialLaw setup) horizon scheduler
                (current ▸ history.1.trace)) rfl
              (lateKey_some (timeouts := timeouts) who (execution.logs who)
                (execution.observe (application setup timeouts leaks) who))
            have near := OnePacketComparison.assembled_firstActivation_disclosure_gain_le
              (timeouts := timeouts)
              setup leaks bounds
              horizon scheduler wellFormed covers capacity sequence scale positive le_one weights
              targetSequence assembled n
              opportunity inclusion timely completes site (PMF.pure choice) history current actualAt
              event pending never key decided outputEq codeEq ordered decoded intended reached
              parameter utility excludedPayoff below (upper who)
              (fun outcome => le_upper outcome who) boundNonneg (readoutBounded who)
              (excludedBounded who)
            have := (positive n).le
            dsimp only [rowError]
            exact near.trans (by
              have extra : 0 ≤ 2 * payoffBound * (scale n ^ 3 * (2 * horizon + 1)) +
                  (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
                    (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * payoffBound) := by
                positivity
              linarith)
  let belief := (targetSequence n).belief who site
  let native := fun history : (N).InformationHistory who site.1 =>
    expect ((N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature) common who
          ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
      expect ((N).runBehavioralUntil certificate common stopped history.1) payoff
  let bad := fun history : (N).InformationHistory who site.1 =>
    if RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
      history.1.trace then (0 : ℝ) else 1
  have payoffBounded : ∀ final, |payoff final| ≤ payoffBound := by
    intro final
    dsimp only [payoff]
    split
    · exact excludedBounded who
    · cases final.state with
      | none =>
          simpa only [exclusionBase, abs_zero] using (abs_nonneg _).trans (excludedBounded who)
      | some control =>
          change |if who ∈ control.execution.application.config.defaulted then excludedPayoff who
            else exclusionReadoutUtility setup parameter utility excludedPayoff
              (sourceReadout setup timeouts leaks (some control)) who| ≤ payoffBound
          split
          · exact excludedBounded who
          · exact readoutBounded who _
  have rows : ∀ history, native history ≤ rowError n + 2 * payoffBound * bad history := by
    intro history
    by_cases regular : RegularTrace setup timeouts leaks bounds horizon scheduler (sequence
      n) who
        history.1.trace
    · simpa only [bad, regular, ↓reduceIte, mul_zero, add_zero] using regularRows history regular
    · have first := expect_abs_le_of_bounded (μ := (N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature) common who
          ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1)
        boundNonneg payoffBounded
      have second := expect_abs_le_of_bounded
        (μ := (N).runBehavioralUntil certificate common stopped history.1)
        boundNonneg payoffBounded
      dsimp only [native, bad]
      rw [ite_eq_right regular, mul_one]
      linarith [(abs_le.mp first).2, (abs_le.mp second).1]
  have averaged := expect_mono (μ := belief) (fun history _ => rows history)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  rw [expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
    expect_constant, expect_const_mul] at averaged
  have pendingHere := pending
  rw [atSite] at pendingHere
  have rare := irregular n who site notFree notOwing atSite (pendingEvent_spec (timeouts :=
    timeouts) pendingHere).1
  have scaled : 2 * payoffBound * expect belief bad ≤ 2 * payoffBound * |drift n| :=
    mul_le_mul_of_nonneg_left (rare.trans (le_abs_self (drift n)))
      (by positivity : 0 ≤ 2 * payoffBound)
  have complete : expect belief native ≤ rowError n + 2 * payoffBound * |drift n| := by
    linarith only [averaged, scaled]
  change expect belief native ≤ error n
  dsimp only [error]
  linarith only [complete, abs_nonneg (commitError n)]




open Classical in
/-- Every pure nonlate local deviation on the supplied native assessments has
vanishing gain or is bounded by a source deviation under the same beliefs. -/
theorem assembled_nonlate_local_comparisons
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
    (opportunity : Opportunity timeouts leaks (initialLaw setup) horizon scheduler delay)
    (inclusion : ProtectedInclusion timeouts leaks (initialLaw setup) horizon scheduler bound)
    (timely : (AsyncTimely timeouts) delay bound)
    (completes : CompletesPlay timeouts leaks (initialLaw setup) horizon scheduler)
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
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound)
    (payoffBounded : ∀ who (final : (NP).History),
      |exclusionBase setup timeouts parameter utility excludedPayoff leaks final.state who| ≤
        payoffBound) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (N).InformationSite who),
        ¬ Vegas.FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) →
        ¬ Vegas.OwingAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) →
        ¬ ownedKeyed
          (Vegas.FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler)
          (LateDeliveryAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler)
          ((N).agentAt site) →
        ∀ choice : (N).Choice who site.1,
          localGain (2 * horizon + 1) (fun final => final.state)
              (exclusionBase setup timeouts parameter utility excludedPayoff leaks)
                (targetSequence n) site (PMF.pure choice) ≤ error n ∨
          ∃ mixture : PMF (setup.intendedModel.AssessmentDeviation who),
            localGain (2 * horizon + 1) (fun final => final.state)
                (exclusionBase setup timeouts parameter utility excludedPayoff leaks)
                  (targetSequence n) site (PMF.pure choice) ≤
              expect mixture
                (intendedSiteGain setup parameter utility excludedPayoff (sequence n)) +
                error n := by
  obtain ⟨nativeError, nativeLimit, nativeComparisons⟩ :=
    assembled_nonlate_pending_comparisons setup timeouts leaks bounds horizon scheduler
      wellFormed independent observable covers coversInputs capacity sequence sourceMixed
      sourceBayes scale positive le_one scaleEq weights targetSequence assembled mixed bayes
      (fun control trace _ => opportunity control
        ((Menu).toRawTrace (initialLaw setup) horizon scheduler trace))
      (fun control trace _ => inclusion control
        ((Menu).toRawTrace (initialLaw setup) horizon scheduler trace)) timely
      (fun control trace _ ended => completes control
        ((Menu).toRawTrace (initialLaw setup) horizon scheduler trace) ended)
      parameter utility excludedPayoff below upper le_upper boundNonneg readoutBounded
      excludedBounded
  obtain ⟨valueError, valueLimit, comparisonValues⟩ :=
    assembled_terminal_stopped_comparison_bounds setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff wellFormed independent observable sequence sourceMixed
      scale positive le_one scaleEq covers coversInputs capacity weights targetSequence assembled
      mixed bayes opportunity inclusion timely completes boundNonneg payoffBounded excludedBounded
  let error := fun n => |nativeError n| + 2 * |valueError n|
  have limit : Tendsto error atTop (nhds 0) := by
    simpa only [abs_zero, zero_mul, mul_zero, add_zero] using
      nativeLimit.abs.add (valueLimit.abs.const_mul 2)
  refine ⟨error, limit, ?_⟩
  intro n who site notFree notOwing notKeyed choice
  have nonlate : ¬ LateDelivery setup timeouts leaks who site.1 :=
    fun late => notKeyed ⟨late, notFree⟩
  obtain ⟨past, view, atSite⟩ : ∃ past view, site.1 = some (past, view) := by
    obtain ⟨history, _running, _choice, _legal⟩ := site.2
    have active := InformationSite.active (N) site history
    obtain ⟨control, state, actor⟩ := (application setup timeouts leaks).control_of_active
      (initialLaw setup) horizon scheduler
      ((Menu).toRawHistory (initialLaw setup) horizon scheduler history.1) who active
    change history.1.state = some control at state
    have observed := ((Menu).info (initialLaw setup) horizon scheduler who
      history.1.trace).symm.trans history.2
    rw [state] at observed
    simp only [ReactiveApplication.observe, actor, ↓reduceIte] at observed
    exact ⟨control.execution.logs who,
      control.execution.observe (application setup timeouts leaks) who, observed.symm⟩
  cases pending : pendingEvent setup timeouts leaks who site.1 with
  | none =>
      left
      rw [localGain]
      have zero := withLaw_eq_self_of_unpending_notOwing (timeouts := timeouts) wellFormed
        site notOwing atSite pending ((targetSequence n).strategy who) (PMF.pure choice)
      rw [zero]
      simp only [assessmentComparisonWith, sub_self]
      dsimp only [error]
      positivity
  | some event =>
      have pendingAt := pending
      rw [atSite] at pendingAt
      have turn := (pendingEvent_spec (timeouts := timeouts) pendingAt).1
      have near := (comparisonValues n who site notFree notOwing atSite turn).2 (PMF.pure choice)
      dsimp only at near
      have upper := (abs_le.mp near).2
      have coversError : nativeError n + 2 * valueError n ≤ error n := by
        dsimp only [error]
        linarith [le_abs_self (nativeError n), le_abs_self (valueError n)]
      rcases nativeComparisons n who site choice notFree notOwing nonlate pending with
        bounded | ⟨deviation, bounded⟩
      · left
        dsimp only at bounded
        linarith only [upper, bounded, coversError]
      · right
        refine ⟨PMF.pure deviation, ?_⟩
        rw [expect_pure]
        dsimp only at bounded
        linarith only [upper, bounded, coversError]


end Vegas.OnePacketComparison
