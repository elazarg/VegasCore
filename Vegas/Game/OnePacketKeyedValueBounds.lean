/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketKeyedFailure
import Vegas.Game.OnePacketLateUniform
import Vegas.Game.OnePacketPendingValueAffine
import Vegas.Game.OnePacketCompletionPotential
import GameTheoryExtensions.Math.Probability.AffineDecorrelation

/-! # Affine keyed values on the actual native assessment sequence -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)
  {Public : Type*} {signal : State L setup.context → Public}

local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon scheduler
local notation "Menu" => bounds.onePacketMenu runtime leaks
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks)
    (fun native : EventGraphRuntime.State (graph setup) =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config native) = ∅)

open Classical in
/-- The same native comparison posterior factors the pending-event failure and
source continuation value, given the concrete forced-history affine estimate. -/
private theorem keyed_value_sub_le_of_pending
    [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds (initialLaw setup)
      horizon scheduler bounds.candidateCount p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale
      positive le_one weights targetSequence) (n
        : ℕ)
    {who : Player} (site : (N).InformationSite who)
    (late : LateDelivery setup runtime leaks who site.1)
    (debtFree : SiteDebtFree setup runtime leaks bounds horizon scheduler site)
    {key : LateKey setup runtime leaks} (siteKey : lateKey setup runtime leaks who site.1 = some
      key)
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past, view))
    {unforced gamma : ℝ}
    (unforcedMass : expect ((targetSequence n).belief who site) (fun history =>
        if ForcedState setup runtime leaks who history.1.state then (0 : ℝ) else 1) ≤ unforced)
    (decorrelated : BeliefDecorrelated ((targetSequence n).belief who site)
      (fun history => operationalRecord setup runtime leaks bounds horizon scheduler
        history.1.trace)
      (fun history => nativeDecodedState setup runtime leaks history.1.state) gamma)
    (option : LateOption bounds.candidateCount)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound)
    (boundaryError : ℝ) (boundaryErrorNonneg : 0 ≤ boundaryError) :
    let target := targetSequence n
    let common := target.strategy
    let certificate := ((Menu).bounded (initialLaw setup) horizon
      scheduler).wellFoundedHistories
    let law := onePacketLate setup runtime leaks bounds horizon scheduler sequence scale
      positive
      le_one n ((N).agentAt site) option
    let installed := Profile.update (sig := (N).behavioralSignature) common who
      ((common who).withLaw site.1 law)
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who
    let error := boundaryError *
      (2 * horizon + 1) +
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
        (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * payoffBound) +
      2 * payoffBound * (scale n ^ 3 * (2 * horizon + 1))
    (∀ history : (N).InformationHistory who site.1,
      ForcedState setup runtime leaks who history.1.state →
      let failure := expect (localHistoryRun (2 * horizon + 1) target site law history)
        (fun final => if DecisionFailed (runtime := runtime) key final.state then (1 : ℝ) else 0)
      let value := decodedPointValue setup runtime leaks bounds horizon scheduler
        parameter utility
        excludedPayoff (setup.intendedOpeningProfile (sequence n).strategy) who (siteRank (runtime
          := runtime) site.1)
        history.1
      |expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff -
        ((1 - failure) * value + failure * excludedPayoff who)| ≤ error) →
    |expect (target.belief who site) (fun history =>
        expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff) -
      (excludedPayoff who +
        (1 - localFailure (2 * horizon + 1) target site
          {final | DecisionFailed (runtime := runtime) key final.state} law) *
          (siteValue setup runtime leaks bounds horizon scheduler parameter utility
            excludedPayoff
            target (setup.intendedOpeningProfile (sequence n).strategy) site - excludedPayoff
              who))| ≤
      error + 2 * payoffBound * unforced +
      4 * payoffBound * ((2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3) + unforced) +
      4 * payoffBound * gamma := by
  intro target common certificate law installed stopped payoff error pendingAffine
  let belief := target.belief who site
  let failure := fun history : (N).InformationHistory who site.1 =>
    expect (localHistoryRun (2 * horizon + 1) target site law history)
      (fun final => if DecisionFailed (runtime := runtime) key final.state then (1 : ℝ) else 0)
  let value := fun history : (N).InformationHistory who site.1 =>
    decodedPointValue setup runtime leaks bounds horizon scheduler parameter utility
      excludedPayoff
      (setup.intendedOpeningProfile (sequence n).strategy) who (siteRank (runtime := runtime)
        site.1) history.1
  let valueOf : setup.ProtocolState → ℝ := fun found => match found with
    | none => excludedPayoff who
    | some point => if IntendedReached setup point then
        sourcePointValue setup parameter utility excludedPayoff
          (setup.intendedOpeningProfile (sequence n).strategy) who point else excludedPayoff who
  let result := fun history : (N).InformationHistory who site.1 =>
    expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff
  let lumping := certificateLumping setup runtime leaks bounds horizon scheduler sequence scale
    positive le_one covers (by have := capacity who; omega) (le_refl _) weights
    targetSequence assembled n who
  let lumped := lumpedFailure setup runtime leaks bounds horizon scheduler lumping
    (2 * horizon + 1) key option
  let pathError : ℝ := (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)
  have pathNonneg : 0 ≤ pathError := by
    have := (positive n).le
    dsimp only [pathError]
    positivity
  have errorNonneg : 0 ≤ error := by
    have := boundaryErrorNonneg
    have := (positive n).le
    dsimp only [error]
    positivity
  have failureUnit : ∀ history, 0 ≤ failure history ∧ failure history ≤ 1 := by
    intro history
    exact expect_mem_unit _ _ fun _ => by split <;> norm_num
  have lumpedUnit : ∀ record, 0 ≤ lumped record ∧ lumped record ≤ 1 := by
    intro record
    exact expect_mem_unit _ _ (lumping.failure_unit key)
  have valueBounded : ∀ found, |valueOf found| ≤ payoffBound := by
    intro found
    cases found with
    | none => exact excludedBounded
    | some point =>
        simp only [valueOf]
        split
        · exact expect_abs_le_of_bounded boundNonneg readoutBounded
        · exact excludedBounded
  have valueEq : ∀ history : (N).InformationHistory who site.1,
      value history = valueOf (nativeDecodedState setup runtime leaks history.1.state) := by
    intro history
    obtain ⟨remaining, execution, current, _, _, ordered⟩ :=
      ordered_of_site setup runtime leaks bounds horizon scheduler atSite history
    unfold value decodedPointValue
    rw [current]
    change _ = valueOf (decodedPoint setup execution.application.config)
    rw [decodedPoint_eq_of_isPrefix ordered]
    rfl
  have failureNear : expect belief (fun history => |failure history - lumped
      (operationalRecord setup runtime leaks bounds horizon scheduler history.1.trace)|) ≤
      pathError + unforced := by
    have pointwise : ∀ history ∈ belief.support,
        |failure history - lumped (operationalRecord setup runtime leaks bounds horizon
          scheduler
          history.1.trace)| ≤ pathError +
          if ForcedState setup runtime leaks who history.1.state then (0 : ℝ) else 1 := by
      intro history supported
      by_cases forced : ForcedState setup runtime leaks who history.1.state
      · simp only [forced, ↓reduceIte, add_zero]
        have near := lumping.pathwise (2 * horizon + 1) site ⟨Or.inl late,
          debtFree⟩ key siteKey
          option history supported forced
        simpa only [failure, localHistoryRun, lumped, pathError, target, law,
          InformationModel.truncatedRunner, lumpedFailure ] using near
      · simp only [forced, ↓reduceIte]
        have := failureUnit history
        have := lumpedUnit (operationalRecord setup runtime leaks bounds horizon scheduler
          history.1.trace)
        rw [abs_le]
        constructor <;> linarith
    have averaged := expect_mono pointwise (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)
    rw [expect_add (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _),
      expect_constant] at averaged
    exact averaged.trans (by dsimp only [belief]; linarith [unforcedMass])
  have payoffNear : expect belief (fun history =>
      |result history - (excludedPayoff who +
        (1 - failure history) * (value history - excludedPayoff who))|) ≤
      error + 2 * payoffBound * unforced := by
    have payoffBounded : ∀ final, |payoff final| ≤ payoffBound := by
      intro final
      dsimp only [payoff]
      split
      · exact excludedBounded
      · cases state : final.state with
        | none => simpa only [state, exclusionBase, abs_zero] using boundNonneg
        | some control =>
            by_cases defaulted : who ∈ control.execution.application.config.defaulted
            · simpa only [state, exclusionBase, defaulted, ite_true] using excludedBounded
            · simpa only [state, exclusionBase, defaulted, ite_false] using
                readoutBounded (sourceReadout setup runtime leaks (some control))
    have pointwise : ∀ history ∈ belief.support,
        |result history - (excludedPayoff who +
          (1 - failure history) * (value history - excludedPayoff who))| ≤
        error + 2 * payoffBound *
          if ForcedState setup runtime leaks who history.1.state then (0 : ℝ) else 1 := by
      intro history _supported
      by_cases forced : ForcedState setup runtime leaks who history.1.state
      · simp only [forced, ↓reduceIte, mul_zero, add_zero]
        have near := pendingAffine history forced
        have centered : (excludedPayoff who +
            (1 - failure history) * (value history - excludedPayoff who)) =
            (1 - failure history) * value history + failure history * excludedPayoff who := by ring
        rw [centered]
        exact near
      · simp only [forced, ↓reduceIte, mul_one]
        have resultBound := expect_abs_le_of_bounded boundNonneg payoffBounded
          (μ := ((N).runBehavioralUntil certificate installed stopped history.1))
        have sourceBound : |value history| ≤ payoffBound := by rw [valueEq]; exact valueBounded _
        have failedUnit := failureUnit history
        have mixtureBound : |excludedPayoff who +
            (1 - failure history) * (value history - excludedPayoff who)| ≤ payoffBound := by
          rw [abs_le] at excludedBounded sourceBound ⊢
          constructor <;> nlinarith
        exact (abs_sub _ _).trans (by linarith)
    have averaged := expect_mono pointwise (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)
    rw [expect_add (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _),
      expect_constant, expect_const_mul] at averaged
    have nonneg : 0 ≤ 2 * payoffBound := by linarith
    have scaled := mul_nonneg nonneg (sub_nonneg.mpr unforcedMass)
    dsimp only [belief] at averaged
    nlinarith
  have affine := abs_expect_affine_sub_le_of_decorrelated belief
    (fun history => operationalRecord setup runtime leaks bounds horizon scheduler
      history.1.trace)
    (fun history => nativeDecodedState setup runtime leaks history.1.state) decorrelated failure
      result
      value
    lumped valueOf (excludedPayoff who)
    (fun history => by have := failureUnit history; rw [abs_le]; constructor <;> linarith)
    (fun record => by have := lumpedUnit record; rw [abs_le]; constructor <;> linarith)
    valueBounded valueEq excludedBounded (payoffIntegrable_of_finite _ _) failureNear payoffNear
  have failureEq : localFailure (2 * horizon + 1) target site
      {final | DecisionFailed (runtime := runtime) key final.state} law = expect belief failure :=
        by
    unfold localFailure
    rw [expect_localRun]
    rfl
  rw [failureEq]
  exact affine

open Classical in
theorem assembled_keyed_value_sub_le
    [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds (initialLaw setup)
      horizon scheduler bounds.candidateCount p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale
      positive le_one weights targetSequence) (n
        : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some
        control) →
      control.execution.application.config.defaulted = ∅ →
      OpportunityAt runtime leaks control.execution delay)
    (inclusion : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some
        control) →
      control.execution.application.config.defaulted = ∅ →
      ProtectedInclusionAt runtime leaks control.execution bound)
    (timely : runtime.AsyncTimely delay bound)
    (completes : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some
        control) →
      control.execution.application.config.defaulted = ∅ →
      (application setup runtime leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    {who : Player} (site : (N).InformationSite who)
    (late : LateDelivery setup runtime leaks who site.1)
    (debtFree : SiteDebtFree setup runtime leaks bounds horizon scheduler site)
    {key : LateKey setup runtime leaks} (siteKey : lateKey setup runtime leaks who site.1 = some
      key)
    {event : (graph setup).EventId} (pending : pendingEvent setup runtime leaks who site.1 = some
      event)
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past, view))
    {unforced gamma : ℝ}
    (unforcedMass : expect ((targetSequence n).belief who site) (fun history =>
        if ForcedState setup runtime leaks who history.1.state then (0 : ℝ) else 1) ≤ unforced)
    (decorrelated : BeliefDecorrelated ((targetSequence n).belief who site)
      (fun history => operationalRecord setup runtime leaks bounds horizon scheduler
        history.1.trace)
      (fun history => nativeDecodedState setup runtime leaks history.1.state) gamma)
    (option : LateOption bounds.candidateCount)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let target := targetSequence n
    let common := target.strategy
    let certificate := ((Menu).bounded (initialLaw setup) horizon
      scheduler).wellFoundedHistories
    let law := onePacketLate setup runtime leaks bounds horizon scheduler sequence scale
      positive
      le_one n ((N).agentAt site) option
    let installed := Profile.update (sig := (N).behavioralSignature) common who
      ((common who).withLaw site.1 law)
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who
    let error := (2 * payoffBound * (1 - slotRetention (scale n))) *
      (2 * horizon + 1) +
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
        (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * payoffBound) +
      2 * payoffBound * (scale n ^ 3 * (2 * horizon + 1))
    |expect (target.belief who site) (fun history =>
        expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff) -
      (excludedPayoff who +
        (1 - localFailure (2 * horizon + 1) target site
          {final | DecisionFailed (runtime := runtime) key final.state} law) *
          (siteValue setup runtime leaks bounds horizon scheduler parameter utility
            excludedPayoff
            target (setup.intendedOpeningProfile (sequence n).strategy) site - excludedPayoff
              who))| ≤
      error + 2 * payoffBound * unforced +
      4 * payoffBound * ((2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3) + unforced) +
      4 * payoffBound * gamma := by
  apply keyed_value_sub_le_of_pending setup runtime leaks bounds horizon
    scheduler covers
    capacity sequence scale positive le_one weights targetSequence assembled n site late debtFree
    siteKey atSite
    unforcedMass decorrelated option parameter utility excludedPayoff boundNonneg readoutBounded
    excludedBounded
    (2 * payoffBound * (1 - slotRetention (scale n))) (by
      have retention := slotRetention_le_one (positive n).le (le_one n)
      positivity)
  intro history forced
  exact OnePacketComparison.assembled_pending_value_affine setup runtime leaks bounds horizon
    scheduler wellFormed
    covers capacity sequence scale positive le_one weights targetSequence assembled n opportunity
    inclusion timely completes
    site (Or.inl late) debtFree siteKey pending atSite _ history forced (Or.inl ⟨option, rfl⟩)
    parameter utility excludedPayoff boundNonneg readoutBounded excludedBounded

open Classical in
/-- The original common posterior has a uniformly vanishing affine keyed-value error. -/
theorem assembled_keyed_value_bounds
    [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    [Finite setup.intendedProtocol.History]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup runtime leaks bounds horizon scheduler (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (slots_pos : 0 < bounds.candidateCount)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds (initialLaw setup)
      horizon scheduler bounds.candidateCount p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale
      positive le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (N) (targetSequence n)
      ((Menu).decisionRecall (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup runtime leaks).Control,
      (NP).Trace (some control) → control.execution.application.config.defaulted = ∅ →
        OpportunityAt runtime leaks control.execution delay)
    (inclusion : ∀ control : (application setup runtime leaks).Control,
      (NP).Trace (some control) → control.execution.application.config.defaulted = ∅ →
        ProtectedInclusionAt runtime leaks control.execution bound)
    (timely : runtime.AsyncTimely delay bound)
    (completes : ∀ control : (application setup runtime leaks).Control,
      (NP).Trace (some control) → control.execution.application.config.defaulted = ∅ →
        (application setup runtime leaks).terminal (some control) →
          control.execution.application.config.cut.Terminal)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (payoffBound : ℝ) (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound) :
    ∃ (failureScore : ℕ → LateKey setup runtime leaks → LateOption bounds.candidateCount → ℝ)
      (error : ℕ → ℝ), Tendsto error atTop (nhds 0) ∧
      (∀ n key option, 0 ≤ failureScore n key option ∧ failureScore n key option ≤ 1) ∧
      ∀ n who (site : (N).InformationSite who),
        ¬ Vegas.FreeAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) →
        ¬ Vegas.OwingAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) →
        ownedKeyed (Vegas.FreeAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler)
          (LateDeliveryAgent setup runtime leaks bounds (initialLaw setup) horizon
            scheduler)
          ((N).agentAt site) →
        ∀ key, lateKey setup runtime leaks who site.1 = some key → ∀ option,
        let target := targetSequence n
        let certificate := ((Menu).bounded (initialLaw setup) horizon
          scheduler).wellFoundedHistories
        let law := onePacketLate setup runtime leaks bounds horizon scheduler sequence scale
          positive
          le_one n ((N).agentAt site) option
        let installed := Profile.update (sig := (N).behavioralSignature) target.strategy who
          ((target.strategy who).withLaw site.1 law)
        let stopped := fun final : (NP).History => ¬ Clear final.state ∨
          DecodedState setup runtime leaks (failureProfile setup.program)
            (ProtocolState.OwesFailure who setup.program) final.state
        |expect (target.belief who site) (fun history =>
            expect ((N).runBehavioralUntil certificate installed stopped history.1)
              (fun final => if stopped final then excludedPayoff who else
                exclusionBase setup runtime parameter utility excludedPayoff leaks final.state
                  who)) -
          (excludedPayoff who + (1 - failureScore n key option) *
            (siteValue setup runtime leaks bounds horizon scheduler parameter utility
              excludedPayoff
              target (setup.intendedOpeningProfile (sequence n).strategy) site - excludedPayoff
                who))| ≤
          error n := by
  let inputs := OnePacketBaseInputs.ofSetup setup runtime leaks bounds horizon scheduler
          wellFormed independent
    observable
    sequence sourceMixed covers coversInputs capacity slots_pos
  have sameScale : scale = inputs.scale := funext scaleEq
  subst scale
  let target := targetSequence
  obtain ⟨unforced, unforcedLimit, unforcedBound⟩ := inputs.lateUnforced setup runtime leaks
    bounds horizon
    scheduler wellFormed
    weights
    target assembled mixed bayes
  obtain ⟨gamma, gammaLimit, decorrelated⟩ := inputs.lateDecorrelated setup runtime leaks bounds
    horizon
    scheduler wellFormed sourceMixed
    weights
    target assembled mixed bayes
  obtain ⟨score, scoreError, scoreLimit, scoreUnit, scoreNear⟩ :=
    keyed_failure_bounds_of_assembled setup runtime leaks bounds horizon scheduler
      wellFormed independent observable sequence sourceMixed inputs.scale positive le_one
      (fun _ => rfl) covers coversInputs capacity slots_pos
      weights
      target assembled mixed bayes
  let depth : ℝ := 2 * horizon + 1
  let path := fun n => depth * (inputs.scale n ^ 3 + inputs.scale n ^ 3)
  let row := fun n =>
    (2 * payoffBound * (1 * (1 - slotRetention (inputs.scale n)))) * depth +
    (2 * (inputs.scale n ^ 3 + path n) * depth + inputs.scale n ^ 3 * depth) * (2 * payoffBound) +
      2 * payoffBound * (inputs.scale n ^ 3 * depth)
  let error := fun n => row n + 2 * payoffBound * |unforced n| +
    4 * payoffBound * (path n + |unforced n|) + 4 * payoffBound * |gamma n| +
      2 * payoffBound * |scoreError n|
  have cube := inputs.scale_vanishing.pow 3
  have retention := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_slotRetention inputs.scale_vanishing)
  have pathLimit : Tendsto path atTop (nhds 0) := by
    simpa [path] using (cube.add cube).const_mul depth
  have rowLimit : Tendsto row atTop (nhds 0) := by
    have first := (retention.const_mul (2 * payoffBound * 1)).mul_const depth
    have second := ((((cube.add pathLimit).const_mul 2).mul_const depth).add
      (cube.mul_const depth)).mul_const (2 * payoffBound)
    have third := (cube.mul_const depth).const_mul (2 * payoffBound)
    simpa [row, mul_assoc] using (first.add second).add third
  refine ⟨score, error, ?_, scoreUnit, ?_⟩
  · simpa [error] using (((rowLimit.add (unforcedLimit.abs.const_mul (2 * payoffBound))).add
      ((pathLimit.add unforcedLimit.abs).const_mul (4 * payoffBound))).add
        (gammaLimit.abs.const_mul (4 * payoffBound))).add
          (scoreLimit.abs.const_mul (2 * payoffBound))
  intro n who site notFree notOwing keyed key siteKey option targetAt certificate law installed
    stopped
  obtain ⟨past, view, event, atSite, pending, _⟩ := id keyed.1
  have debtFree := siteDebtFree_of_not_owing setup runtime leaks bounds horizon scheduler
    notOwing
  have core := assembled_keyed_value_sub_le setup runtime leaks bounds horizon scheduler
    wellFormed covers capacity sequence inputs.scale positive le_one weights targetSequence
    assembled n opportunity inclusion timely completes site keyed.1 debtFree siteKey pending
    atSite ((unforcedBound n who site notFree notOwing keyed).trans (le_abs_self _))
    ((decorrelated n who site notFree notOwing keyed).mono (le_abs_self _)) option parameter utility
    excludedPayoff boundNonneg (readoutBounded who) (excludedBounded who)
  let failure := localFailure (2 * horizon + 1) targetAt site
    {final | DecisionFailed (runtime := runtime) key final.state} law
  let value := siteValue setup runtime leaks bounds horizon scheduler parameter utility
    excludedPayoff
    targetAt (setup.intendedOpeningProfile (sequence n).strategy) site
  have valueBound : |value - excludedPayoff who| ≤ 2 * payoffBound := by
    have valueBounded : |value| ≤ payoffBound := expect_abs_le_of_bounded boundNonneg
      (fun history => by
        unfold decodedPointValue
        split
        · exact excludedBounded who
        · split
          · exact excludedBounded who
          · split
            · exact expect_abs_le_of_bounded boundNonneg (readoutBounded who)
            · exact excludedBounded who)
    exact (abs_sub _ _).trans (by linarith [excludedBounded who])
  have scoreBound : |failure - score n key option| ≤ |scoreError n| :=
    (scoreNear n who site notFree notOwing keyed key siteKey option).trans (le_abs_self _)
  have gap : |(excludedPayoff who + (1 - failure) * (value - excludedPayoff who)) -
      (excludedPayoff who + (1 - score n key option) * (value - excludedPayoff who))| ≤
      2 * payoffBound * |scoreError n| := by
    have difference : (excludedPayoff who + (1 - failure) * (value - excludedPayoff who)) -
        (excludedPayoff who + (1 - score n key option) * (value - excludedPayoff who)) =
        (score n key option - failure) * (value - excludedPayoff who) := by ring
    rw [difference, abs_mul, abs_sub_comm]
    exact (mul_le_mul scoreBound valueBound (abs_nonneg _) (by positivity)).trans
      (le_of_eq (mul_comm _ _))
  have finalBound := (abs_sub_le
    (expect (targetAt.belief who site) (fun history =>
      expect ((N).runBehavioralUntil certificate installed stopped history.1)
        (fun final => if stopped final then excludedPayoff who else
          exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who)))
    (excludedPayoff who + (1 - failure) * (value - excludedPayoff who))
    (excludedPayoff who + (1 - score n key option) * (value - excludedPayoff who))).trans
      (add_le_add core gap)
  simpa [error, row, path, depth, failure, value, Nat.cast_add, Nat.cast_mul] using finalBound

end Vegas
