/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLocalCompletionValue
import Vegas.Game.OnePacketPendingPhaseValue
import Vegas.Game.OnePacketPendingFailure

/-! # Affine source continuation values at pending events -/

noncomputable section

namespace Vegas.OnePacketComparison

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)

local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon scheduler
local notation "Menu" => bounds.onePacketMenu runtime leaks
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks)
    (fun native : EventGraphRuntime.State (graph setup) =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config native) = ∅)

open Classical in
/-- The actual common continuation factors through the current event, with
uniform source-potential and physical completion errors. -/
theorem pending_value_affine_of_boundary_values
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
      positive le_one weights targetSequence) (n : ℕ)
    (terminalCompletes : ∀ (final : (application setup runtime leaks).Control),
      ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some final) →
      final.execution.application.config.defaulted = ∅ →
      (application setup runtime leaks).terminal (some final) →
      final.execution.application.config.cut.Terminal)
    {who : Player} (site : (N).InformationSite who)
    (pendingSite : LateDelivery setup runtime leaks who site.1 ∨ FirstActivation setup runtime
      leaks who site.1)
    (debtFree : SiteDebtFree setup runtime leaks bounds horizon scheduler site)
    {key : LateKey setup runtime leaks} (siteKey : lateKey setup runtime leaks who site.1 = some
      key)
    {event : (graph setup).EventId} (pending : pendingEvent setup runtime leaks who site.1 = some
      event)
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past, view))
    (law : PMF ((N).Choice who site.1))
    (history : (N).InformationHistory who site.1)
    (forced : ForcedState setup runtime leaks who history.1.state)
    (lawShape : (∃ option : LateOption bounds.candidateCount,
      law = onePacketLate setup runtime leaks bounds horizon scheduler sequence scale
        positive
        le_one n ((N).agentAt site) option) ∨
      law = PMF.pure (silenceChoice setup runtime leaks bounds (initialLaw setup) horizon
        scheduler
        who site.1))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound)
    (boundaryError : ℝ) (boundaryErrorNonneg : 0 ≤ boundaryError) :
    let common := (targetSequence n).strategy
    let certificate := ((Menu).bounded (initialLaw setup) horizon
      scheduler).wellFoundedHistories
    let installed := Profile.update (sig := (N).behavioralSignature) common who
      ((common who).withLaw site.1 law)
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who
    let failure := expect ((N).runBehavioralFrom installed (2 * horizon + 1) history.1)
      (fun final => if DecisionFailed (runtime := runtime) key final.state then (1 : ℝ) else 0)
    (∀ (nextRank : Nat) (start : (NP).History)
      (anchor : (application setup runtime leaks).Execution),
      start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩ →
      ReachedBoundary setup runtime leaks horizon scheduler nextRank anchor →
      ∀ point : ProtocolState setup.program,
      sourceServicePrefix? setup nextRank anchor.application.config = some point →
      ProtocolState.Intended setup.program point →
      let stopped := fun final : (NP).History => ¬ Clear final.state ∨
        DecodedState setup runtime leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure who setup.program) final.state
      |expect ((N).runBehavioralUntil certificate
          common stopped start)
          (fun final => if stopped final then excludedPayoff who else
            exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who) -
        sourcePointValue setup parameter utility excludedPayoff
          (setup.intendedOpeningProfile (sequence n).strategy) who point| ≤
        boundaryError *
          (application setup runtime leaks).rank horizon start.state) →
    |expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff -
      ((1 - failure) *
        decodedPointValue setup runtime leaks bounds horizon scheduler parameter utility
          excludedPayoff (setup.intendedOpeningProfile (sequence n).strategy) who
          (siteRank (runtime := runtime) site.1) history.1 +
        failure * excludedPayoff who)| ≤
      boundaryError *
        (2 * horizon + 1) +
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
        (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * payoffBound) +
      2 * payoffBound * (scale n ^ 3 * (2 * horizon + 1)) := by
  intro common certificate installed stopped payoff failure boundaryValues
  let phase := (N).runBehavioralUntil certificate installed
    (LateStopped setup runtime leaks bounds horizon scheduler (siteRank (runtime :=
      runtime) site.1)) history.1
  obtain ⟨remaining, execution, current, recallEq, observeEq, ordered⟩ :=
    ordered_of_site setup runtime leaks bounds horizon scheduler atSite history
  subst recallEq
  subst observeEq
  let menu := bounds.onePacketMenu runtime leaks
  have trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.1.trace
  have rawTrace := menu.toRawTrace (initialLaw setup) horizon scheduler trace
  have pendingAt := pending
  rw [atSite] at pendingAt
  obtain ⟨turn, readyView, owned, _⟩ := pendingEvent_spec (runtime := runtime) pendingAt
  have ready := (execution.application.publicView_eventReady event).mp readyView
  have siteKeyHere := siteKey
  rw [atSite] at siteKeyHere
  have decided := decidedEvent_eq_of_pending setup runtime leaks horizon scheduler pendingAt
    rawTrace rfl siteKeyHere
  obtain ⟨point, decoded, intendedPoint, _reachedPoint⟩ :=
    intendedReached_of_forced_debtFree (runtime := runtime) wellFormed site debtFree history
      current ordered forced
  have pointDecoded := (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have clear := defaulted_eq_empty_of_decodedIntended pointDecoded
    intendedPoint
  have phaseEq := pending_until_eq_clearUntil (runtime := runtime) certificate
    installed history.1
    current ordered clear event
    ready
  have tail := OnePacketComparison.local_completion_value_sub_le_of_boundary_values setup runtime
    leaks bounds horizon scheduler (sequence n) common terminalCompletes certificate
    who site.1 law history.1 current history.2 event ready owned key decided ordered point decoded
    intendedPoint parameter utility excludedPayoff boundNonneg readoutBounded excludedBounded
    boundaryError boundaryErrorNonneg
    boundaryValues
  dsimp only at tail
  have freshEq : siteFresh (runtime := runtime) who site.1 = fun control : (application setup
    runtime leaks).Control =>
      ¬ StoreEventFailed control.execution.application.config.store event := by
    funext control
    simp only [siteFresh, pending]
  rw [← freshEq, ← phaseEq] at tail
  have physical := pending_phase_value_bounds (runtime := runtime) parameter utility
    excludedPayoff terminalCompletes
    wellFormed sequence scale
    positive le_one weights targetSequence assembled n covers (by have := capacity who; omega)
    le_rfl site pendingSite
    debtFree siteKey pending atSite law history forced lawShape readoutBounded excludedBounded
  dsimp only at physical
  change |expect phase _ -
      ((1 - expect phase (fun final => if DecisionFailed (runtime := runtime) key final.state then
        (1 : ℝ) else 0)) *
        decodedPointValue setup runtime leaks bounds horizon scheduler parameter utility
          excludedPayoff (setup.intendedOpeningProfile (sequence n).strategy) who
          (siteRank (runtime := runtime) site.1) history.1 +
        expect phase (fun final => if DecisionFailed (runtime := runtime) key final.state then (1
          : ℝ) else 0) *
          excludedPayoff who)| ≤ _ ∧ expect phase _ ≤ _ at physical
  change |expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff -
      expect phase _| ≤ _ + 2 * payoffBound * expect phase _ at tail
  have smallBad := mul_le_mul_of_nonneg_left physical.2
    (by positivity : 0 ≤ 2 * payoffBound)
  have failureEq := pending_failure_run_eq_phase (runtime := runtime) terminalCompletes
    certificate installed history.1
    current ordered clear key
    event ready decided
  dsimp only [failure]
  rw [failureEq]
  exact (abs_sub_le _ _ _).trans ((add_le_add tail physical.1).trans (by linarith))


open Classical in
/-- The actual common continuation factors through the current event, with
uniform source-potential and physical completion errors. -/
theorem assembled_pending_value_affine
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
      positive le_one weights targetSequence) (n : ℕ)
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
    {who : Player} (site : (N).InformationSite who)
    (pendingSite : LateDelivery setup runtime leaks who site.1 ∨ FirstActivation setup runtime
      leaks who site.1)
    (debtFree : SiteDebtFree setup runtime leaks bounds horizon scheduler site)
    {key : LateKey setup runtime leaks} (siteKey : lateKey setup runtime leaks who site.1 = some
      key)
    {event : (graph setup).EventId} (pending : pendingEvent setup runtime leaks who site.1 = some
      event)
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past, view))
    (law : PMF ((N).Choice who site.1))
    (history : (N).InformationHistory who site.1)
    (forced : ForcedState setup runtime leaks who history.1.state)
    (lawShape : (∃ option : LateOption bounds.candidateCount,
      law = onePacketLate setup runtime leaks bounds horizon scheduler sequence scale
        positive
        le_one n ((N).agentAt site) option) ∨
      law = PMF.pure (silenceChoice setup runtime leaks bounds (initialLaw setup) horizon
        scheduler
        who site.1))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let common := (targetSequence n).strategy
    let certificate := ((Menu).bounded (initialLaw setup) horizon
      scheduler).wellFoundedHistories
    let installed := Profile.update (sig := (N).behavioralSignature) common who
      ((common who).withLaw site.1 law)
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who
    let failure := expect ((N).runBehavioralFrom installed (2 * horizon + 1) history.1)
      (fun final => if DecisionFailed (runtime := runtime) key final.state then (1 : ℝ) else 0)
    |expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff -
      ((1 - failure) *
        decodedPointValue setup runtime leaks bounds horizon scheduler parameter utility
          excludedPayoff (setup.intendedOpeningProfile (sequence n).strategy) who
          (siteRank (runtime := runtime) site.1) history.1 +
        failure * excludedPayoff who)| ≤
      (2 * payoffBound * (1 - slotRetention (scale n))) *
        (2 * horizon + 1) +
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
        (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * payoffBound) +
      2 * payoffBound * (scale n ^ 3 * (2 * horizon + 1)) := by
  intro common certificate installed stopped payoff failure
  apply pending_value_affine_of_boundary_values setup runtime leaks bounds horizon scheduler
    wellFormed covers capacity sequence scale positive le_one weights targetSequence assembled n
    completes
    site pendingSite debtFree siteKey pending atSite law history forced lawShape parameter utility
    excludedPayoff boundNonneg readoutBounded excludedBounded
    (2 * payoffBound * (1 - slotRetention (scale n))) (by
      have retention := slotRetention_le_one (positive n).le (le_one n)
      positivity)
  intro nextRank start anchor state boundary target atRank targetIntended
  have baseBounded : ∀ final : (NP).History,
      |exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who| ≤
        payoffBound := by
    intro final
    cases final.state with
    | none => simpa only [exclusionBase, abs_zero] using boundNonneg
    | some control =>
        change |if who ∈ control.execution.application.config.defaulted then excludedPayoff who
          else exclusionReadoutUtility setup parameter utility excludedPayoff
            (sourceReadout setup runtime leaks (some control)) who| ≤ payoffBound
        split
        · exact excludedBounded
        · exact readoutBounded _
  exact assembled_stopped_boundary_value_sub_le setup runtime leaks bounds horizon scheduler
    wellFormed covers capacity sequence scale positive le_one weights targetSequence assembled n
    opportunity inclusion timely completes certificate nextRank start anchor state boundary target
    atRank targetIntended parameter utility excludedPayoff who boundNonneg baseBounded
    excludedBounded

end Vegas.OnePacketComparison
