module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketLocalCompletionValue
public import Vegas.Game.OnePacketPendingPhaseValue
public import Vegas.Game.OnePacketFirstActivationValue
public import Vegas.Game.OnePacketValueTransport
public import Vegas.Game.OnePacketOwnIntended
public import Vegas.Game.OnePacketPrescribedSites
public import Vegas.Game.OnePacketRecordedSilence

@[expose] public section

/-! # The gain from silence at a fresh native decision -/

noncomputable section

namespace Vegas.OnePacketComparison

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

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
/-- Waiting at a fresh debt-free source decision has vanishing gain under
one assembled native assessment sequence. -/
theorem assembled_silence_history_comparison
    [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p,
      PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup) horizon scheduler
        bounds.candidateCount p))
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
    (event : (graph setup).EventId)
    (pending : pendingEvent setup timeouts leaks who site.1 = some event)
    (silent : choice.1 = some ⟨none⟩)
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} (atSite : site.1 = some (past, view))
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
    ∀ history : (N).InformationHistory who site.1,
      RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
        history.1.trace →
      expect ((N).runBehavioralUntil certificate
          (Profile.update (sig := (N).behavioralSignature) common who
            ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
        expect ((N).runBehavioralUntil certificate common stopped history.1) payoff ≤
      2 * ((2 * payoffBound * (1 - slotRetention (scale n))) *
        (2 * horizon + 1)) + 2 * payoffBound * (1 - slotRetention (scale n)) +
      2 * payoffBound * (scale n ^ 3 * (2 * horizon + 1)) +
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
        (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * payoffBound) := by
  intro common certificate stopped payoff history regular
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
  obtain ⟨remaining, execution, point, current, actualAt, never, ordered, decoded, intended,
    reached⟩ := firstActivation_history_facts setup timeouts leaks bounds horizon scheduler
      wellFormed site pending nonlate history stateForced allDebtFree
  let key := LateKey.ofView setup timeouts leaks who (execution.logs who)
    (execution.observe (application setup timeouts leaks) who)
  have siteKey : lateKey setup timeouts leaks who site.1 = some key := by
    rw [actualAt]
    exact lateKey_some (timeouts := timeouts) who (execution.logs who)
      (execution.observe (application setup timeouts leaks) who)
  have pendingHere := pending
  rw [actualAt] at pendingHere
  obtain ⟨turn, readyPublic, owned, _unrecorded⟩ := pendingEvent_spec (timeouts := timeouts)
    pendingHere
  have ready := (execution.application.publicView_eventReady event).mp readyPublic
  have decodedPoint := (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have clear := defaulted_eq_empty_of_decodedIntended
    decodedPoint intended
  have decided := decidedEvent_eq_of_pending setup timeouts leaks horizon scheduler
    pendingHere
    ((Menu).toRawTrace (initialLaw setup) horizon scheduler (current ▸ history.1.trace)) rfl
    (lateKey_some (timeouts := timeouts) who (execution.logs who)
      (execution.observe (application setup timeouts leaks) who))
  have choiceEq : choice = silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler who site.1 := by
    apply Subtype.ext
    rw [silenceChoice_val (timeouts := timeouts) who site.1 (by rw [actualAt]; rfl)]
    exact silent
  let installed := Profile.update (sig := (N).behavioralSignature) common who
    ((common who).withLaw site.1 (PMF.pure choice))
  let phase := (N).runBehavioralUntil certificate installed
    (LateStopped setup timeouts leaks bounds horizon scheduler (siteRank (timeouts :=
      timeouts) site.1)) history.1
  have first : FirstActivation setup timeouts leaks who site.1 :=
    ⟨_, _, event, actualAt, pending, never⟩
  have physical := pending_phase_value_bounds (timeouts := timeouts) parameter utility
    excludedPayoff completes
    wellFormed sequence scale
    positive le_one weights targetSequence assembled n covers (by have := capacity who; omega)
    le_rfl site
    (Or.inr first)
    debtFree siteKey pending actualAt (PMF.pure choice) history stateForced
    (Or.inr (congrArg PMF.pure choiceEq)) readoutBounded excludedBounded
  dsimp only at physical
  change |expect phase _ -
      ((1 - expect phase (fun final => if DecisionFailed (timeouts := timeouts) key final.state then
        (1 : ℝ) else 0)) *
        decodedPointValue setup timeouts leaks bounds horizon scheduler parameter utility
          excludedPayoff (setup.intendedOpeningProfile (sequence n).strategy) who
          (siteRank (timeouts := timeouts) site.1) history.1 +
        expect phase (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1
          : ℝ) else 0) *
          excludedPayoff who)| ≤ _ ∧ expect phase _ ≤ _ at physical
  have pointValue : decodedPointValue setup timeouts leaks bounds horizon scheduler parameter
      utility excludedPayoff (setup.intendedOpeningProfile (sequence n).strategy) who
      (siteRank (timeouts := timeouts) site.1) history.1 = sourcePointValue setup parameter utility
        excludedPayoff
        (setup.intendedOpeningProfile (sequence n).strategy) who point := by
    simp only [decodedPointValue, current, decoded, reached, ↓reduceIte]
  rw [pointValue] at physical
  have lower : excludedPayoff who ≤ sourcePointValue setup parameter utility excludedPayoff
      (setup.intendedOpeningProfile (sequence n).strategy) who point :=
    (sourcePointValue_mem_Icc setup parameter utility excludedPayoff
      (setup.intendedOpeningProfile (sequence n).strategy) who upper le_upper
      (fun target reachable => excludedPayoff_le_of_reached setup parameter utility excludedPayoff
        wellFormed below (sequence n).strategy target reachable who) point reached).1
  have probabilityNonneg : 0 ≤ expect phase
      (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1 : ℝ) else 0) :=
        by
    apply expect_nonneg
    intro final _
    split <;> norm_num
  have phaseEq := pending_until_eq_clearUntil (timeouts := timeouts) certificate installed
    history.1 current
    ordered clear event
    ready
  have tail := assembled_local_completion_value_sub_le setup timeouts
    leaks bounds
    horizon scheduler
    wellFormed covers capacity sequence scale positive le_one weights targetSequence assembled n
    opportunity inclusion timely
    completes certificate who site.1 (PMF.pure choice) history.1 current history.2 event ready owned
    key decided ordered point decoded intended parameter utility excludedPayoff boundNonneg
    readoutBounded excludedBounded
  dsimp only at tail
  have freshEq : siteFresh (timeouts := timeouts) who site.1 = fun control : (application setup
    timeouts leaks).Control =>
      ¬ StoreEventFailed control.execution.application.config.store event := by
    funext control
    simp only [siteFresh, pending]
  rw [← freshEq, ← phaseEq] at tail
  have baseline := OnePacketComparison.assembled_firstActivation_value_lower setup timeouts
    leaks bounds horizon
    scheduler wellFormed covers capacity sequence scale positive le_one weights targetSequence
    assembled n opportunity
    inclusion timely completes certificate history.1 current clear event pendingHere never ordered
    decoded intended parameter utility excludedPayoff boundNonneg readoutBounded excludedBounded
  dsimp only at baseline
  change sourcePointValue setup parameter utility excludedPayoff
      (setup.intendedOpeningProfile (sequence n).strategy) who point -
      expect ((N).runBehavioralUntil certificate common stopped history.1) payoff ≤ _ at baseline
  change |expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff -
      expect phase _| ≤ _ + 2 * payoffBound * expect phase _ at tail
  have smallBad := mul_le_mul_of_nonneg_left physical.2
    (by positivity : 0 ≤ 2 * payoffBound)
  have affineUpper := (abs_le.mp physical.1).2
  have tailUpper := (abs_le.mp tail).2
  nlinarith [mul_nonneg probabilityNonneg (sub_nonneg.mpr lower)]


end Vegas.OnePacketComparison
