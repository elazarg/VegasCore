/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketFirstActivationValue
import Vegas.Game.OnePacketPhasePotential
import Vegas.Game.OnePacketLocalCompletionValue
import Vegas.Game.OnePacketEventPhaseLaw
import Vegas.Game.OnePacketValueTransport

/-! # Source incentive comparison for a fresh disclosure -/

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
/-- An arbitrary current disclosure response gains only the vanishing common
continuation error at a fresh source decision. -/
theorem assembled_firstActivation_disclosure_gain_le
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
    {who : Player} (site : (N).InformationSite who)
    (law : PMF ((N).Choice who site.1))
    (history : (N).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup timeouts leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (atSite : site.1 = some (execution.logs who,
      execution.observe (application setup timeouts leaks) who))
    (event : (graph setup).EventId)
    (pending : pendingEvent setup timeouts leaks who site.1 = some event)
    (never : ∀ entry ∈ execution.logs who, ¬ ActivatedAt setup timeouts leaks who event entry)
    (key : LateKey setup timeouts leaks) (decided : decidedEvent (timeouts := timeouts) key = some
      event)
    {payload : L.Ty} {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks)
    (ordered : execution.application.config.cut.IsPrefix (siteRank (timeouts := timeouts) site.1))
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup (siteRank (timeouts := timeouts) site.1)
      execution.application.config =
      some point)
    (intended : ProtocolState.Intended setup.program point) (reached : IntendedReached setup point)
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
    expect ((N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature) common who
          ((common who).withLaw site.1 law)) stopped history.1) payoff -
      expect ((N).runBehavioralUntil certificate common stopped history.1) payoff ≤
      2 * ((2 * payoffBound * (1 - slotRetention (scale n))) *
        (2 * horizon + 1)) + 2 * payoffBound * (1 - slotRetention (scale n)) := by
  intro common certificate stopped payoff
  let installed := Profile.update (sig := (N).behavioralSignature) common who
    ((common who).withLaw site.1 law)
  let phase := (N).runBehavioralUntil certificate installed
    (LateStopped setup timeouts leaks bounds horizon scheduler (siteRank (timeouts :=
      timeouts) site.1)) history.1
  let profile := setup.intendedOpeningProfile (sequence n).strategy
  have pendingHere := pending
  rw [atSite] at pendingHere
  obtain ⟨turn, readyPublic, _owned, _unrecorded⟩ := pendingEvent_spec (timeouts := timeouts)
    pendingHere
  have ready := (execution.application.publicView_eventReady event).mp readyPublic
  have owned := nodeView_resolve_actor outputEq codeEq
  have pointDecoded := (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have clear := defaulted_eq_empty_of_decodedIntended
    pointDecoded intended
  have phaseEq := pending_until_eq_clearUntil (timeouts := timeouts) certificate installed
    history.1 current
    ordered clear event
    ready
  have physical := disclosure_sourceValue setup timeouts leaks bounds horizon scheduler
    completes
    (sequence n)
    (targetSequence n) site pending law history current turn ordered outputEq codeEq decoded
    intended decided parameter utility excludedPayoff readoutBounded
  dsimp only at physical
  change expect phase _ =
    (1 - expect phase (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1
      : ℝ) else 0)) *
      sourcePointValue setup parameter utility excludedPayoff profile who point +
      expect phase (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1 :
        ℝ) else 0) *
        excludedPayoff who at physical
  obtain ⟨target, _step, _intended, supports⟩ := disclosure_sourceKernel (timeouts := timeouts)
    (sequence n) (targetSequence n) site pending law history current turn ordered outputEq codeEq
    decoded intended (fun final trace ended same => by
      have finalDecoded : decodedPoint setup final.execution.application.config = some point := by
        rw [same]
        exact pointDecoded
      have finalClear := defaulted_eq_empty_of_decodedIntended finalDecoded intended
      rw [completes final trace finalClear ended]
      exact Finset.mem_univ _)
  have noBad : expect phase (lateBadStop setup timeouts leaks bounds horizon scheduler
      (siteRank (timeouts := timeouts) site.1) (siteFresh (timeouts := timeouts) who site.1)
        event) =
        0 := by
    calc
      _ = expect phase (fun _ => (0 : ℝ)) := by
        apply expect_congr_on_support
        intro final member
        obtain ⟨control, state, alternatives⟩ := supports final member
        unfold lateBadStop
        split_ifs with bad
        · obtain ⟨⟨other, otherState, _completed, notFailed⟩, absent⟩ := bad
          rw [state] at otherState
          cases Option.some.inj otherState
          rcases alternatives with somePoint | ⟨_none, failed⟩
          · rw [somePoint] at absent
            cases absent
          · exact (notFailed failed).elim
        · rfl
      _ = 0 := expect_constant _ _
  have tail := assembled_local_completion_value_sub_le setup timeouts
    leaks bounds
    horizon scheduler
    wellFormed covers capacity sequence scale positive le_one weights targetSequence assembled n
    opportunity inclusion timely
    completes certificate who site.1 law history.1 current history.2 event ready owned key decided
    ordered point decoded intended parameter utility excludedPayoff boundNonneg readoutBounded
    excludedBounded
  dsimp only at tail
  have freshEq : siteFresh (timeouts := timeouts) who site.1 = fun control : (application setup
    timeouts leaks).Control =>
      ¬ StoreEventFailed control.execution.application.config.store event := by
    funext control
    simp only [siteFresh, pending]
  rw [← freshEq, ← phaseEq, noBad, mul_zero, add_zero] at tail
  change |expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff -
      expect phase _| ≤ _ at tail
  have lower := (sourcePointValue_mem_Icc setup parameter utility excludedPayoff profile who
    upper le_upper (fun target reachable => excludedPayoff_le_of_reached setup parameter utility
      excludedPayoff wellFormed below (sequence n).strategy target reachable who) point reached).1
  have probabilityNonneg : 0 ≤ expect phase
      (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1 : ℝ) else 0) :=
        by
    apply expect_nonneg
    intro final _
    split <;> norm_num
  have baseline := OnePacketComparison.assembled_firstActivation_value_lower setup timeouts
    leaks bounds horizon
    scheduler wellFormed covers capacity sequence scale positive le_one weights targetSequence
    assembled n opportunity
    inclusion timely completes certificate history.1 current clear event pendingHere never ordered
    decoded intended parameter utility excludedPayoff boundNonneg readoutBounded excludedBounded
  dsimp only at baseline
  change sourcePointValue setup parameter utility excludedPayoff profile who point -
      expect ((N).runBehavioralUntil certificate common stopped history.1) payoff ≤ _ at baseline
  have upperTail := (abs_le.mp tail).2
  rw [physical] at upperTail
  nlinarith [mul_nonneg probabilityNonneg (sub_nonneg.mpr lower)]

end Vegas.OnePacketComparison
