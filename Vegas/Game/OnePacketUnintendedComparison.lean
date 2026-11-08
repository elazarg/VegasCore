/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketFirstActivationValue
import Vegas.Game.OnePacketOwnIntended
import Vegas.Game.OnePacketPrescribedSites
import Vegas.Game.OnePacketValueTransport
import Vegas.Game.OnePacketUnintendedValue

/-! # Unintended nonlate commitments have exclusion value -/

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
/-- An unintended first-callback commitment has exclusion value on regular
histories, so its gain is bounded by the common honest-retention error. -/
theorem assembled_unintendedCommitment_history_comparison
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
    (unintendedChoice :
      ¬ IntendedCommitment setup timeouts leaks bounds horizon scheduler site choice)
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} (atSite : site.1 = some (past, view))
    (response : (application setup timeouts leaks).Action) (selected : choice.1 = some response)
    (material : (application setup timeouts leaks).Submission)
    (sends : response.transmission = some material)
    (event : (graph setup).EventId) (candidate : Handle (graph setup))
    (packet : material.call.packet = .commitment event candidate)
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
      (2 * payoffBound * (1 - slotRetention (scale n))) *
        (2 * horizon + 1) + 2 * payoffBound * (1 - slotRetention (scale n)) := by
  intro common certificate stopped payoff history regular
  have forced := forcedAgent_of_not_free setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler notFree
  have debtFree := siteDebtFree_of_not_owing setup timeouts leaks bounds horizon scheduler notOwing
  have ownIntended := ownCompletionsIntended_of_siteNotOwes (timeouts := timeouts) wellFormed
    debtFree history
  have allDebtFree := not_owesFailure_of_regular (timeouts := timeouts) wellFormed (sequence n)
    atSite forced history regular ownIntended
  have stateForced := forcedState_of_regular (timeouts := timeouts) wellFormed (sequence n) atSite
    forced history regular ownIntended
  have valueEq := unintendedCommitment_stopped_value setup timeouts leaks bounds horizon scheduler
    wellFormed completes common site choice notOwing atTurn unintendedChoice atSite response
    selected material sends event candidate packet parameter utility excludedPayoff readoutBounded
    excludedBounded history stateForced
  have submitted : (submittedEvent? timeouts) leaks response = some event := by
    unfold EventGraphRuntime.submittedEvent?
    simp only [sends, packet, Payload.event?]
  obtain ⟨otherPast, otherView, otherResponse, otherEvent, otherAt, otherChosen, otherSubmitted,
    turn⟩ := atTurn
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (atSite.symm.trans otherAt))
  have sameResponse := Option.some.inj (selected.symm.trans otherChosen)
  subst otherResponse
  have sameEvent := Option.some.inj (submitted.symm.trans otherSubmitted)
  subst otherEvent
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
    reached⟩ := firstActivation_history_facts setup timeouts leaks bounds horizon scheduler
      wellFormed site pending nonlate history stateForced allDebtFree
  have pointDecoded := (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have clear := defaulted_eq_empty_of_decodedIntended pointDecoded intended
  have lower := (sourcePointValue_mem_Icc setup parameter utility excludedPayoff
    (setup.intendedOpeningProfile (sequence n).strategy) who upper le_upper
    (fun target reachable => excludedPayoff_le_of_reached setup parameter utility excludedPayoff
      wellFormed below (sequence n).strategy target reachable who) point reached).1
  have baseline := assembled_firstActivation_value_lower setup timeouts leaks bounds horizon
    scheduler wellFormed covers capacity sequence scale positive le_one weights targetSequence
    assembled n opportunity inclusion timely completes certificate history.1 current clear event
    (by rwa [← actualAt]) never ordered decoded intended parameter utility excludedPayoff
    boundNonneg readoutBounded excludedBounded
  dsimp only at baseline valueEq
  change sourcePointValue setup parameter utility excludedPayoff
      (setup.intendedOpeningProfile (sequence n).strategy) who point -
      expect ((N).runBehavioralUntil certificate common stopped history.1) payoff ≤ _ at baseline
  rw [valueEq]
  linarith

end Vegas.OnePacketComparison
