/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySourcePhaseValue
import Vegas.Game.RecoveryLateSourcePhase
import Vegas.Game.RecoveryEventPhaseLaw
import Vegas.Game.RecoveryFirstActivationValue
import Vegas.Game.IntendedChoiceReach
import Vegas.Game.OnePacketNonLateValueBlind

/-! # Unintended nonlate commitments have exclusion value -/

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
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native ∅))

open Classical in
/-- A non-intended first-callback commitment is worth exactly exclusion on
regular histories, so its gain is bounded by honest retention error. -/
theorem nativeComparison_unintendedCommitment_history_comparison [Fintype (RP).History]
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
    (unintendedChoice :
      ¬ IntendedCommitment setup leaks bounds horizon (NativeScheduler) site choice)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (response : (application setup leaks).Action) (selected : choice.1 = some response)
    (material : (application setup leaks).Submission)
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
    let common := nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale
      positive le_one weights n
    let certificate := ((Menu).bounded (initialLaw setup) horizon
      (NativeScheduler)).wellFoundedHistories
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup parameter utility excludedPayoff leaks final.state who
    ∀ history : (N).InformationHistory who site.1,
      RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) who history.1.trace →
      expect ((N).runBehavioralUntil certificate
          (Profile.update (sig := (N).behavioralSignature) common who
            ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
        expect ((N).runBehavioralUntil certificate common stopped history.1) payoff ≤
      (2 * payoffBound * (Fintype.card Player * (1 - slotRetention (scale n)))) *
        (2 * horizon + 1) + 2 * payoffBound * (1 - slotRetention (scale n)) := by
  intro common certificate stopped payoff history regular
  have forced := forcedAgent_of_not_free setup leaks bounds horizon (NativeScheduler) notFree
  have debtFree := siteDebtFree_of_not_owing setup leaks bounds horizon (NativeScheduler) notOwing
  have ownIntended := ownCompletionsIntended_of_siteNotOwes wellFormed debtFree history
  have allDebtFree := not_owesFailure_of_regular wellFormed (sequence n) atSite forced history
    regular ownIntended
  have stateForced := forcedState_of_regular wellFormed (sequence n) atSite forced history regular
    ownIntended
  have member : response ∈ bounds.onePacketActions (runtime setup) leaks who past view := by
    obtain ⟨other, otherChosen, offered⟩ := choice_response setup leaks bounds horizon
      (NativeScheduler) site atSite choice
    have same := Option.some.inj (selected.symm.trans otherChosen)
    subst other
    exact offered
  obtain ⟨candidateOwner, ⟨serial, candidateSlot⟩, payload, outputEq, codeEq, _⟩ :=
    onePacket_commitment_facts bounds member sends packet
  have candidateEq : candidate = (who, .prepared serial) := Prod.ext candidateOwner candidateSlot
  subst candidateEq
  have submitted : (runtime setup).submittedEvent? leaks response = some event := by
    unfold EventGraphRuntime.submittedEvent?
    simp only [sends, packet, Payload.event?]
  obtain ⟨otherPast, otherView, otherResponse, otherEvent, otherAt, otherChosen, otherSubmitted,
    turn⟩ := atTurn
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (atSite.symm.trans otherAt))
  have sameResponse := Option.some.inj (selected.symm.trans otherChosen)
  subst otherResponse
  have sameEvent := Option.some.inj (submitted.symm.trans otherSubmitted)
  subst otherEvent
  have pending := pendingEvent_of_turnSubmission setup leaks bounds horizon (NativeScheduler) site
    atSite turn choice selected submitted
  obtain ⟨remaining, execution, point, current, actualAt, never, ordered, decoded, intended,
    reached⟩ := firstActivation_history_facts setup leaks bounds horizon (NativeScheduler)
      wellFormed site pending nonlate history stateForced allDebtFree
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (atSite.symm.trans actualAt))
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have pointDecoded := (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have clear := publicExclusionRecord_of_decodedIntended
    ((Menu).toRawTrace (initialLaw setup) horizon (NativeScheduler) (current ▸ history.1.trace))
    pointDecoded intended
  have afterLookup : ∀ slot, (execution.respond (application setup leaks) who
      response).application.candidates.lookup (who, slot) =
      material.call.candidateAfter who
        (execution.observe (application setup leaks) who).application.candidates slot := by
    intro slot
    rcases response with ⟨transmission⟩
    change transmission = some material at sends
    subst sends
    exact material.call.candidateAfter_eq who execution.application slot
  have fixed : (execution.respond (application setup leaks) who
      response).application.candidates.lookup (who, .prepared serial) ≠ .fresh := by
    rw [afterLookup]
    unfold Submission.candidateAfter
    rw [packet]
    simp only [and_self, ↓reduceIte]
    split
    · split <;> simp
    · assumption
  have projected : projectView setup leaks who site.1 =
      some (ProtocolState.observe who setup.program point) := by
    rw [actualAt]
    exact projectView_observe setup leaks who execution (siteRank site.1) ordered point decoded _
  have acting := (decodedPoint_actor who ready pointDecoded).trans
    (PublicView.ownTurn?_spec _ who event turn).2
  have unintended : ∀ value act,
      (execution.respond (application setup leaks) who response).application.candidates.lookup
        (who, .prepared serial) = .openable ⟨payload, value⟩ →
      decodeEventAction setup.program event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (PublicationResult.success value)) = some act →
      act ∉ ProtocolView.intendedAvailable who setup.program
        (ProtocolState.observe who setup.program point) := by
    intro value act opened decodedAct actMember
    apply unintendedChoice
    refine ⟨_, _, response, material, event, serial, payload, outputEq, value, actualAt, selected,
      sends, packet, (afterLookup _).symm.trans opened, ?_⟩
    rw [projected]
    change ProtocolView.intendedMenu who setup.program _ (sourceOfValue setup event outputEq value)
    unfold sourceOfValue
    rw [decodedAct]
    exact ⟨acting, actMember⟩
  let installed := Profile.update (sig := (N).behavioralSignature) common who
    ((common who).withLaw site.1 (PMF.pure choice))
  have running : ¬ (NP).terminal history.1.state := by
    rw [current]
    rintro ⟨_, impossible⟩
    cases impossible
  have going : ¬ LateStopped setup leaks bounds horizon (NativeScheduler) (siteRank site.1)
      history.1 := by
    rintro ⟨other, state, nextPrefix⟩
    rw [current] at state
    cases Option.some.inj state
    have := isPrefix_unique nextPrefix ordered
    omega
  have oneStep : ((N).runBehavioralFrom installed 1 history.1).map History.state =
      PMF.pure (some ⟨remaining, none,
        execution.respond (application setup leaks) who response⟩) := by
    rw [(Menu).run_one_response (initialLaw setup) horizon (NativeScheduler) installed history.1 who
      remaining execution current]
    dsimp only [installed]
    simp only [ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
      ReactiveApplication.ResponseMenu.embedPolicy, Profile.update_same, PMF.map_comp]
    rw [← actualAt, BehavioralPolicy.withLaw_self, PMF.pure_map]
    change PMF.pure (some (⟨remaining, none, execution.respond (application setup leaks) who
      (choice.1.getD (⟨none⟩ : (application setup leaks).Action))⟩ :
        (application setup leaks).Control)) = _
    rw [selected, Option.getD_some]
  have phaseOwed : ∀ final ∈ ((N).runBehavioralUntil certificate installed
      (LateStopped setup leaks bounds horizon (NativeScheduler) (siteRank site.1))
      history.1).support,
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state := by
    intro final member
    rw [(N).runBehavioralUntil_of_running certificate installed going running,
      PMF.mem_support_bind_iff] at member
    obtain ⟨middle, stepped, rest⟩ := member
    have middleState : middle.state =
        some ⟨remaining, none, execution.respond (application setup leaks) who response⟩ := by
      have mem : middle.state ∈ (((N).runBehavioralFrom installed 1 history.1).map
          History.state).support := (PMF.mem_support_map_iff _ _ _).mpr ⟨middle, stepped, rfl⟩
      rw [oneStep, PMF.mem_support_pure_iff] at mem
      exact mem
    exact recovery_unintendedCommitment_phase_owes (initialLaw_initialized setup)
      (initialLaw_native setup) completes (failureProfile setup.program) turn outputEq codeEq
      pointDecoded intended ordered response material sends packet fixed unintended certificate
      installed middle middleState final rest
  have phaseEq := recovery_pending_until_eq_clearUntil (initialLaw_initialized setup)
    (initialLaw_native setup) completes certificate installed history.1 current ordered clear event
    ready
  have payoffBounded : ∀ final, |payoff final| ≤ payoffBound := by
    intro final
    dsimp only [payoff]
    split
    · exact excludedBounded
    · rw [exclusionBase_eq_readout]
      exact readoutBounded _
  have valueEq : expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff =
      excludedPayoff who := by
    rw [debtStopped_eq_bind_eventPhase certificate installed who history.1 _ current ordered point
      decoded intended, expect_bind_tower_bounded _ _ _ payoffBounded]
    have constant : ∀ final ∈ ((N).runBehavioralUntil certificate installed
        (fun final => LateStopped setup leaks bounds horizon (NativeScheduler) (siteRank site.1)
          final ∨ ¬ Clear final.state) history.1).support,
        expect ((N).runBehavioralUntil certificate installed stopped final) payoff =
          excludedPayoff who := by
      intro final member
      have owed := phaseOwed final (phaseEq.symm ▸ member)
      have halt : stopped final := Or.inr owed
      rw [(N).runBehavioralUntil_of_stopped certificate installed halt, expect_pure]
      exact ite_eq_left halt
    exact (expect_congr_on_support constant).trans (expect_constant _ _)
  have lower := (sourcePointValue_mem_Icc setup parameter utility excludedPayoff
    (setup.intendedOpeningProfile (sequence n).strategy) who upper le_upper
    (fun target reachable => excludedPayoff_le_of_reached setup parameter utility excludedPayoff
      wellFormed below (sequence n).strategy target reachable who) point reached).1
  have baseline := nativeComparison_firstActivation_value_lower setup leaks bounds horizon
    scheduler wellFormed covers capacity sequence scale positive le_one weights n opportunity
    inclusion timely completes certificate history.1 current clear event (by rwa [← actualAt])
    never ordered decoded intended parameter utility excludedPayoff boundNonneg readoutBounded
    excludedBounded
  dsimp only at baseline
  change sourcePointValue setup parameter utility excludedPayoff
      (setup.intendedOpeningProfile (sequence n).strategy) who point -
      expect ((N).runBehavioralUntil certificate common stopped history.1) payoff ≤ _ at baseline
  rw [valueEq]
  linarith

end Vegas.RecoveryOnePacket
