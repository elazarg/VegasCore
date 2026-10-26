/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryPhaseValueBlind
import Vegas.Game.RecoverySourcePhaseValue


/-! # Exclusion value of an unintended current commitment -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication runtime leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler runtime leaks scheduler
local notation "R" => model setup runtime leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) Initial horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon (NativeScheduler)
local notation "Menu" => bounds.onePacketMenu runtime leaks
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk
    native
    ∅))


open Classical in
theorem unintendedCommitment_stopped_value
    [(application setup runtime leaks).FiniteNature (initialLaw setup) NativeScheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed)
    (terminalCompletes : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).Trace (some
        control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      (application setup runtime leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (common : ∀ player, (N).BehavioralPolicy player)
    {who : Player} (site : (N).InformationSite who) (choice : (N).Choice who site.1)
    (notOwing : ¬ Vegas.OwingAgent setup runtime leaks bounds horizon NativeScheduler ((N).agentAt
      site))
    (atTurn : CommitsAtTurn setup runtime leaks bounds horizon NativeScheduler who site choice)
    (unintendedChoice : ¬ IntendedCommitment setup runtime leaks bounds horizon NativeScheduler
      site choice)
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past, view))
    (response : (application setup runtime leaks).Action) (selected : choice.1 = some response)
    (material : (application setup runtime leaks).Submission)
    (sends : response.transmission = some material)
    (event : (graph setup).EventId) (candidate : Handle (graph setup))
    (packet : material.call.packet = .commitment event candidate)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ}
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound)
    (history : (N).InformationHistory who site.1)
    (forced : ForcedState setup runtime leaks who history.1.state) :
    let certificate := ((Menu).bounded (initialLaw setup) horizon
      NativeScheduler).wellFoundedHistories
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who
    expect ((N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature) common who
          ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff =
      excludedPayoff who := by
  intro certificate stopped payoff
  have debtFree := siteDebtFree_of_not_owing setup runtime leaks bounds horizon NativeScheduler
    notOwing
  have member : response ∈ bounds.onePacketActions runtime leaks who past view := by
    obtain ⟨other, otherChosen, offered⟩ := choice_response setup runtime leaks bounds horizon
      (NativeScheduler) site atSite choice
    have same := Option.some.inj (selected.symm.trans otherChosen)
    subst other
    exact offered
  obtain ⟨candidateOwner, ⟨serial, candidateSlot⟩, payload, outputEq, codeEq, _⟩ :=
    onePacket_commitment_facts (runtime := runtime) bounds member sends packet
  have candidateEq : candidate = (who, .prepared serial) := Prod.ext candidateOwner candidateSlot
  subst candidateEq
  have submitted : runtime.submittedEvent? leaks response = some event := by
    unfold EventGraphRuntime.submittedEvent?
    simp only [sends, packet, Payload.event?]
  obtain ⟨otherPast, otherView, otherResponse, otherEvent, otherAt, otherChosen, otherSubmitted,
    turn⟩ := atTurn
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (atSite.symm.trans otherAt))
  have sameResponse := Option.some.inj (selected.symm.trans otherChosen)
  subst otherResponse
  have sameEvent := Option.some.inj (submitted.symm.trans otherSubmitted)
  subst otherEvent
  have pending := pendingEvent_of_turnSubmission setup runtime leaks bounds horizon
    (NativeScheduler) site
    atSite turn choice selected submitted
  obtain ⟨remaining, execution, current, pastEq, viewEq, ordered⟩ :=
    ordered_of_site setup runtime leaks bounds horizon NativeScheduler atSite history
  have actualAt : site.1 = some (execution.recall who,
      execution.observe (application setup runtime leaks) who) := by
    rw [pastEq, viewEq]
    exact atSite
  obtain ⟨point, decoded, intended, _reached⟩ :=
    intendedReached_of_forced_debtFree (runtime := runtime) wellFormed site debtFree history
      current ordered forced
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (atSite.symm.trans actualAt))
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have pointDecoded := (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have clear := exclusionEvidence_of_decodedIntended (runtime := runtime)
    ((Menu).toRawTrace (initialLaw setup) horizon (NativeScheduler) (current ▸ history.1.trace))
    pointDecoded intended
  have afterLookup : ∀ slot, (execution.respond (application setup runtime leaks) who
      response).application.candidates.lookup (who, slot) =
      material.call.candidateAfter who
        (execution.observe (application setup runtime leaks) who).application.candidates slot := by
    intro slot
    rcases response with ⟨transmission⟩
    change transmission = some material at sends
    subst sends
    exact material.call.candidateAfter_eq who execution.application slot
  have fixed : (execution.respond (application setup runtime leaks) who
      response).application.candidates.lookup (who, .prepared serial) ≠ .fresh := by
    rw [afterLookup]
    unfold Submission.candidateAfter
    rw [packet]
    simp only [and_self, ↓reduceIte]
    split
    · split <;> simp
    · assumption
  have projected : projectView setup runtime leaks who site.1 =
      some (ProtocolState.observe who setup.program point) := by
    rw [actualAt]
    exact projectView_observe setup runtime leaks who execution (siteRank (runtime := runtime)
      site.1) ordered point decoded _
  have acting := (decodedPoint_actor who ready pointDecoded).trans
    (PublicView.ownTurn?_spec _ who event turn).2
  have unintended : ∀ value act,
      (execution.respond (application setup runtime leaks) who
        response).application.candidates.lookup
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
  have going : ¬ LateStopped setup runtime leaks bounds horizon (NativeScheduler) (siteRank
    (runtime := runtime) site.1)
      history.1 := by
    rintro ⟨other, state, nextPrefix⟩
    rw [current] at state
    cases Option.some.inj state
    have := isPrefix_unique nextPrefix ordered
    omega
  have oneStep : ((N).runBehavioralFrom installed 1 history.1).map History.state =
      PMF.pure (some ⟨remaining, none,
        execution.respond (application setup runtime leaks) who response⟩) := by
    rw [(Menu).run_one_response (initialLaw setup) horizon (NativeScheduler) installed history.1
      who
      remaining execution current]
    dsimp only [installed]
    simp only [ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
      ReactiveApplication.ResponseMenu.embedPolicy, Profile.update_same, PMF.map_comp]
    rw [← actualAt, BehavioralPolicy.withLaw_self, PMF.pure_map]
    change PMF.pure (some (⟨remaining, none, execution.respond (application setup runtime leaks) who
      (choice.1.getD (⟨none⟩ : (application setup runtime leaks).Action))⟩ :
        (application setup runtime leaks).Control)) = _
    rw [selected, Option.getD_some]
  have phaseOwed : ∀ final ∈ ((N).runBehavioralUntil certificate installed
      (LateStopped setup runtime leaks bounds horizon (NativeScheduler) (siteRank (runtime :=
        runtime) site.1))
      history.1).support,
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state := by
    intro final member
    rw [(N).runBehavioralUntil_of_running certificate installed going running,
      PMF.mem_support_bind_iff] at member
    obtain ⟨middle, stepped, rest⟩ := member
    have middleState : middle.state =
        some ⟨remaining, none, execution.respond (application setup runtime leaks) who response⟩
          := by
      have mem : middle.state ∈ (((N).runBehavioralFrom installed 1 history.1).map
          History.state).support := (PMF.mem_support_map_iff _ _ _).mpr ⟨middle, stepped, rfl⟩
      rw [oneStep, PMF.mem_support_pure_iff] at mem
      exact mem
    exact Vegas.unintendedCommitment_phase_owes (runtime := runtime) terminalCompletes
      (failureProfile setup.program)
      turn outputEq codeEq
      pointDecoded intended ordered response material sends packet fixed unintended certificate
      installed middle middleState final rest
  have phaseEq := pending_until_eq_clearUntil (runtime := runtime) terminalCompletes certificate
    installed history.1
    current ordered clear event
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
    rw [debtStopped_eq_bind_eventPhase (runtime := runtime) certificate installed who history.1 _
      current ordered point
      decoded intended, expect_bind_tower_bounded _ _ _ payoffBounded]
    have constant : ∀ final ∈ ((N).runBehavioralUntil certificate installed
        (fun final => LateStopped setup runtime leaks bounds horizon (NativeScheduler) (siteRank
          (runtime := runtime) site.1)
          final ∨ ¬ Clear final.state) history.1).support,
        expect ((N).runBehavioralUntil certificate installed stopped final) payoff =
          excludedPayoff who := by
      intro final member
      have owed := phaseOwed final (phaseEq.symm ▸ member)
      have halt : stopped final := Or.inr owed
      rw [(N).runBehavioralUntil_of_stopped certificate installed halt, expect_pure]
      exact ite_eq_left halt
    exact (expect_congr_on_support constant).trans (expect_constant _ _)
  exact valueEq


open Classical in
theorem recovery_unintendedCommitment_stopped_value
    [(application setup runtime leaks).FiniteNature (initialLaw setup) NativeScheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed)
    (completes : Recovery.CompletesPlay runtime leaks Initial horizon scheduler)
    (common : ∀ player, (N).BehavioralPolicy player)
    {who : Player} (site : (N).InformationSite who) (choice : (N).Choice who site.1)
    (notOwing : ¬ Vegas.OwingAgent setup runtime leaks bounds horizon NativeScheduler ((N).agentAt
      site))
    (atTurn : CommitsAtTurn setup runtime leaks bounds horizon NativeScheduler who site choice)
    (unintendedChoice : ¬ IntendedCommitment setup runtime leaks bounds horizon NativeScheduler
      site choice)
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past, view))
    (response : (application setup runtime leaks).Action) (selected : choice.1 = some response)
    (material : (application setup runtime leaks).Submission)
    (sends : response.transmission = some material)
    (event : (graph setup).EventId) (candidate : Handle (graph setup))
    (packet : material.call.packet = .commitment event candidate)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ}
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound)
    (history : (N).InformationHistory who site.1)
    (forced : ForcedState setup runtime leaks who history.1.state) :
    let certificate := ((Menu).bounded (initialLaw setup) horizon
      NativeScheduler).wellFoundedHistories
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who
    expect ((N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature) common who
          ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff =
      excludedPayoff who := by
  exact unintendedCommitment_stopped_value setup runtime leaks bounds horizon scheduler wellFormed
    (Recovery.CompletesPlay.clear_counted_native (runtime := runtime) bounds
      (initialLaw_initialized setup)
      (initialLaw_native setup) completes)
    common site choice notOwing atTurn unintendedChoice atSite response selected material sends
    event candidate packet parameter utility excludedPayoff readoutBounded excludedBounded
    history forced

open Classical in
theorem unintendedCommitment_value_sub_le
    [(application setup runtime leaks).FiniteNature (initialLaw setup) NativeScheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed)
    (terminalCompletes : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).Trace (some
        control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      (application setup runtime leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (assessment : (N).BehavioralAssessment)
    {who : Player} (site : (N).InformationSite who) (choice : (N).Choice who site.1)
    (notOwing : ¬ Vegas.OwingAgent setup runtime leaks bounds horizon NativeScheduler ((N).agentAt
      site))
    (atTurn : CommitsAtTurn setup runtime leaks bounds horizon NativeScheduler who site choice)
    (unintendedChoice : ¬ IntendedCommitment setup runtime leaks bounds horizon NativeScheduler
      site choice)
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past, view))
    (response : (application setup runtime leaks).Action) (selected : choice.1 = some response)
    (material : (application setup runtime leaks).Submission)
    (sends : response.transmission = some material)
    (event : (graph setup).EventId) (candidate : Handle (graph setup))
    (packet : material.call.packet = .commitment event candidate)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ}
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound)
    {unforced : ℝ}
    (unforcedMass : expect (assessment.belief who site) (fun history =>
      if ForcedState setup runtime leaks who history.1.state then (0 : ℝ) else 1) ≤ unforced) :
    let certificate := ((Menu).bounded (initialLaw setup) horizon
      NativeScheduler).wellFoundedHistories
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who
    |expect (assessment.belief who site) (fun history =>
        expect ((N).runBehavioralUntil certificate
          (Profile.update (sig := (N).behavioralSignature) assessment.strategy who
            ((assessment.strategy who).withLaw site.1 (PMF.pure choice))) stopped history.1)
          payoff) - excludedPayoff who| ≤ 2 * payoffBound * unforced := by
  intro certificate stopped payoff
  let result := fun history : (N).InformationHistory who site.1 =>
    expect ((N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) assessment.strategy who
        ((assessment.strategy who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff
  have bounded : ∀ final, |payoff final| ≤ payoffBound := by
    intro final
    dsimp only [payoff]
    split
    · exact excludedBounded
    · rw [exclusionBase_eq_readout]
      exact readoutBounded _
  have boundNonneg : 0 ≤ payoffBound := (abs_nonneg _).trans excludedBounded
  have rows : ∀ history ∈ (assessment.belief who site).support,
      |result history - excludedPayoff who| ≤ 2 * payoffBound *
        if ForcedState setup runtime leaks who history.1.state then (0 : ℝ) else 1 := by
    intro history _supported
    by_cases forced : ForcedState setup runtime leaks who history.1.state
    · have same := unintendedCommitment_stopped_value setup runtime leaks bounds horizon scheduler
        wellFormed terminalCompletes assessment.strategy site choice notOwing atTurn
        unintendedChoice atSite response selected material sends event candidate packet parameter
        utility excludedPayoff
        readoutBounded excludedBounded history forced
      simp only [forced, ↓reduceIte, mul_zero]
      change |result history - excludedPayoff who| ≤ 0
      rw [show result history = excludedPayoff who from same, sub_self, abs_zero]
    · have inside : |result history| ≤ payoffBound :=
        expect_abs_le_of_bounded boundNonneg bounded
      simp only [forced, ↓reduceIte, mul_one]
      exact (abs_sub _ _).trans (by linarith)
  have near := abs_expect_sub_le_expect (assessment.belief who site) result
    (fun _ => excludedPayoff who) (fun history => 2 * payoffBound *
      if ForcedState setup runtime leaks who history.1.state then (0 : ℝ) else 1) rows
  rw [expect_constant, expect_const_mul] at near
  have scaled : 2 * payoffBound * expect (assessment.belief who site) (fun history =>
      if ForcedState setup runtime leaks who history.1.state then (0 : ℝ) else 1) ≤
        2 * payoffBound * unforced := mul_le_mul_of_nonneg_left unforcedMass (by positivity)
  exact near.trans scaled


open Classical in
theorem recovery_unintendedCommitment_value_sub_le
    [(application setup runtime leaks).FiniteNature (initialLaw setup) NativeScheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed)
    (completes : Recovery.CompletesPlay runtime leaks Initial horizon scheduler)
    (assessment : (N).BehavioralAssessment)
    {who : Player} (site : (N).InformationSite who) (choice : (N).Choice who site.1)
    (notOwing : ¬ Vegas.OwingAgent setup runtime leaks bounds horizon NativeScheduler ((N).agentAt
      site))
    (atTurn : CommitsAtTurn setup runtime leaks bounds horizon NativeScheduler who site choice)
    (unintendedChoice : ¬ IntendedCommitment setup runtime leaks bounds horizon NativeScheduler
      site choice)
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past, view))
    (response : (application setup runtime leaks).Action) (selected : choice.1 = some response)
    (material : (application setup runtime leaks).Submission)
    (sends : response.transmission = some material)
    (event : (graph setup).EventId) (candidate : Handle (graph setup))
    (packet : material.call.packet = .commitment event candidate)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ}
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound)
    {unforced : ℝ}
    (unforcedMass : expect (assessment.belief who site) (fun history =>
      if ForcedState setup runtime leaks who history.1.state then (0 : ℝ) else 1) ≤ unforced) :
    let certificate := ((Menu).bounded (initialLaw setup) horizon
      NativeScheduler).wellFoundedHistories
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who
    |expect (assessment.belief who site) (fun history =>
        expect ((N).runBehavioralUntil certificate
          (Profile.update (sig := (N).behavioralSignature) assessment.strategy who
            ((assessment.strategy who).withLaw site.1 (PMF.pure choice))) stopped history.1)
          payoff) - excludedPayoff who| ≤ 2 * payoffBound * unforced := by
  exact unintendedCommitment_value_sub_le setup runtime leaks bounds horizon scheduler wellFormed
    (Recovery.CompletesPlay.clear_counted_native (runtime := runtime) bounds
      (initialLaw_initialized setup)
      (initialLaw_native setup) completes)
    assessment site choice notOwing atTurn unintendedChoice atSite response selected material sends
    event candidate packet parameter utility excludedPayoff readoutBounded excludedBounded
    unforcedMass

end Vegas.RecoveryOnePacket
