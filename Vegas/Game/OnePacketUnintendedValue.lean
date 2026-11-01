/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketBeliefWiring
import Vegas.Game.RecoveryNonLateChoices
import Vegas.Game.OnePacketUnintendedCommitment
import Vegas.Game.OnePacketLateSuccess
import Vegas.Game.OnePacketEventPhaseLaw
import Vegas.Game.OnePacketComparisonContinuationValue
import GameTheoryExtensions.Math.Probability.ExpectationContraction

/-! # Exclusion value of an unintended current commitment -/

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

/-- At its first completion stop, a fixed unintended binding leaves its owner
owing failure, including after automatic completions. -/
theorem unintendedCommitment_phase_owes
    (terminalCompletes : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
      control.execution.application.config.defaulted = ∅ →
      (application setup runtime leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (profile : BehavioralProfile setup.program)
    {remaining : Nat} {who : Player} {execution : (application setup runtime leaks).Execution}
    {event : (graph setup).EventId}
    (turn : execution.application.publicView.ownTurn? who = some event) {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {point : ProtocolState setup.program}
    (decoded : decodedPoint setup execution.application.config = some point)
    (pointIntended : ProtocolState.Intended setup.program point)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    (response : (application setup runtime leaks).Action) (material : (application setup runtime
      leaks).Submission)
    (submits : response.transmission = some material) {candidate : Handle (graph setup)}
    (call : (sentEnvelope setup runtime leaks execution who material).payload.call =
      .commitment event candidate)
    (fixed : (execution.respond (application setup runtime leaks) who
      response).application.candidates.lookup candidate ≠ .fresh)
    (unintended : ∀ value act, (execution.respond (application setup runtime leaks) who
        response).application.candidates.lookup candidate = .openable ⟨payload, value⟩ →
      decodeEventAction setup.program event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (some (PublicationResult.success value))) = some act →
      act ∉ ProtocolView.intendedAvailable who setup.program
        (ProtocolState.observe who setup.program point))
    (certificate : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu runtime leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (history : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    (current : history.state = some ⟨remaining, none,
      execution.respond (application setup runtime leaks) who response⟩) :
    ∀ final ∈ ((N).runBehavioralUntil certificate players
        (LateStopped setup runtime leaks bounds horizon scheduler rank) history).support,
      DecodedState setup runtime leaks profile (ProtocolState.OwesFailure who setup.program)
        final.state
        := by
  let menu := bounds.onePacketMenu runtime leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  have afterTrace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, execution.respond (application setup runtime leaks) who response⟩) :=
    current ▸ history.trace
  have ready : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
  have sameConfig := (runtime.reactive_respond_application leaks execution who response).1
  have start : UnintendedCommitmentInvariant setup runtime leaks bounds horizon scheduler profile
    who
      (respondEntry setup runtime leaks execution who response)
      (sentEnvelope setup runtime leaks execution who material) event candidate outputEq
      execution.application.config point history.state := by
    rw [current]
    refine ⟨⟨afterTrace⟩, recordsEntry_respond (runtime := runtime) execution who response
      remaining none,
      by rw [respondEntry_of_transmission (runtime := runtime) execution who response material
        submits], rfl, call,
      fixed, unintended, fun _ => sameConfig, fun done => ?_⟩
    rw [sameConfig] at done
    exact (ready.1 done).elim
  intro final supported
  have reachedInvariant := model.runBehavioralUntil_support_closed certificate players
    (LateStopped setup runtime leaks bounds horizon scheduler rank) _
    (fun history _ _ joint legal target holds reached =>
      unintendedCommitmentInvariant_transition (runtime := runtime) bounds horizon scheduler
        profile codeEq decoded
        (ProtocolState.intendedFor_of_intended who setup.program point pointIntended) ready
        history.state target joint legal holds reached) history start final supported
  obtain ⟨anchor, state, action, primary, primaryStep, drained⟩ :=
    lateStop_primary_drain certificate players ordered ready
      (fun last trace ended same => by
        have lastClear : last.execution.application.config.defaulted = ∅ := by
          rw [same]
          exact defaulted_eq_empty_of_decodedIntended decoded pointIntended
        rw [terminalCompletes last trace lastClear ended]
        exact Finset.mem_univ _)
      history current sameConfig final supported
  have primaryDone : event ∈ primary.config.cut.completed := by
    rw [execution.application.config.step_cut event ready action _ primaryStep,
      EventOrder.Cut.mem_complete]
    exact Or.inl rfl
  have completed : event ∈ anchor.execution.application.config.cut.completed := by
    rw [drained]
    exact EventGraph.Config.Step.path_completed_mono primary.drain_graph_steps primaryDone
  rw [state] at reachedInvariant
  have debt := reachedInvariant.2.2.2.2.2.2.2.2 completed
  simpa only [state] using debt



open Classical in
theorem unintendedCommitment_stopped_value
    [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed)
    (terminalCompletes : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some
        control) →
      control.execution.application.config.defaulted = ∅ →
      (application setup runtime leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (common : ∀ player, (N).BehavioralPolicy player)
    {who : Player} (site : (N).InformationSite who) (choice : (N).Choice who site.1)
    (notOwing : ¬ Vegas.OwingAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt site))
    (atTurn : CommitsAtTurn setup runtime leaks bounds horizon scheduler who site choice)
    (unintendedChoice : ¬ IntendedCommitment setup runtime leaks bounds horizon scheduler
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
      scheduler).wellFoundedHistories
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
  have debtFree := siteDebtFree_of_not_owing setup runtime leaks bounds horizon scheduler
    notOwing
  have member : response ∈ bounds.onePacketActions runtime leaks who past view := by
    obtain ⟨other, otherChosen, offered⟩ := choice_response setup runtime leaks bounds horizon
      scheduler site atSite choice
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
  obtain ⟨remaining, execution, current, pastEq, viewEq⟩ :
      ∃ remaining execution, history.1.state = some ⟨remaining, some who, execution⟩ ∧
        execution.recall who = past ∧
        execution.observe (application setup runtime leaks) who = view := by
    obtain ⟨fullHistory, infoEq⟩ := history
    have observed : (application setup runtime leaks).observe who fullHistory.state =
        some (past, view) :=
      ((Menu).info (initialLaw setup) horizon scheduler who fullHistory.trace).symm.trans
        (infoEq.trans atSite)
    cases state : fullHistory.state with
    | none =>
        rw [state] at observed
        cases observed
    | some control =>
        rw [state] at observed
        rcases control with ⟨remaining, actor, execution⟩
        unfold ReactiveApplication.observe at observed
        by_cases acting : actor = some who
        · subst acting
          simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at observed
          exact ⟨remaining, execution, rfl, observed.1, observed.2⟩
        · simp only [acting, ↓reduceIte] at observed
          cases observed
  have trace : (NP).Trace (some ⟨remaining, some who, execution⟩) := current ▸ history.1.trace
  obtain ⟨found, foundOrdered, _⟩ := pendingAt_history (runtime := runtime)
    ((Menu).toRawTrace (initialLaw setup) horizon scheduler trace)
  have siteRankEq : siteRank (runtime := runtime) site.1 = found := by
    rw [atSite, ← viewEq]
    change (execution.application.config.history.map EventCompletion.event).length = found
    rw [List.length_map]
    exact history_length_of_isPrefix _ foundOrdered
  have ordered : execution.application.config.cut.IsPrefix
      (siteRank (runtime := runtime) site.1) := siteRankEq.symm ▸ foundOrdered
  have actualAt : site.1 = some (execution.recall who,
      execution.observe (application setup runtime leaks) who) := by
    rw [pastEq, viewEq]
    exact atSite
  have forcedHere := forced
  rw [current] at forcedHere
  obtain ⟨point, pointDecoded, forcedPoint⟩ :=
    (forcedState_iff_decodedPoint (runtime := runtime) _).mp forcedHere
  have decoded : sourceServicePrefix? setup (siteRank (runtime := runtime) site.1)
      execution.application.config = some point :=
    (decodedPoint_eq_of_isPrefix ordered).symm.trans pointDecoded
  obtain ⟨rank, ⟨residual⟩, holds⟩ := decodedState_intended_or_owes (runtime := runtime)
    wellFormed (failureProfile setup.program) (Menu) horizon scheduler trace _ rfl
  have sameRank := EventOrder.Cut.IsPrefix.unique residual.checkpoint.ordered ordered
  subst sameRank
  have intended : ProtocolState.Intended setup.program point := by
    rcases holds point decoded with intended | ⟨player, owed⟩
    · exact intended
    · by_cases same : player = who
      · subst player
        exact (debtFree history point (by rw [current]; exact pointDecoded) owed).elim
      · exact ((forcedPoint.2 player same).2 owed).elim
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (atSite.symm.trans actualAt))
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have pointDecoded := (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have clear := defaulted_eq_empty_of_decodedIntended
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
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have acting : ProtocolView.actor who setup.program
      (ProtocolState.observe who setup.program point) = some who :=
    (decodedPoint_actor who ready pointDecoded).trans (by simp [owned, clear])
  have unintended : ∀ value act,
      (execution.respond (application setup runtime leaks) who
        response).application.candidates.lookup
        (who, .prepared serial) = .openable ⟨payload, value⟩ →
      decodeEventAction setup.program event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (some (PublicationResult.success value))) = some act →
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
  have going : ¬ LateStopped setup runtime leaks bounds horizon scheduler (siteRank
    (runtime := runtime) site.1)
      history.1 := by
    rintro ⟨other, state, completed, done, atRank⟩
    rw [current] at state
    cases Option.some.inj state
    have := (ordered.2 completed).mp done
    omega
  have oneStep : ((N).runBehavioralFrom installed 1 history.1).map History.state =
      PMF.pure (some ⟨remaining, none,
        execution.respond (application setup runtime leaks) who response⟩) := by
    rw [(Menu).run_one_response (initialLaw setup) horizon scheduler installed history.1
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
      (LateStopped setup runtime leaks bounds horizon scheduler (siteRank (runtime :=
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
    exact unintendedCommitment_phase_owes setup runtime leaks bounds horizon scheduler
      terminalCompletes
      (failureProfile setup.program)
      turn outputEq codeEq
      pointDecoded intended ordered response material sends packet fixed unintended certificate
      installed middle middleState final rest
  have phaseEq := pending_until_eq_clearUntil (runtime := runtime) certificate
    installed history.1
    current ordered clear event
    ready
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
              (sourceReadout setup runtime leaks (some control)) who| ≤ payoffBound
          split
          · exact excludedBounded
          · exact readoutBounded _
  have valueEq : expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff =
      excludedPayoff who := by
    rw [debtStopped_eq_bind_eventPhase (runtime := runtime) certificate installed who history.1 _
      current ordered point decoded intended, expect_bind_tower_bounded _ _ _ payoffBounded]
    have constant : ∀ final ∈ ((N).runBehavioralUntil certificate installed
        (fun final => LateStopped setup runtime leaks bounds horizon scheduler (siteRank
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
theorem unintendedCommitment_value_sub_le
    [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed)
    (terminalCompletes : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some
        control) →
      control.execution.application.config.defaulted = ∅ →
      (application setup runtime leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (assessment : (N).BehavioralAssessment)
    {who : Player} (site : (N).InformationSite who) (choice : (N).Choice who site.1)
    (notOwing : ¬ Vegas.OwingAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt site))
    (atTurn : CommitsAtTurn setup runtime leaks bounds horizon scheduler who site choice)
    (unintendedChoice : ¬ IntendedCommitment setup runtime leaks bounds horizon scheduler
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
      scheduler).wellFoundedHistories
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
    · cases final.state with
      | none =>
          simpa only [exclusionBase, abs_zero] using (abs_nonneg _).trans excludedBounded
      | some control =>
          change |if who ∈ control.execution.application.config.defaulted then excludedPayoff who
            else exclusionReadoutUtility setup parameter utility excludedPayoff
              (sourceReadout setup runtime leaks (some control)) who| ≤ payoffBound
          split
          · exact excludedBounded
          · exact readoutBounded _
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
  have near := (abs_expect_sub_le_expect_abs_sub (assessment.belief who site) result
    (fun _ => excludedPayoff who) (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)).trans
      (expect_mono rows (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _))
  rw [expect_constant, expect_const_mul] at near
  have scaled : 2 * payoffBound * expect (assessment.belief who site) (fun history =>
      if ForcedState setup runtime leaks who history.1.state then (0 : ℝ) else 1) ≤
        2 * payoffBound * unforced := mul_le_mul_of_nonneg_left unforcedMass (by positivity)
  exact near.trans scaled


end Vegas.OnePacketComparison
