/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobDisclosureChronology

/-! # Successful disclosure after an actual clean first binding

At every legal native continuation of an accepted clean first binding,
sequentially rational Bob publishes its immutable answer. The optional
callback either already publishes it or leaves a clean timely final callback.
Both implications use complete actual information classes, including hidden
histories assigned zero posterior belief. Publication remains persistent even
when a later response creates an unrelated audit deduction.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobDisclosurePublication

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobDisclosureChronology
open LateOpeningRuntimeBobBindingService (SilentRecall)
open LateOpeningRuntimeBobBindingPacket (responseMessage)
open LateOpeningRuntimeBobRawBinding (serviced serviced_round serviced_trace)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (reward forfeit : ℝ) (deposit : Player → ℝ)
  (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)

private theorem decoded_covered (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) (response : app.Action)
    (supported : response ∈ (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
        who past view).support) : response ∈ rawMenu.actions who past view :=
  rawMenu.decode_embedPolicy_covered initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) who (assessment.strategy who)
      past view response supported

private theorem final_response_publication
    (decision : LateOpeningRuntimeBobIncentive.DecisionHistory weight nonnegative)
    (boundedTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨6, some bob, decision.execution⟩))
    (forfeitPositive : 0 < forfeit) (depositPositive : 0 < deposit bob)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (response : app.Action)
    (supported : response ∈ (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob
        (decision.execution.recall bob) (decision.execution.observe app bob)).support)
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (LateOpeningRuntimeBobIncentive.continuation weight nonnegative
      decision response players).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success decision.answer) := by
  let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
    ⟨some ⟨6, some bob, decision.execution⟩, boundedTrace⟩
  have running : ¬ (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).terminal history.state := by
    change ¬ (6 = 0 ∧ some bob = none)
    simp
  obtain ⟨site, same⟩ := (LateOpeningRuntimeNash.model weight nonnegative)
    |>.exists_informationSite_of_active bob history running rfl
  let representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1 := ⟨history, same.symm⟩
  have current : representative.1.state = some ⟨6, some bob, decision.execution⟩ := rfl
  have info := LateOpeningRuntimeBobRationality.site_information weight nonnegative site
    representative decision current
  have selected : response ∈ ((assessment.strategy bob site.1).map
      (fun choice => choice.1.getD ⟨none⟩)).support := by
    rw [info]
    unfold ReactiveApplication.ResponseMenu.decodeProfile ReactiveApplication.decodePolicy
      ReactiveApplication.ResponseMenu.embedPolicy at supported
    rw [PMF.map_comp] at supported
    exact supported
  have valid := LateOpeningRuntimeBobInformation.decisionOfInformation_spec weight nonnegative
    site representative decision current representative
  have recovered : (LateOpeningRuntimeBobInformation.decisionOfInformation weight nonnegative
      site representative decision current representative).execution = decision.execution := by
    have states := congrArg (fun state : Option app.Control =>
      state.map (fun control => control.execution)) (current.symm.trans valid.1)
    simpa only [Option.map_some, Option.some.injEq] using states.symm
  have reached' : final ∈ (LateOpeningRuntimeBobIncentive.continuation weight nonnegative
      (LateOpeningRuntimeBobInformation.decisionOfInformation weight nonnegative site
        representative decision current representative) response players).support := by
    unfold LateOpeningRuntimeBobIncentive.continuation
    rw [recovered]
    exact reached
  exact LateOpeningRuntimeBobFinalFiberRationality.sequentially_rational_supported_publication
    weight nonnegative site representative decision current reward forfeit
      (fun actual => PMF.pure actual) deposit forfeitPositive
      (by
        intro actual observed present
        cases (PMF.mem_support_pure_iff _ _).mp present
        exact List.Subset.refl _)
      depositPositive.le assessment rational representative response selected players final reached'

/-- An optional response supported by the actual native strategy either
publishes immediately or reaches the genuine rational final callback.
Future Alice policies remain arbitrary. -/
theorem optional_response_publication
    (decision : LateOpeningRuntimeOptionalOpening.DecisionHistory weight nonnegative)
    (boundedTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨12, some bob, decision.execution⟩))
    (timer : decision.execution.application.activatedAt bobRevealEvent = some 3)
    (clock : decision.execution.application.clock = 3)
    (forfeitPositive : 0 < forfeit) (depositPositive : 0 < deposit bob)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (response : app.Action)
    (supported : response ∈ (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob
        (decision.execution.recall bob) (decision.execution.observe app bob)).support)
    (players : Player → app.Policy)
    (bobPolicy : players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 12 (decision.execution.respond app bob response)).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success decision.answer) := by
  let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
    ⟨some ⟨12, some bob, decision.execution⟩, boundedTrace⟩
  have running : ¬ (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).terminal history.state := by
    change ¬ (12 = 0 ∧ some bob = none)
    simp
  obtain ⟨site, same⟩ := (LateOpeningRuntimeNash.model weight nonnegative)
    |>.exists_informationSite_of_active bob history running rfl
  let representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      bob site.1 := ⟨history, same.symm⟩
  have current : representative.1.state = some ⟨12, some bob, decision.execution⟩ := rfl
  have valid := LateOpeningRuntimeOptionalInformation.decisionOfInformation_spec weight
    nonnegative site representative decision current representative
  have recovered : (LateOpeningRuntimeOptionalInformation.decisionOfInformation weight
      nonnegative site representative decision current representative).execution =
        decision.execution := by
    have states := congrArg (fun state : Option app.Control =>
      state.map (fun control => control.execution)) (current.symm.trans valid.1)
    simpa only [Option.map_some, Option.some.injEq] using states.symm
  have classified := LateOpeningRuntimeOptionalPacket.sequentially_rational_supported_response
    weight nonnegative site representative decision current reward forfeit deposit forfeitPositive
      depositPositive assessment rational representative response supported
  rw [recovered] at classified
  rcases classified with silent | published
  · have responseEq : response = ⟨none⟩ := by
      cases response
      cases silent
      rfl
    subst response
    let decoded := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
    obtain ⟨respondedTrace⟩ := rawMenu.trace_respond initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) 12 decision.execution bob ⟨none⟩
        boundedTrace (decoded_covered weight nonnegative assessment bob _ _ _ supported)
    obtain ⟨beforeTrace⟩ := rawMenu.trace_runRounds initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) decoded
        (decoded_covered weight nonnegative assessment) 7 5 _ (beforeFinal decision.execution)
          respondedTrace (by
            rw [silence_prefix_law weight nonnegative decision decoded]
            exact (PMF.mem_support_pure_iff _ _).mpr rfl)
    rw [app.runRounds_add (LateOpeningRuntimeService.scheduler weight nonnegative) players 5 7,
      silence_prefix_law weight nonnegative decision players, PMF.pure_bind] at reached
    obtain ⟨next, advanced, suffix⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
    have cursor : (beforeFinal decision.execution).environmentRecall.length = 19 := by
      have raw := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) beforeTrace
      have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) raw
      change (beforeFinal decision.execution).environmentRecall.length + 7 = 26 at counted
      omega
    have chosen : LateOpeningRuntimeService.scheduler weight nonnegative
        (beforeFinal decision.execution).environmentRecall
          ((beforeFinal decision.execution).observeEnvironment app) = PMF.pure (.activate bob) := by
      change stageChoice weight nonnegative _ _ = _
      rw [cursor]
      rfl
    rw [ReactiveApplication.round, chosen, PMF.pure_bind, ReactiveApplication.dispatch] at advanced
    obtain ⟨observed, sampled, responded⟩ := (PMF.mem_support_bind_iff _ _ _).mp advanced
    obtain ⟨lastResponse, lastSelected, rfl⟩ := PMF.support_map .. ▸ responded
    obtain ⟨finalDecision, sameExecution, sameAnswer, _⟩ := final_of_optional_silence weight
      nonnegative decision timer clock observed sampled
    obtain ⟨observedTrace⟩ := rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) 6 _ observed (.activate bob)
        beforeTrace (by
          rw [chosen]
          exact (PMF.mem_support_pure_iff _ _).mpr rfl) sampled
    have finalTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
          (some ⟨6, some bob, finalDecision.execution⟩) := sameExecution.symm ▸ observedTrace
    have lastSupported : lastResponse ∈ (decoded bob (finalDecision.execution.recall bob)
        (finalDecision.execution.observe app bob)).support := by
      rw [sameExecution]
      change lastResponse ∈ (players bob _ _).support at lastSelected
      rwa [bobPolicy] at lastSelected
    have finalReached : final ∈ (LateOpeningRuntimeBobIncentive.continuation weight nonnegative
        finalDecision lastResponse players).support := by
      change final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
        players 6 (finalDecision.execution.respond app bob lastResponse)).support
      rwa [sameExecution]
    have result := final_response_publication weight nonnegative reward forfeit deposit assessment
      finalDecision finalTrace forfeitPositive depositPositive rational lastResponse lastSupported
        players final finalReached
    rwa [sameAnswer] at result
  · obtain ⟨first, firstReached, suffix⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
    have material : ∃ value, response.transmission = some value := by
      cases value : response.transmission with
      | none =>
          have responseEq : response = ⟨none⟩ := by
            cases response
            cases value
            rfl
          rw [responseEq] at published
          change decision.execution.application.config.store (.inr bobRevealEvent) =
            some (.success decision.answer) at published
          have present : (decision.execution.application.config.outputs bobRevealEvent).isSome := by
            change (decision.execution.application.config.store (.inr bobRevealEvent)).isSome = true
            rw [published]
            rfl
          exact (decision.ready.1
            ((decision.execution.application.config.output_available bobRevealEvent).mp
              present)).elim
      | some submission => exact ⟨submission, rfl⟩
    obtain ⟨material, materialEq⟩ := material
    have responseEq : response = ⟨some material⟩ := by
      cases response
      cases materialEq
      rfl
    subst response
    rw [LateOpeningRuntimeOptionalPacket.submission_round weight nonnegative decision material
      players, PMF.mem_support_pure_iff] at firstReached
    subst first
    exact (ReactiveApplication.Invariant.policyInvariant app
      (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr bobRevealEvent)
        (.success decision.answer)) players).runRounds
      (LateOpeningRuntimeService.scheduler weight nonnegative) 11 _ final published suffix

/-- A legal private representation of the accepted canonical binding settles
its selected answer under the original rational receiver policy on every
actual physical branch. No posterior support restriction is present. -/
theorem binding_publication (execution : app.Execution)
    (boundedTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (quiet : SilentRecall execution)
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (material : app.Submission) (answer : Answer)
    (available : ⟨some material⟩ ∈ rawMenu.actions bob (execution.recall bob)
      (execution.observe app bob))
    (selected : (serviced execution ⟨some material⟩).application.config.store (.inr bobBindEvent) =
      some (.success answer))
    (packet : responseMessage execution material = LateOpeningRuntimeBobSuffix.bindingMessage)
    (forfeitPositive : 0 < forfeit) (depositPositive : 0 < deposit bob)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (players : Player → app.Policy)
    (bobPolicy : players bob = rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy bob)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (execution.respond app bob ⟨some material⟩)).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success answer) := by
  have rawTrace := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) boundedTrace
  obtain ⟨respondedTrace⟩ := rawMenu.trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 execution bob ⟨some material⟩
      boundedTrace available
  let decoded := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
  obtain ⟨servedTrace⟩ := rawMenu.trace_round initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) decoded
      (decoded_covered weight nonnegative assessment) 13 _ (serviced execution ⟨some material⟩)
        respondedTrace (by
          rw [serviced_round weight nonnegative execution rawTrace quiet ⟨some material⟩ decoded]
          exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have servedRaw := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) servedTrace
  have cursor : (serviced execution ⟨some material⟩).environmentRecall.length = 13 := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) servedRaw
    change (serviced execution ⟨some material⟩).environmentRecall.length + 13 = 26 at counted
    omega
  obtain ⟨revealReady, _, _⟩ := LateOpeningRuntimeBobBindingChronology.accepted_chronology
    weight nonnegative execution rawTrace quiet ready ⟨some material⟩ answer selected
  have completed : bobBindEvent ∈
      (serviced execution ⟨some material⟩).application.publicView.observation.completionOrder :=
    ((serviced execution ⟨some material⟩).application.config.history_exact bobBindEvent).mpr
      (revealReady.2 (by decide))
  have chosen : LateOpeningRuntimeService.scheduler weight nonnegative
      (serviced execution ⟨some material⟩).environmentRecall
        ((serviced execution ⟨some material⟩).observeEnvironment app) =
          PMF.pure (.activate bob) := by
    change stageChoice weight nonnegative _ _ = _
    rw [cursor]
    change PMF.pure (if bobBindEvent ∈
      (serviced execution ⟨some material⟩).application.publicView.observation.completionOrder
        then (.activate bob : app.Command) else .wait) = _
    rw [ite_eq_left completed]
  change final ∈ ((app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
    (execution.respond app bob ⟨some material⟩)).bind
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 13)).support
    at reached
  rw [serviced_round weight nonnegative execution rawTrace quiet ⟨some material⟩ players,
    PMF.pure_bind] at reached
  obtain ⟨next, activated, suffix⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  rw [ReactiveApplication.round, chosen, PMF.pure_bind, ReactiveApplication.dispatch] at activated
  obtain ⟨observed, sampled, responded⟩ := (PMF.mem_support_bind_iff _ _ _).mp activated
  obtain ⟨response, supported, rfl⟩ := PMF.support_map .. ▸ responded
  obtain ⟨decision, sameExecution, sameAnswer, timer, clock⟩ := optional_of_binding weight
    nonnegative execution rawTrace quiet ready material answer selected packet observed sampled
  obtain ⟨observedTrace⟩ := rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 12 _ observed (.activate bob)
      servedTrace (by
        rw [chosen]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl) sampled
  have optionalTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨12, some bob, decision.execution⟩) := sameExecution.symm ▸ observedTrace
  have optionalSupported : response ∈ (decoded bob (decision.execution.recall bob)
      (decision.execution.observe app bob)).support := by
    rw [sameExecution]
    change response ∈ (players bob _ _).support at supported
    rwa [bobPolicy] at supported
  have result := optional_response_publication weight nonnegative reward forfeit deposit
    assessment decision optionalTrace (sameExecution.symm ▸ timer) (sameExecution.symm ▸ clock)
      forfeitPositive depositPositive rational response optionalSupported players bobPolicy final
        (by rwa [sameExecution])
  rwa [sameAnswer] at result

end Vegas.Examples.LateOpeningRuntimeBobDisclosurePublication
