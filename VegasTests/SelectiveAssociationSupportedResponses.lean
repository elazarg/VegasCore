/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationGuessEquilibrium

/-! # Supported native responses keep their guarantees against changed futures

Sequential rationality constrains the raw response chosen at an information
set. Reserved inclusion executes this same response independently of later
player policies, including Alice's deviating continuation.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory GameTheory.Protocol

theorem native_response_supported_choice
    (profile : ∀ who, nativeModel.BehavioralPolicy who) (who : Player)
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView)
    (response : nativeApp.Action)
    (supported : response ∈ (nativeMenu.decodeProfile (FinDist.pure nativeInitial)
      nativeHorizon nativeScheduler profile who past view).support) :
    ∃ choice : nativeModel.Choice who (some (past, view)),
      choice ∈ (profile who (some (past, view))).support ∧ choice.1 = some response := by
  rw [ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
    ReactiveApplication.ResponseMenu.embedPolicy, FinDist.map_comp,
    FinDist.support_map] at supported
  obtain ⟨choice, chosen, decoded⟩ := supported
  obtain ⟨action, _, selected⟩ := choice.2
  change choice.1.getD ⟨none⟩ = response at decoded
  rw [selected, Option.getD_some] at decoded
  subst action
  exact ⟨choice, chosen, selected⟩

private theorem native_reserved_unique (event : nativeGraph.EventId) (who : Player)
    (firstPlayers secondPlayers : Player → nativeApp.Policy) (execution : nativeApp.Execution)
    (first second : nativeApp.Execution)
    (firstMem : first ∈ (nativeRuntime.interactionStep nativeLeaks firstPlayers nativeNetwork
      (.includeLatest event who) execution).support)
    (secondMem : second ∈ (nativeRuntime.interactionStep nativeLeaks secondPlayers nativeNetwork
      (.includeLatest event who) execution).support) : first = second := by
  rw [nativeRuntime.interaction_includeLatest_environment] at firstMem secondMem
  obtain ⟨result, law⟩ := nativeRuntime.reactiveLatest_step_pure nativeLeaks who event execution
  rw [law] at firstMem secondMem
  exact (FinDist.mem_support_pure.mp firstMem).trans (FinDist.mem_support_pure.mp secondMem).symm

private theorem success_of_getD (value : Option (PublicationResult Bool)) (bit : Bool)
    (correct : value.getD .failure = .success bit) : value = some (.success bit) := by
  cases value with
  | none => cases correct
  | some result => exact congrArg some correct

open Classical in
/-- A raw response supported by Bob's equilibrium policy binds the certified
bit under actual reserved inclusion, even when other players use different
policies throughout the surrounding execution. -/
theorem native_supported_guess_inclusion
    (assessment : nativeModel.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1))
    (control : nativeApp.Control) (trace : nativeArena.Trace (some control))
    (active : control.actor = some bob)
    (granted : control.execution.application.serviceGrant = some bobBinding) (bit : Bool)
    (observed : nativeRuntime.bindingEvidenceObserved nativeLeaks
      (control.execution.observe nativeApp bob) (aliceBindingEvidence bit))
    (response : nativeApp.Action)
    (chosen : response ∈ (nativeMenu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon
      nativeScheduler assessment.strategy bob (control.execution.recall bob)
        (control.execution.observe nativeApp bob)).support)
    (players : Player → nativeApp.Policy) (next : nativeApp.Execution)
    (reached : next ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest bobBinding bob) (control.execution.respond nativeApp bob response)).support) :
    bobBindingRef.get? next.application.config.store = some (.success bit) := by
  let past := control.execution.recall bob
  let view := control.execution.observe nativeApp bob
  obtain ⟨choice, choiceMem, selected⟩ := native_response_supported_choice assessment.strategy bob
    past view response chosen
  have information : nativeModel.infoOf bob trace = some (past, view) := by
    change (nativeMenu.signals (FinDist.pure nativeInitial) nativeHorizon nativeScheduler).infoOf
      bob trace = some (past, view)
    rw [nativeMenu.info]
    simp only [ReactiveApplication.observe, active, ↓reduceIte]
    rfl
  let history : nativeModel.InformationHistory bob (some (past, view)) :=
    ⟨⟨some control, trace⟩, information⟩
  have running : ¬nativeArena.terminal (some control) := by
    intro stopped
    have no : control.actor = none := stopped.2
    rw [active] at no
    cases no
  let site : nativeModel.InformationSite bob := ⟨some (past, view), history, running,
    response, selected ▸ choice.2⟩
  let changed := Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy bob
    ((assessment.strategy bob).commit (some (past, view)) choice)
  obtain ⟨final, finalMem⟩ := (nativeModel.runBehavioralFrom changed
    (2 * nativeHorizon + 1) ⟨some control, trace⟩).support_nonempty
  have incomplete := native_decision_unfinished bobBinding control trace bob active granted
  have finalCorrect := native_supported_certified_guess assessment rational site past view rfl bit
    granted (native_bob_view_unfinished past view granted history) observed choice choiceMem history
    final finalMem
  obtain ⟨middle, middleMem, settled⟩ := native_bob_settlement_behavioral changed control trace
    response active granted incomplete
    (native_committed_response assessment.strategy bob _ choice response selected past view rfl)
    final finalMem
  have equal := native_reserved_unique bobBinding bob _ players
    (control.execution.respond nativeApp bob response) middle next middleMem reached
  subst middle
  rw [settled] at finalCorrect
  exact success_of_getD _ bit (Option.some.inj finalCorrect)

open Classical in
/-- The same guarantee holds for each owner's supported opening response.
It concerns immediate ordinary inclusion, so changed future policies cannot
turn an equilibrium-supported opening into strategic withholding. -/
theorem native_supported_opening_inclusion
    (assessment : nativeModel.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1))
    (who : Player) (control : nativeApp.Control) (trace : nativeArena.Trace (some control))
    (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent who))
    (bit : Bool) (stored : (nativeBindingRef who).get?
      control.execution.application.config.store = some (.success bit))
    (response : nativeApp.Action)
    (chosen : response ∈ (nativeMenu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon
      nativeScheduler assessment.strategy who (control.execution.recall who)
        (control.execution.observe nativeApp who)).support)
    (players : Player → nativeApp.Policy) (next : nativeApp.Execution)
    (reached : next ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest (nativePublicationEvent who) who)
      (control.execution.respond nativeApp who response)).support) :
    (nativePublicationRef who).get? next.application.config.store = some (.success bit) := by
  let past := control.execution.recall who
  let view := control.execution.observe nativeApp who
  obtain ⟨choice, choiceMem, selected⟩ := native_response_supported_choice assessment.strategy who
    past view response chosen
  have information : nativeModel.infoOf who trace = some (past, view) := by
    change (nativeMenu.signals (FinDist.pure nativeInitial) nativeHorizon nativeScheduler).infoOf
      who trace = some (past, view)
    rw [nativeMenu.info]
    simp only [ReactiveApplication.observe, active, ↓reduceIte]
    rfl
  let history : nativeModel.InformationHistory who (some (past, view)) :=
    ⟨⟨some control, trace⟩, information⟩
  have running : ¬nativeArena.terminal (some control) := by
    intro stopped
    have no : control.actor = none := stopped.2
    rw [active] at no
    cases no
  let site : nativeModel.InformationSite who := ⟨some (past, view), history, running,
    response, selected ▸ choice.2⟩
  let changed := Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy who
    ((assessment.strategy who).commit (some (past, view)) choice)
  obtain ⟨final, finalMem⟩ := (nativeModel.runBehavioralFrom changed
    (2 * nativeHorizon + 1) ⟨some control, trace⟩).support_nonempty
  have incomplete := native_decision_unfinished (nativePublicationEvent who) control trace who
    active granted
  have viewIncomplete : nativePublicationEvent who ∉
      view.application.publicView.observation.completionOrder := by
    change nativePublicationEvent who ∉
      control.execution.application.config.history.map EventGraph.Completion.event
    exact fun completed => incomplete
      ((control.execution.application.config.history_exact _).mp completed)
  have viewStored : (nativeBindingRef who).get? view.application.observation.store =
      some (.success bit) := by
    change (nativeBindingRef who).get?
      (nativeGraph.playerStore who control.execution.application.config.store) = _
    rwa [(nativeBindingRef who).get?_playerStore who _ rfl]
  obtain ⟨publishedBit, finalPublished⟩ := native_supported_opening_succeeds assessment who site
    past view rfl bit granted viewIncomplete viewStored (rational who site) choice choiceMem
    history final finalMem
  obtain ⟨result, finalEq, preserved⟩ := native_binding_continuation changed control trace who
    (.success bit) stored final finalMem
  rcases final with ⟨finalState, finalTrace⟩
  change finalState = some result at finalEq
  subst finalState
  have provenance := native_publication_binding result.execution.application.config
    (native_history_reachable result finalTrace) who publishedBit
    (by simpa only [nativePublicationAt, Option.bind_some] using finalPublished)
  have bitEq : publishedBit = bit := by
    rw [preserved] at provenance
    cases Option.some.inj provenance
    rfl
  subst publishedBit
  obtain ⟨middle, middleMem, settled⟩ := native_settlement_behavioral changed control trace who
    response active granted incomplete
    (native_committed_response assessment.strategy who _ choice response selected past view rfl)
    ⟨some result, finalTrace⟩ finalMem
  have equal := native_reserved_unique (nativePublicationEvent who) who _ players
    (control.execution.respond nativeApp who response) middle next middleMem reached
  subst middle
  rw [settled] at finalPublished
  exact success_of_getD _ bit (Option.some.inj finalPublished)

end VegasTests.SelectiveAssociation
