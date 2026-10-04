/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.OpaqueBindingForkSourcePosterior

/-! # Uncharged publication after the opaque late binding

The actual builder accepts Bob's evidence-free FALSE and Alice's certified
TRUE after Alice's late canonical commitment. Her retained private risk remains
visible in her own recall, so her later input is outside the prescribed class.
The full terminal public result agrees with the corresponding source play.
Authentic partial sampling collects nothing from Alice's permitted packets.

For this program's displayed success reward, the actual TRUE continuation
attains the upper bound one. This specifies a literal local alternative, not
the choices returned by free-agent completion or a result for arbitrary payoffs.
-/

noncomputable section

namespace Vegas.OpaqueBindingFork.Publication

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

def bindingMessage : Message Player (WitnessedPacket nativeGraph) :=
  ⟨(alice, 0), ⟨.commitment binding (alice, .prepared 0), none, some ⟨binding⟩⟩⟩

def bindingCompleted : app.State :=
  { (riskySubmitted.application.complete binding binding_ready (.success true) (.success true))
    with
      accepted := Function.update riskySubmitted.application.accepted (.inr binding)
        (some (alice, .prepared 0))
      candidates := riskySubmitted.application.candidates.freeze (alice, .prepared 0) }

theorem binding_handle : app.handle riskySubmitted.application bindingMessage =
    some bindingCompleted := by
  have unused : riskySubmitted.application.HandleUnused (alice, .prepared 0) := by
    intro field associated
    change initialState.accepted field = some (alice, .prepared 0) at associated
    obtain ⟨input, owner, payload, _, _, same⟩ :=
      State.initial_accepted_eq_some (graph := nativeGraph) (setup.eventInputs sourceInitial) field
        (alice, .prepared 0) associated
    cases congrArg Prod.snd same
  have meaning := (runtime setup).reactiveBinding_result leaks alice binding .bool (.success true)
    0 riskySecondAlice rfl
  have handled := handle_commitment_eq (runtime setup) riskySubmitted.application (alice, 0)
    binding (alice, .prepared 0) alice .bool binding_output binding_code binding_node
    binding_ready (by change 1 - 0 < 3; decide) rfl rfl rfl unused
  change riskySubmitted.application.bindingResult (alice, .prepared 0) .bool = .success true
    at meaning
  simp only [meaning] at handled
  rw [(runtime setup).reactiveApplication_handle_of_tokenValid leaks _ bindingMessage rfl]
  exact handled

theorem binding_lookup : riskySubmitted.network.lookup (alice, 0) = some bindingMessage := by
  obtain ⟨canonical⟩ := riskySecondAlice_canonical_trace
  have facts := legalFacts setup leaks horizon scheduler _
    (canonicalMenu.toRawTrace (initialLaw setup) horizon scheduler canonical)
  exact (runtime setup).reactiveBinding_lookup leaks riskySecondAlice alice binding .bool
    (.success true) 0 facts.serials binding_ready

theorem binding_accepted_application : riskyAccepted.application = bindingCompleted := by
  change (riskySubmitted.includePending app (alice, 0)).application = bindingCompleted
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    binding_lookup, binding_handle, Option.getD_some]

theorem riskyBob_clock : riskyBob.application.clock = 3 := by
  change riskyAccepted.application.clock + 1 + 1 = 3
  rw [← accepted_application_eq, cleanAccepted_clock]

theorem riskyBob_accepted : riskyBob.application.accepted (.inr binding) =
    some (alice, .prepared 0) := by
  change riskyAccepted.application.accepted (.inr binding) = _
  rw [binding_accepted_application]
  simp only [bindingCompleted, Function.update_self]

theorem riskyBob_candidate : riskyBob.application.candidates.lookup (alice, .prepared 0) =
    .openable ⟨.bool, true⟩ := by
  change riskyAccepted.application.candidates.lookup (alice, .prepared 0) = _
  rw [binding_accepted_application]
  rfl

def bobAction : app.Action := ⟨some (disclosureSubmission (.withhold bobResolution))⟩

def bobSent : app.Execution := riskyBob.respond app bob bobAction

theorem bob_ready : riskyBob.application.config.cut.Ready bobResolution := by
  rw [← bob_config_eq]
  exact cleanAccepted_bob_ready

def bobCompleted : app.State := riskyBob.application.complete bobResolution bob_ready false .failure

def bobMessage : Message Player (WitnessedPacket nativeGraph) :=
  ⟨(bob, 0), ⟨.withhold bobResolution, none,
    riskyBob.application.publicView.tokenFor (.withhold bobResolution)⟩⟩

theorem bob_handle : app.handle bobSent.application bobMessage = some bobCompleted := by
  obtain ⟨canonical⟩ := riskyBob_canonical_trace
  have trace := canonicalMenu.toRawTrace (initialLaw setup) horizon scheduler canonical
  have publicEq := congrArg (fun input => input.2.application.publicView) bob_input_eq
  change cleanBob.application.publicView = riskyBob.application.publicView at publicEq
  have fits : riskyBob.application.publicView.InclusionFitsDeadline
      (runtime setup) bound bobResolution := by
    rw [← publicEq]
    exact cleanBob_fits
  have handled : handle (runtime setup) riskyBob.application
      ⟨(bob, 0), .withhold bobResolution⟩ = some bobCompleted := by
    apply handle_withhold_unremembered_eq (runtime setup) riskyBob.application
      (bob, 0) bobResolution bob .bool _ _ rfl rfl
      (nodeView_eq_resolve rfl rfl) bob_ready
    · exact fits.withinDeadline
    · rfl
    · exact congrFun (legalFacts setup leaks horizon scheduler _ trace).remembered bobResolution
  change app.handle riskyBob.application bobMessage = some bobCompleted
  rw [(runtime setup).reactiveApplication_handle_of_current_token leaks _ bobMessage rfl]
  exact handled

def included (execution : app.Execution) (id : MessageId Player) : app.Execution :=
  { execution.includePending app id with
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .include id⟩] }

def bobAccepted : app.Execution := included bobSent (bob, 0)

theorem bob_lookup : bobSent.network.lookup (bob, 0) = some bobMessage := by
  obtain ⟨canonical⟩ := riskyBob_canonical_trace
  have facts := legalFacts setup leaks horizon scheduler _
    (canonicalMenu.toRawTrace (initialLaw setup) horizon scheduler canonical)
  exact (runtime setup).respond_submit_lookup leaks riskyBob bob
    ⟨.withhold bobResolution, none⟩ facts.serials

theorem bob_accepted_application : bobAccepted.application = bobCompleted := by
  change (bobSent.includePending app (bob, 0)).application = bobCompleted
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    bob_lookup, bob_handle, Option.getD_some]

theorem bob_receipt : ((bob, 0), true) ∈ bobAccepted.receipts := by
  change ((bob, 0), true) ∈ (bobSent.includePending app (bob, 0)).receipts
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    bob_lookup, bob_handle, Option.isSome_some]
  simp

theorem bob_completed_config : bobCompleted.config =
    (sampled1State.config.complete binding binding_ready (.success true) (.success true)).complete
      bobResolution (by decide) false .failure := by
  change riskyBob.application.config.complete bobResolution bob_ready false .failure = _
  have prior : riskyBob.application.config = sampled1State.config.complete binding binding_ready
      (.success true) (.success true) := by
    change riskyAccepted.application.config = _
    exact riskyAccepted_config
  simp only [prior]

theorem alice_ready : bobCompleted.config.cut.Ready aliceResolution := by
  rw [bob_completed_config]
  decide

def tick (execution : app.Execution) : app.Execution :=
  WaitRiskConfounding.advance (runtime setup) leaks execution

def bobTicked : app.Execution := tick (tick (tick (tick bobAccepted)))

def expireCompleted (execution : app.Execution) (event : nativeGraph.EventId) : app.Execution :=
  { execution with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .application (.expire event)⟩] }

def bobExpired : app.Execution := expireCompleted bobTicked bobResolution

def aliceInput : app.Execution :=
  WaitRiskConfounding.activate (runtime setup) leaks bobExpired alice

def aliceAction : app.Action :=
  ⟨some (disclosureSubmission (.opening aliceResolution (alice, .prepared 0) ⟨.bool, true⟩))⟩

def aliceSent : app.Execution := aliceInput.respond app alice aliceAction

def aliceCompleted : app.State :=
  aliceInput.application.complete aliceResolution
    (by change bobAccepted.application.config.cut.Ready aliceResolution
        rw [bob_accepted_application]; exact alice_ready) true (.success true)

theorem alice_clock : aliceInput.application.clock = 7 := by
  change bobAccepted.application.clock + 1 + 1 + 1 + 1 = 7
  rw [bob_accepted_application]
  change riskyBob.application.clock + 1 + 1 + 1 + 1 = 7
  rw [riskyBob_clock]

theorem alice_activated : aliceInput.application.activatedAt aliceResolution = some 3 := by
  obtain ⟨canonical⟩ := riskyBob_canonical_trace
  obtain ⟨inputs, invariant⟩ := (roster_trace_facts setup leaks horizon scheduler
    (canonicalMenu.toRawTrace (initialLaw setup) horizon scheduler canonical)).1
  have activation := State.complete_successor_activatedAt riskyBob.application invariant
    bobResolution aliceResolution bob_ready rfl rfl false .failure
  change bobAccepted.application.activatedAt aliceResolution = some 3
  rw [bob_accepted_application]
  exact activation.2.trans (congrArg some riskyBob_clock)

def aliceAccepted : app.Execution := included aliceSent (alice, 1)

def aliceMessage : Message Player (WitnessedPacket nativeGraph) :=
  ⟨(alice, 1), app.packet aliceSent.application alice (aliceInput.network.known alice)
    (disclosureSubmission (.opening aliceResolution (alice, .prepared 0) ⟨.bool, true⟩))⟩

theorem alice_handle : app.handle aliceSent.application aliceMessage = some aliceCompleted := by
  have handled : handle (runtime setup) aliceInput.application
      ⟨(alice, 1), .opening aliceResolution (alice, .prepared 0) ⟨.bool, true⟩⟩ =
      some aliceCompleted := by
    apply handle_opening_eq (runtime setup) aliceInput.application (alice, 1) aliceResolution
      (alice, .prepared 0) alice .bool _ _ rfl rfl (nodeView_eq_resolve rfl rfl)
      (by change bobAccepted.application.config.cut.Ready aliceResolution
          rw [bob_accepted_application]; exact alice_ready)
    · simp only [State.WithinDeadline, alice_activated, alice_clock]
      decide
    · rfl
    · rfl
    · change bobAccepted.application.accepted (.inr binding) = _
      rw [bob_accepted_application]
      exact riskyBob_accepted
    · change bobAccepted.application.candidates.lookup (alice, .prepared 0) = _
      rw [bob_accepted_application]
      exact riskyBob_candidate
    · change FieldRef.get? _ bobAccepted.application.config.store = _
      rw [bob_accepted_application, bob_completed_config]
      decide
    · change EventCode.resolveOutput? _ _ true bobAccepted.application.config.store = _
      rw [bob_accepted_application, bob_completed_config]
      decide
  change app.handle aliceInput.application aliceMessage = some aliceCompleted
  rw [(runtime setup).reactiveApplication_handle_of_current_token leaks
    aliceInput.application aliceMessage rfl]
  exact handled

theorem bobAccepted_trace : Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
    (some ⟨13, none, bobAccepted⟩)) := by
  obtain ⟨canonical⟩ := riskyBob_canonical_trace
  obtain ⟨sent⟩ := app.raw_trace_respond (initialLaw setup) horizon scheduler 14 riskyBob bob
    bobAction (canonicalMenu.toRawTrace (initialLaw setup) horizon scheduler canonical)
  apply app.raw_trace_environment (initialLaw setup) horizon scheduler 13 bobSent bobAccepted
    (.include (bob, 0)) sent
  · change _ ∈ (PMF.pure (.include (bob, 0) : app.Command)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

def publicationPlayers (who : Player) : app.Policy := fun _ _ =>
  PMF.pure (if who = alice then aliceAction else bobAction)

private theorem tick_round (execution : app.Execution)
    (selected : scheduler execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure (.application .advanceClock)) :
    app.round scheduler publicationPlayers execution = PMF.pure (tick execution) := by
  rw [ReactiveApplication.round, selected, PMF.pure_bind, ReactiveApplication.dispatch,
    WaitRiskConfounding.advance_law (runtime setup) leaks, PMF.pure_bind]
  rfl

private theorem expiry_round (execution : app.Execution) (event : nativeGraph.EventId)
    (selected : scheduler execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure (.application (.expire event)))
    (notReady : ¬execution.application.config.cut.Ready event) :
    app.round scheduler publicationPlayers execution = PMF.pure (expireCompleted execution event) :=
    by
  rw [ReactiveApplication.round, selected, PMF.pure_bind, ReactiveApplication.dispatch]
  change PMF.bind (PMF.map _ (PMF.map _
    (environmentStep (runtime setup) execution.application (.expire event)))) _ = _
  rw [environmentStep_expire_of_not_ready (runtime setup) _ event notReady,
    PMF.pure_map, PMF.pure_map, PMF.pure_bind]
  rfl

theorem aliceInput_trace : Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
    (some ⟨7, some alice, aliceInput⟩)) := by
  obtain ⟨accepted⟩ := bobAccepted_trace
  have ticks : app.runRounds scheduler publicationPlayers 4 bobAccepted = PMF.pure bobTicked := by
    rw [ReactiveApplication.runRounds, tick_round _ rfl, PMF.pure_bind,
      ReactiveApplication.runRounds, tick_round _ rfl, PMF.pure_bind,
      ReactiveApplication.runRounds, tick_round _ rfl, PMF.pure_bind,
      ReactiveApplication.runRounds, tick_round _ rfl, PMF.pure_bind]
    rfl
  obtain ⟨ticked⟩ := app.raw_trace_runRounds (initialLaw setup) horizon scheduler publicationPlayers
    9 4 bobAccepted bobTicked accepted (by rw [ticks]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have completed : bobResolution ∈ bobTicked.application.config.cut.completed := by
    change bobResolution ∈ bobAccepted.application.config.cut.completed
    rw [bob_accepted_application, bob_completed_config]
    decide
  have expired : app.round scheduler publicationPlayers bobTicked = PMF.pure bobExpired :=
    expiry_round _ _ rfl (fun ready => ready.1 completed)
  obtain ⟨expiry⟩ := app.raw_trace_round (initialLaw setup) horizon scheduler publicationPlayers 8
    bobTicked bobExpired ticked (by rw [expired]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  apply app.raw_trace_environment (initialLaw setup) horizon scheduler 7 bobExpired aliceInput
    (.activate alice) expiry
  · change _ ∈ (PMF.pure (.activate alice : app.Command)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [WaitRiskConfounding.activate_empty_law (runtime setup) leaks _ alice rfl]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem aliceInput_persistent_risk : (runtime setup).persistentServiceRisk leaks bound alice
    (aliceInput.recall alice) (aliceInput.observe app alice) = true := by
  apply (runtime setup).persistentServiceRisk_of_recalled leaks bound alice
  have recalled : aliceInput.recall alice = riskyBob.recall alice := rfl
  rw [recalled]
  exact riskyBob_submission_risk

theorem aliceInput_not_sourceCompatible : ¬service.sourceCompatibleInfo alice
    (some (aliceInput.recall alice, aliceInput.observe app alice)) := by
  intro compatible
  obtain ⟨past, view, same, _, clear⟩ := service.sourceCompatibleInfo_clear alice _ compatible
  obtain ⟨recallEq, viewEq⟩ := Prod.mk.inj (Option.some.inj same)
  rw [← recallEq, ← viewEq] at clear
  change (runtime setup).serviceRisk leaks bound alice (aliceInput.recall alice)
    (aliceInput.observe app alice) = false at clear
  have risky : (runtime setup).serviceRisk leaks bound alice (aliceInput.recall alice)
      (aliceInput.observe app alice) = true := by
    simp only [serviceRisk, aliceInput_persistent_risk, Bool.true_or]
  rw [risky] at clear
  cases clear

theorem alice_lookup : aliceSent.network.lookup (alice, 1) = some aliceMessage := by
  obtain ⟨trace⟩ := aliceInput_trace
  have serials := (legalFacts setup leaks horizon scheduler _ trace).serials
  change ((aliceInput.network.submit alice _).2).lookup (alice, 1) = some aliceMessage
  exact serials.lookup_submit alice _

theorem alice_accepted_application : aliceAccepted.application = aliceCompleted := by
  change (aliceSent.includePending app (alice, 1)).application = aliceCompleted
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    alice_lookup, alice_handle, Option.getD_some]

theorem alice_receipt : ((alice, 1), true) ∈ aliceAccepted.receipts := by
  change ((alice, 1), true) ∈ (aliceSent.includePending app (alice, 1)).receipts
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    alice_lookup, alice_handle, Option.isSome_some]
  simp

def aliceTicked : app.Execution := tick (tick (tick (tick (tick aliceAccepted))))

def finalExecution : app.Execution := expireCompleted aliceTicked aliceResolution

theorem final_config : finalExecution.application.config =
    ((sampled1State.config.complete binding binding_ready (.success true) (.success true)).complete
      bobResolution (by decide) false .failure).complete aliceResolution (by decide)
        true (.success true) := by
  change aliceAccepted.application.config = _
  rw [alice_accepted_application]
  change aliceInput.application.config.complete aliceResolution _ true (.success true) = _
  have prior : aliceInput.application.config =
      (sampled1State.config.complete binding binding_ready (.success true) (.success true)).complete
        bobResolution (by decide) false .failure := by
    change bobAccepted.application.config = _
    rw [bob_accepted_application, bob_completed_config]
  simp only [prior]

theorem final_terminal : finalExecution.application.config.cut.Terminal := by
  rw [final_config]
  decide

theorem alice_suffix_law : app.runRounds scheduler publicationPlayers 7
    (aliceInput.respond app alice aliceAction) = PMF.pure finalExecution := by
  have aliceIncluded : app.round scheduler publicationPlayers aliceSent =
      PMF.pure aliceAccepted := by
    have selected : scheduler aliceSent.environmentRecall (aliceSent.observeEnvironment app) =
        PMF.pure (.include (alice, 1)) := by
      unfold scheduler stageCommand reactiveLatest
      rfl
    rw [ReactiveApplication.round, selected, PMF.pure_bind, ReactiveApplication.dispatch]
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
    rfl
  have aliceNotReady : ¬aliceTicked.application.config.cut.Ready aliceResolution := by
    intro ready
    have done : aliceResolution ∈ aliceTicked.application.config.cut.completed := by
      change aliceResolution ∈ finalExecution.application.config.cut.completed
      rw [final_config]
      decide
    exact ready.1 done
  change app.runRounds scheduler publicationPlayers 7 aliceSent = _
  rw [ReactiveApplication.runRounds, aliceIncluded, PMF.pure_bind,
    ReactiveApplication.runRounds, tick_round _ rfl, PMF.pure_bind,
    ReactiveApplication.runRounds, tick_round _ rfl, PMF.pure_bind,
    ReactiveApplication.runRounds, tick_round _ rfl, PMF.pure_bind,
    ReactiveApplication.runRounds, tick_round _ rfl, PMF.pure_bind,
    ReactiveApplication.runRounds, tick_round _ rfl, PMF.pure_bind]
  change app.runRounds scheduler publicationPlayers 1 aliceTicked = _
  rw [ReactiveApplication.runRounds, expiry_round _ _ rfl aliceNotReady, PMF.pure_bind]
  rfl

theorem suffix_law : app.runRounds scheduler publicationPlayers 14 bobSent =
    PMF.pure finalExecution := by
  have bobIncluded : app.round scheduler publicationPlayers bobSent = PMF.pure bobAccepted := by
    have selected : scheduler bobSent.environmentRecall (bobSent.observeEnvironment app) =
        PMF.pure (.include (bob, 0)) := rfl
    rw [ReactiveApplication.round, selected, PMF.pure_bind, ReactiveApplication.dispatch]
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
    rfl
  have bobNotReady : ¬bobTicked.application.config.cut.Ready bobResolution := by
    intro ready
    have done : bobResolution ∈ bobTicked.application.config.cut.completed := by
      change bobResolution ∈ bobAccepted.application.config.cut.completed
      rw [bob_accepted_application, bob_completed_config]
      decide
    exact ready.1 done
  have activateAlice : app.round scheduler publicationPlayers bobExpired =
      PMF.pure aliceSent := by
    have selected : scheduler bobExpired.environmentRecall (bobExpired.observeEnvironment app) =
        PMF.pure (.activate alice) := rfl
    rw [ReactiveApplication.round, selected, PMF.pure_bind, ReactiveApplication.dispatch,
      WaitRiskConfounding.activate_empty_law (runtime setup) leaks _ alice rfl, PMF.pure_bind]
    change (publicationPlayers alice (aliceInput.recall alice) (aliceInput.observe app alice)).map
      (aliceInput.respond app alice) = _
    simp only [publicationPlayers, ite_true, PMF.pure_map]
    rfl
  rw [ReactiveApplication.runRounds, bobIncluded, PMF.pure_bind,
    ReactiveApplication.runRounds, tick_round _ rfl, PMF.pure_bind,
    ReactiveApplication.runRounds, tick_round _ rfl, PMF.pure_bind,
    ReactiveApplication.runRounds, tick_round _ rfl, PMF.pure_bind,
    ReactiveApplication.runRounds, tick_round _ rfl, PMF.pure_bind]
  change app.runRounds scheduler publicationPlayers 9 bobTicked = _
  rw [ReactiveApplication.runRounds, expiry_round _ _ rfl bobNotReady, PMF.pure_bind]
  change app.runRounds scheduler publicationPlayers 8 bobExpired = _
  rw [ReactiveApplication.runRounds, activateAlice, PMF.pure_bind]
  exact alice_suffix_law

theorem final_trace : Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
    (app.finished finalExecution)) := by
  obtain ⟨canonical⟩ := riskyBob_canonical_trace
  obtain ⟨sent⟩ := app.raw_trace_respond (initialLaw setup) horizon scheduler 14 riskyBob bob
    bobAction (canonicalMenu.toRawTrace (initialLaw setup) horizon scheduler canonical)
  exact app.raw_trace_runRounds (initialLaw setup) horizon scheduler publicationPlayers 0 14
    bobSent finalExecution sent (by rw [suffix_law]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)

def terminalSource : State simpleExpr setup.program.terminalCtx :=
  Env.cons (.success true) (Env.cons .failure (Env.cons (.success true)
    (Env.cons true (Env.cons true sourceInitial))))

theorem final_readout : sourceReadout setup leaks (app.finished finalExecution) =
    some terminalSource := by
  change sourceReadout setup leaks (some ⟨0, none, finalExecution⟩) = _
  rw [sourceReadout_eq_decode]
  change decodeState? (terminalRefs setup.program) finalExecution.application.config.store = _
  rw [final_config]
  apply decodeState?_eq_some
  intro name cell read
  rcases read with _ | read
  · change (_ : Option (PublicationResult Bool)) = some (.success true)
    rfl
  rcases read with _ | read
  · change (_ : Option (PublicationResult Bool)) = some .failure
    rfl
  rcases read with _ | read
  · change (_ : Option (PublicationResult Bool)) = some (.success true)
    rfl
  rcases read with _ | read
  · change (_ : Option Bool) = some true
    rfl
  rcases read with _ | read
  · change (_ : Option Bool) = some true
    rfl
  rcases read with _ | read
  · change (_ : Option (PublicationResult Bool)) = some (.success true)
    rfl
  nomatch read

theorem final_public_outcome : (sourceReadout setup leaks (app.finished finalExecution)).map
      (SourceProgram.publicOutcome setup.program) =
    some (Env.cons (.success true) (Env.cons .failure
      (Env.cons true (Env.cons true (Env.empty _))))) := by
  rw [final_readout]
  rfl

theorem alice_certified : certifiedOpening aliceMessage.payload = true := by
  change certifiedOpening ((disclosureSubmission
    (.opening aliceResolution (alice, .prepared 0) ⟨.bool, true⟩)).emit aliceSent.application alice
      (aliceInput.network.known alice)) = true
  apply disclosureSubmission_certified _ _ _ _ _ _ rfl
  change bobAccepted.application.candidates.lookup (alice, .prepared 0) = _
  rw [bob_accepted_application]
  exact riskyBob_candidate

theorem alice_guard : finalExecution.application.publicView.openingGuardsAccepted
    aliceMessage.payload = true := by
  change finalExecution.application.publicView.openingGuardsAccepted
    ⟨.opening aliceResolution (alice, .prepared 0) ⟨.bool, true⟩, _, _⟩ = true
  simp only [PublicView.openingGuardsAccepted, State.publicView]
  simp only [final_config]
  decide

private theorem include_inputs (execution : app.Execution) (id : MessageId Player) :
    (included execution id).network.inputs = execution.network.inputs := by
  change (execution.includePending app id).network.inputs = execution.network.inputs
  rw [app.includePending_network]
  unfold MessageNetwork.includePending
  cases execution.network.lookup id <;> rfl

theorem final_inputs : finalExecution.network.inputs = [bindingMessage, bobMessage, aliceMessage] :=
    by
  change aliceAccepted.network.inputs = _
  change (included aliceSent (alice, 1)).network.inputs = _
  rw [include_inputs]
  change List.append bobAccepted.network.inputs [aliceMessage] = _
  change List.append (included bobSent (bob, 0)).network.inputs [aliceMessage] = _
  rw [include_inputs]
  change List.append (List.append riskyBob.network.inputs [bobMessage]) [aliceMessage] = _
  have first : riskyBob.network.inputs = [bindingMessage] := by
    change riskyAccepted.network.inputs = _
    change (includedExecution riskySubmitted).network.inputs = _
    change (riskySubmitted.includePending app (alice, 0)).network.inputs = _
    rw [app.includePending_network]
    simp only [MessageNetwork.includePending, binding_lookup]
    rfl
  rw [first]
  rfl

theorem final_binding_receipt : ((alice, 0), true) ∈ finalExecution.receipts := by
  change ((alice, 0), true) ∈ aliceAccepted.receipts
  change ((alice, 0), true) ∈ (aliceSent.includePending app (alice, 1)).receipts
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    alice_lookup, alice_handle, Option.isSome_some]
  apply List.mem_append_left
  change ((alice, 0), true) ∈ bobAccepted.receipts
  change ((alice, 0), true) ∈ (bobSent.includePending app (bob, 0)).receipts
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    bob_lookup, bob_handle, Option.isSome_some]
  apply List.mem_append_left
  change ((alice, 0), true) ∈ riskyAccepted.receipts
  change ((alice, 0), true) ∈ (riskySubmitted.includePending app (alice, 0)).receipts
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    binding_lookup, binding_handle, Option.isSome_some]
  simp

theorem final_misses : finalExecution.application.missedEvents = ∅ := by
  change aliceAccepted.application.missedEvents = _
  rw [alice_accepted_application]
  change bobAccepted.application.missedEvents = _
  rw [bob_accepted_application]
  change riskyAccepted.application.missedEvents = _
  rw [← accepted_application_eq]
  exact cleanAccepted_missedEvents

theorem final_alice_permitted (record : app.TrafficRecord)
    (present : record ∈ app.executionTraffic finalExecution)
    (authored : record.envelope.sender = alice) :
    ((runtime setup).settledRecord leaks finalExecution).permits record.envelope = true := by
  obtain ⟨trace⟩ := final_trace
  have inputs := app.stateTraffic_inputs (initialLaw setup) horizon scheduler trace
  change (app.executionTraffic finalExecution).map ReactiveApplication.TrafficRecord.envelope =
    finalExecution.network.inputs at inputs
  have packet : record.envelope ∈ [bindingMessage, bobMessage, aliceMessage] := by
    rw [← final_inputs, ← inputs]
    exact List.mem_map.mpr ⟨record, present, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at packet
  rcases packet with bindingPacket | bobPacket | opening
  · rw [bindingPacket]
    apply SettledRecord.permits_of_accepted _ _ binding rfl
    · exact final_binding_receipt
    · refine ⟨rfl, ?_⟩
      have counted : finalExecution.application.publicView.bindingCountBefore alice binding = 0 :=
          by
        simp only [PublicView.bindingCountBefore, State.publicView]
        rw [final_config]
        decide
      change (alice, Slot.prepared 0) = (alice, Slot.prepared
        (finalExecution.application.publicView.bindingCountBefore alice binding))
      rw [counted]
  · rw [bobPacket] at authored
    cases (by decide : bobMessage.sender ≠ alice) authored
  · rw [opening]
    apply SettledRecord.permits_of_accepted _ _ aliceResolution rfl
    · change ((alice, 1), true) ∈ aliceAccepted.receipts
      exact alice_receipt
    · exact ⟨alice_certified, alice_guard⟩

theorem final_audit_charge
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    GameTheory.Enforcement.TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) (app.finished finalExecution) alice = 0 := by
  unfold sourceServiceAudit
  change GameTheory.Enforcement.TerminalAudit.charge
    ((runtime setup).serviceAuditObservation leaks) _ (some ⟨0, none, finalExecution⟩) alice = 0
  rw [(runtime setup).serviceAudit_charge]
  have clear := PublicView.missedDecisionBy_clear finalExecution.application.publicView
    final_misses alice
  rw [clear]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply app.sampledTrafficAudit_sound
  · exact authentic _
  · intro record present authored
    exact final_alice_permitted record present authored

def displayedUtility (source : State simpleExpr setup.program.terminalCtx) (who : Player) : ℝ :=
  if who = alice then if (source.get .here).isSuccess then 1 else 0 else 0

theorem displayed_payoff (source : State simpleExpr setup.program.terminalCtx) :
    ((setup.program.evaluatePayoffs source).lookup alice).getD 0 =
      if (source.get .here).isSuccess then 1 else 0 := by
  rfl

def auditedUtility
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : ℝ) : app.ProtocolState → Player → ℝ :=
  GameTheory.Enforcement.TerminalAudit.utility (baseUtility setup leaks displayedUtility)
    ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
    (fun _ => deposit)

theorem final_utility
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) : auditedUtility sample deposit (app.finished finalExecution) alice = 1 := by
  unfold auditedUtility GameTheory.Enforcement.TerminalAudit.utility
  rw [final_audit_charge sample authentic]
  simp only [zero_mul, sub_zero, baseUtility, final_readout, Option.elim_some]
  rfl

theorem displayedUtility_mem_Icc (source : State simpleExpr setup.program.terminalCtx)
    (who : Player) : displayedUtility source who ∈ Set.Icc 0 1 := by
  unfold displayedUtility
  split <;> try norm_num
  split <;> norm_num

theorem auditedUtility_le_one
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : ℝ) (nonnegative : 0 ≤ deposit) (state : app.ProtocolState) (who : Player) :
    auditedUtility sample deposit state who ≤ 1 := by
  have base : baseUtility setup leaks displayedUtility state who ≤ 1 := by
    unfold baseUtility
    cases sourceReadout setup leaks state with
    | none => norm_num
    | some source => exact (displayedUtility_mem_Icc source who).2
  have charge := (GameTheory.Enforcement.TerminalAudit.charge_mem_Icc
    ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
      state who).1
  unfold auditedUtility GameTheory.Enforcement.TerminalAudit.utility
  exact (sub_le_self _ (mul_nonneg charge nonnegative)).trans base

theorem continuation_value
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) :
    expect ((app.runRounds scheduler publicationPlayers 14 bobSent).map app.finished)
      (fun state => auditedUtility sample deposit state alice) = 1 := by
  rw [suffix_law, PMF.pure_map, expect_pure, final_utility sample authentic]

theorem alice_true_value
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) :
    expect ((app.runRounds scheduler publicationPlayers 7
        (aliceInput.respond app alice aliceAction)).map app.finished)
      (fun state => auditedUtility sample deposit state alice) = 1 := by
  rw [alice_suffix_law, PMF.pure_map, expect_pure, final_utility sample authentic]

private theorem auditedUtility_integrable
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : ℝ) (nonnegative : 0 ≤ deposit) (law : PMF app.ProtocolState) :
    PayoffIntegrable law (fun state => auditedUtility sample deposit state alice) := by
  apply payoffIntegrable_of_bounded _ _ (C := 1 + deposit)
  intro state
  have base : baseUtility setup leaks displayedUtility state alice ∈ Set.Icc 0 1 := by
    unfold baseUtility
    cases sourceReadout setup leaks state with
    | none => norm_num
    | some source => exact displayedUtility_mem_Icc source alice
  have charge := GameTheory.Enforcement.TerminalAudit.charge_mem_Icc
    ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
      state alice
  have lower := mul_le_mul_of_nonneg_right charge.2 nonnegative
  have upper := auditedUtility_le_one sample deposit nonnegative state alice
  apply abs_le.mpr
  constructor
  · unfold auditedUtility GameTheory.Enforcement.TerminalAudit.utility
    linarith [base.1]
  · linarith

theorem no_larger_displayed_value
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : ℝ) (nonnegative : 0 ≤ deposit) (law : PMF app.ProtocolState) :
    expect law (fun state => auditedUtility sample deposit state alice) ≤ 1 := by
  exact expect_le_const law _ (auditedUtility_integrable sample deposit nonnegative law) 1
    (fun state _ => auditedUtility_le_one sample deposit nonnegative state alice)

def partialSample (rate : ℝ) (nonnegative : 0 ≤ rate) (small : rate ≤ 1)
    (actual : List (SettledEvidence setup)) : PMF (List (SettledEvidence setup)) :=
  mix rate nonnegative small (PMF.pure actual) (PMF.pure [])

theorem partialSample_authentic (rate : ℝ) (nonnegative : 0 ≤ rate) (small : rate ≤ 1)
    (actual observed : List (SettledEvidence setup))
    (supported : observed ∈ (partialSample rate nonnegative small actual).support) :
    observed ⊆ actual := by
  rcases support_mix_subset rate nonnegative small _ _ supported with all | empty
  · cases (PMF.mem_support_pure_iff _ _).mp all
    exact List.Subset.refl _
  · cases (PMF.mem_support_pure_iff _ _).mp empty
    exact List.nil_subset _

theorem partialSample_zero_charge (rate : ℝ) (nonnegative : 0 ≤ rate) (small : rate ≤ 1) :
    GameTheory.Enforcement.TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks (partialSample rate nonnegative small))
        (app.finished finalExecution) alice = 0 :=
  final_audit_charge _ (partialSample_authentic rate nonnegative small)

def publishingProfile : BehavioralProfile setup.program := fun _ =>
  (fun _ _ => PMF.pure (.success true),
    (fun _ _ => PMF.pure false, (fun _ _ => PMF.pure true, PUnit.unit)))

theorem publishing_admitted (who : Player) :
    (publishingProfile who).Admitted setup.program (CommitmentInterface.values setup.program) := by
  dsimp only [publishingProfile, BehavioralPolicy.Admitted, CommitmentInterface.values,
    setup, program]
  refine ⟨?_, trivial⟩
  intro own view choice supported
  cases (PMF.mem_support_pure_iff _ _).mp supported
  trivial

theorem publishing_source_law : SourceProgram.run setup.program publishingProfile sourceInitial =
    PMF.pure terminalSource := by
  simp only [SourceProgram.run, setup, program, runWith, IExpr.evalDist, simpleExpr,
    evalLawDistExpr, RationalLaw.denote_pure, publishingProfile, afterSample, commitKernel,
    revealKernel, afterCommit, afterReveal, PMF.pure_bind]
  rfl

theorem continuation_source_outcome :
    (app.runRounds scheduler publicationPlayers 14 bobSent).map
        (fun execution => (sourceReadout setup leaks (app.finished execution)).map
          (SourceProgram.publicOutcome setup.program)) =
      (SourceProgram.run setup.program publishingProfile sourceInitial).map
        (fun source => some (SourceProgram.publicOutcome setup.program source)) := by
  rw [suffix_law, publishing_source_law, PMF.pure_map, PMF.pure_map, final_readout]
  rfl

end Vegas.OpaqueBindingFork.Publication
