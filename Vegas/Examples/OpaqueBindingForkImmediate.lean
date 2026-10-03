/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.OpaqueBindingForkSites
import Vegas.Game.SourceServiceFirstTurnCalls

/-! # Immediate acceptance and the later Bob input -/

noncomputable section

namespace Vegas.OpaqueBindingFork

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

def immediateSubmitted : app.Execution := firstAliceExecution.respond app alice bindingResponse

def immediateAccepted : app.Execution := includedExecution immediateSubmitted

theorem immediateAccepted_config : immediateAccepted.application.config =
    sampled1State.config.complete binding binding_ready
      (cast (congrArg EventField.Action binding_output.symm) (.success true))
      (cast (congrArg EventField.Value binding_output.symm) (.success true)) := by
  have unused : firstAliceExecution.application.HandleUnused (alice, .prepared 0) := by
    intro field associated
    change initialState.accepted field = some (alice, .prepared 0) at associated
    obtain ⟨input, owner, payload, _, _, same⟩ :=
      State.initial_accepted_eq_some (graph := nativeGraph) (setup.eventInputs sourceInitial) field
        (alice, .prepared 0) associated
    cases congrArg Prod.snd same
  let players : Player → app.Policy := fun _ => app.silentPolicy
  let network : (runtime setup).NetworkPolicy leaks := fun _ _ => PMF.pure .wait
  have realized := (runtime setup).rawBinding_reserved_config leaks firstAliceExecution alice
    binding .bool binding_output binding_code binding_node 0 (some ⟨.bool, true⟩)
    binding_ready (by change 0 - 0 < 3; decide) rfl rfl unused
    MessageNetwork.SerialsBeforeNext.empty players network
  dsimp only at realized
  rw [(runtime setup).rawBinding_reserved_selection leaks firstAliceExecution alice binding 0
    (some ⟨.bool, true⟩) MessageNetwork.SerialsBeforeNext.empty players network] at realized
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at realized
  have endpoint := congrArg PMF.support realized
  simp only [PMF.support_pure] at endpoint
  exact congrArg Prod.fst (Set.singleton_injective endpoint)

private theorem included_bob_entered (execution : app.Execution)
    (absent : execution.application.activatedAt bobResolution = none)
    (notReady : ¬execution.application.config.cut.Ready bobResolution)
    (ready : (includedExecution execution).application.config.cut.Ready bobResolution) :
    (includedExecution execution).application.activatedAt bobResolution =
      some execution.application.clock := by
  unfold includedExecution ReactiveApplication.Execution.includePending
    MessageNetwork.includePending at ready ⊢
  cases found : execution.network.lookup (alice, 0) with
  | none => simp only [found] at ready; exact (notReady ready).elim
  | some message =>
      simp only [found] at ready ⊢
      cases handled : app.handle execution.application message with
      | none =>
          simp only [handled, Option.getD_none] at ready
          exact (notReady ready).elim
      | some next =>
          simp only [handled, Option.getD_some] at ready ⊢
          have metadata := handle_clock_activated (runtime setup) execution.application next
            ⟨message.id, message.payload.call⟩ (reactiveHandle_call handled)
          rw [metadata.2]
          simp only [State.refreshActivated, dite_eq_left ready, bobResolution_actor, absent]
          rfl

/-- Alice's immediate packet completes the binding at clock zero. -/
theorem immediateAccepted_bob_entered :
    immediateAccepted.application.activatedAt bobResolution = some 0 := by
  apply included_bob_entered immediateSubmitted rfl
  · change ¬sampled1State.config.cut.Ready bobResolution
    decide
  · change immediateAccepted.application.config.cut.Ready bobResolution
    rw [immediateAccepted_config]
    decide

theorem cleanAccepted_bob_entered : cleanAccepted.application.activatedAt bobResolution =
    some 1 := by
  rw [accepted_application_eq]
  apply included_bob_entered riskySubmitted rfl
  · change ¬sampled1State.config.cut.Ready bobResolution
    decide
  · change riskyAccepted.application.config.cut.Ready bobResolution
    rw [riskyAccepted_config]
    decide

/-- The clean ordering of the later scheduler coin: an irrelevant Alice
activation, the paired tick, the empty inclusion, two ticks and completed expiry. -/
def immediateSecond : app.Execution :=
  (WaitRiskConfounding.activate (runtime setup) leaks immediateAccepted alice).respond app alice
    ⟨none⟩

def immediateTicked : app.Execution :=
  WaitRiskConfounding.advance (runtime setup) leaks immediateSecond

def immediateEmptyInclude : app.Execution :=
  { immediateTicked with environmentRecall := immediateTicked.environmentRecall ++
      [⟨immediateTicked.observeEnvironment app, .wait⟩] }

def immediateTick1 : app.Execution :=
  WaitRiskConfounding.advance (runtime setup) leaks immediateEmptyInclude

def immediateBeforeExpiry : app.Execution :=
  WaitRiskConfounding.advance (runtime setup) leaks immediateTick1

def immediateAfterExpiry : app.Execution := expiredExecution immediateBeforeExpiry

def immediateBob : app.Execution :=
  WaitRiskConfounding.activate (runtime setup) leaks immediateAfterExpiry bob

theorem immediateBob_entered : immediateBob.application.activatedAt bobResolution = some 0 :=
  immediateAccepted_bob_entered

theorem cleanBob_entered : cleanBob.application.activatedAt bobResolution = some 1 :=
  cleanAccepted_bob_entered

/-- The current public activation table already excludes the immediate path
from this later Bob information fiber, even before inspecting his recall. -/
theorem immediateBob_input_ne_clean : (immediateBob.recall bob, immediateBob.observe app bob) ≠
    (cleanBob.recall bob, cleanBob.observe app bob) := by
  intro same
  have metadata := congrArg (fun input : List app.PlayerEntry × app.PlayerView =>
    input.2.application.publicView.activatedAt bobResolution) same
  change immediateBob.application.activatedAt bobResolution =
    cleanBob.application.activatedAt bobResolution at metadata
  rw [immediateBob_entered, cleanBob_entered] at metadata
  cases metadata

theorem immediateBob_input_ne_risky : (immediateBob.recall bob, immediateBob.observe app bob) ≠
    (riskyBob.recall bob, riskyBob.observe app bob) := by
  rw [← bob_input_eq]
  exact immediateBob_input_ne_clean

/-- The actual source policy chooses Alice's canonical true binding at her first input. -/
def immediatePlayers : Player → app.Policy :=
  sourceServiceTurnPolicy setup leaks bound 1 (firstTurnTiming setup 1) sourceProfile

theorem immediate_first_response : immediatePlayers alice (firstAliceExecution.recall alice)
    (firstAliceExecution.observe app alice) = PMF.pure bindingResponse := by
  rw [immediatePlayers, sourceServiceTurnPolicy_firstTurn binding_actor (by rfl)]
  have canonical : (runtime setup).canonicalServiceDecision leaks alice
      (firstAliceExecution.recall alice) (firstAliceExecution.observe app alice)
      binding (.success true) = bindingResponse := by
    apply (runtime setup).canonicalServiceDecision_binding leaks alice _ _ binding .bool
      binding_output binding_code binding_node 0
    have counted : (firstAliceExecution.observe app alice).application.publicView.bindingCount
        alice = 0 := by decide
    rw [← counted]
    exact canonicalFreshSlot_canonical alice _ (by rfl)
  have policy : sourceServiceCanonicalPolicy setup leaks sourceProfile alice
      (firstAliceExecution.recall alice) (firstAliceExecution.observe app alice) =
        PMF.pure bindingResponse := by
    rw [sourceServiceCanonicalPolicy_at_event setup leaks sourceProfile alice firstAliceExecution
      binding binding_turn binding_actor]
    change ((compileEventProfile setup.program sourceProfile) alice binding binding_actor
      (setup.eventGraph.fromModeObservation .sequential alice
        ((graph setup).playerObserve alice sampled1Execution.application.config))).map _ = _
    rw [compiled_binding_true, PMF.pure_map]
    exact congrArg PMF.pure canonical
  have unrecorded : (runtime setup).eventRecorded leaks (firstAliceExecution.recall alice)
      binding = false := rfl
  have fits : (firstAliceExecution.observe app alice).application.publicView.InclusionFitsDeadline
      (runtime setup) bound binding := by change 0 - 0 + 2 < 3; decide
  simp only [sourceServiceCanonicalOpportunity, unrecorded, Bool.false_eq_true, ite_false,
    ite_eq_left fits, policy, PMF.pure_bind]
  rfl

private theorem immediate_initial_law : initialLaw setup = PMF.pure initialState := by
  rw [initialLaw_eq_inputs]
  change ((PMF.pure sourceInitial).map setup.eventInputs).map
    (State.initial (graph := nativeGraph)) = _
  rw [PMF.pure_map, PMF.pure_map]
  rfl

/-- The first accepted packet is reached by the actual initialized first-turn policy. -/
theorem immediatePlayers_rounds4 : app.roundsFrom (initialLaw setup) scheduler immediatePlayers 4 =
    PMF.pure immediateAccepted := by
  have zero : app.roundsFrom (initialLaw setup) scheduler immediatePlayers 0 =
      PMF.pure initialExecution := by
    simp only [ReactiveApplication.roundsFrom, immediate_initial_law, PMF.pure_bind,
      ReactiveApplication.runRounds]
    rfl
  have first : app.round scheduler immediatePlayers initialExecution =
      PMF.pure sampled0Execution := by
    change (PMF.pure (.application (.executeSample sample0) : app.Command)).bind _ = _
    rw [PMF.pure_bind, ReactiveApplication.dispatch, sampled0_environment, PMF.pure_bind]
    rfl
  have second : app.round scheduler immediatePlayers sampled0Execution =
      PMF.pure sampled1Execution := by
    change (PMF.pure (.application (.executeSample sample1) : app.Command)).bind _ = _
    rw [PMF.pure_bind, ReactiveApplication.dispatch, sampled1_environment, PMF.pure_bind]
    rfl
  have submitted : app.round scheduler immediatePlayers sampled1Execution =
      PMF.pure immediateSubmitted := by
    change (PMF.pure (.activate alice : app.Command)).bind _ = _
    rw [PMF.pure_bind, ReactiveApplication.dispatch,
      WaitRiskConfounding.activate_empty_law (runtime setup) leaks _ alice rfl, PMF.pure_bind]
    change (immediatePlayers alice (firstAliceExecution.recall alice)
      (firstAliceExecution.observe app alice)).map _ = _
    rw [immediate_first_response, PMF.pure_map]
    rfl
  have accepted : app.round scheduler immediatePlayers immediateSubmitted =
      PMF.pure immediateAccepted := by
    change (PMF.pure (.include (alice, 0) : app.Command)).bind _ = _
    simp only [PMF.pure_bind, ReactiveApplication.dispatch,
      ReactiveApplication.Execution.environmentStep, PMF.pure_map]
    rfl
  rw [app.roundsFrom_succ (initialLaw setup) scheduler immediatePlayers 3,
    app.roundsFrom_succ (initialLaw setup) scheduler immediatePlayers 2,
    app.roundsFrom_succ (initialLaw setup) scheduler immediatePlayers 1,
    app.roundsFrom_succ (initialLaw setup) scheduler immediatePlayers 0,
    zero, PMF.pure_bind, first, PMF.pure_bind, second, PMF.pure_bind,
    submitted, PMF.pure_bind, accepted]

private theorem immediate_second_idle : immediatePlayers alice
    ((WaitRiskConfounding.activate (runtime setup) leaks immediateAccepted alice).recall alice)
    ((WaitRiskConfounding.activate (runtime setup) leaks immediateAccepted alice).observe
      app alice) =
      PMF.pure ⟨none⟩ := by
  apply sourceServiceTurnPolicy_idle
  change immediateAccepted.application.publicView.Idle alice
  intro event ready
  have current : immediateAccepted.application.config.cut.Ready bobResolution := by
    rw [immediateAccepted_config]
    decide
  have same := setup.eventGraph.sequentialize_ready_unique
    immediateAccepted.application.config.cut
    ((immediateAccepted.application.publicView_eventReady event).mp ready) current
  subst event
  exact (by decide : nativeGraph.actor? bobResolution ≠ some alice)

private theorem next_immediate_round (count : Nat) (before after : app.Execution)
    (prior : before ∈ (app.roundsFrom (initialLaw setup) scheduler immediatePlayers count).support)
    (command : app.Command)
    (selected : command ∈ (scheduler before.environmentRecall
      (before.observeEnvironment app)).support)
    (dispatched : after ∈ (app.dispatch immediatePlayers command before).support) :
    after ∈ (app.roundsFrom (initialLaw setup) scheduler immediatePlayers (count + 1)).support := by
  rw [app.roundsFrom_succ, PMF.support_bind]
  apply Set.mem_iUnion₂.mpr
  refine ⟨before, prior, ?_⟩
  rw [ReactiveApplication.round, PMF.support_bind]
  exact Set.mem_iUnion₂.mpr ⟨command, selected, dispatched⟩

theorem immediateBob_roundSupported : app.RoundSupported (initialLaw setup) horizon scheduler
    immediatePlayers (some ⟨14, some bob, immediateBob⟩) := by
  have accepted : immediateAccepted ∈
      (app.roundsFrom (initialLaw setup) scheduler immediatePlayers 4).support := by
    rw [immediatePlayers_rounds4]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have second : immediateSecond ∈
      (app.roundsFrom (initialLaw setup) scheduler immediatePlayers 5).support := by
    apply next_immediate_round 4 immediateAccepted immediateSecond accepted (.activate alice)
    · change _ ∈ (mix (1 / 2) (by norm_num) (by norm_num)
        (PMF.pure (.activate alice)) (PMF.pure (.application .advanceClock : app.Command))).support
      exact mem_support_mix_left _ _ _ (by norm_num) ((PMF.mem_support_pure_iff _ _).mpr rfl)
    · rw [ReactiveApplication.dispatch,
        WaitRiskConfounding.activate_empty_law (runtime setup) leaks _ alice rfl, PMF.pure_bind]
      change _ ∈ ((immediatePlayers alice
        ((WaitRiskConfounding.activate (runtime setup) leaks immediateAccepted alice).recall alice)
        ((WaitRiskConfounding.activate (runtime setup) leaks immediateAccepted alice).observe
          app alice)).map _).support
      rw [immediate_second_idle, PMF.pure_map]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have ticked : immediateTicked ∈
      (app.roundsFrom (initialLaw setup) scheduler immediatePlayers 6).support := by
    apply next_immediate_round 5 immediateSecond immediateTicked second (.application .advanceClock)
    · exact (PMF.mem_support_pure_iff _ _).mpr rfl
    · rw [ReactiveApplication.dispatch, WaitRiskConfounding.advance_law (runtime setup) leaks,
        PMF.pure_bind]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have empty : immediateEmptyInclude ∈
      (app.roundsFrom (initialLaw setup) scheduler immediatePlayers 7).support := by
    apply next_immediate_round 6 immediateTicked immediateEmptyInclude ticked .wait
    · exact (PMF.mem_support_pure_iff _ _).mpr rfl
    · change _ ∈ ((immediateTicked.environmentStep app .wait).bind _).support
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have tick1 : immediateTick1 ∈
      (app.roundsFrom (initialLaw setup) scheduler immediatePlayers 8).support := by
    apply next_immediate_round 7 immediateEmptyInclude immediateTick1 empty
      (.application .advanceClock)
    · exact (PMF.mem_support_pure_iff _ _).mpr rfl
    · rw [ReactiveApplication.dispatch, WaitRiskConfounding.advance_law (runtime setup) leaks,
        PMF.pure_bind]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have beforeExpiry : immediateBeforeExpiry ∈
      (app.roundsFrom (initialLaw setup) scheduler immediatePlayers 9).support := by
    apply next_immediate_round 8 immediateTick1 immediateBeforeExpiry tick1
      (.application .advanceClock)
    · exact (PMF.mem_support_pure_iff _ _).mpr rfl
    · rw [ReactiveApplication.dispatch, WaitRiskConfounding.advance_law (runtime setup) leaks,
        PMF.pure_bind]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have noReady : ¬immediateBeforeExpiry.application.config.cut.Ready binding := by
    have completed : binding ∈ immediateAccepted.application.config.cut.completed := by
      rw [immediateAccepted_config]
      decide
    exact fun ready => ready.1 completed
  have expiry : immediateBeforeExpiry.environmentStep app (.application (.expire binding)) =
      PMF.pure immediateAfterExpiry := by
    change ((environmentStep (runtime setup) immediateBeforeExpiry.application
      (.expire binding)).map
      _).map _ = _
    rw [environmentStep_expire_of_not_ready (runtime setup) _ binding noReady,
      PMF.pure_map, PMF.pure_map]
    rfl
  have afterExpiry : immediateAfterExpiry ∈
      (app.roundsFrom (initialLaw setup) scheduler immediatePlayers 10).support := by
    apply next_immediate_round 9 immediateBeforeExpiry immediateAfterExpiry beforeExpiry
      (.application (.expire binding))
    · exact (PMF.mem_support_pure_iff _ _).mpr rfl
    · rw [ReactiveApplication.dispatch, expiry, PMF.pure_bind]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
  refine ⟨by change 11 + 14 = 25; rfl, 10, immediateAfterExpiry, .activate bob, rfl,
    afterExpiry, ?_, rfl, ?_⟩
  · exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [WaitRiskConfounding.activate_empty_law (runtime setup) leaks _ bob rfl]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

end Vegas.OpaqueBindingFork
