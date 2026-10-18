/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastInitialFrameSeedPosterior
import Vegas.Examples.CommitSeedBroadcastAudit
import Interaction.ReactiveScheduleEvaluation
import Interaction.ReactiveLocalContinuation

/-! # The prepared physical frame at its exact original protocol depth -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

private theorem initial_common_command (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (command : app.Command)
    (common : ∀ seed, family seed past view = PMF.pure command) :
    scheduler past view = PMF.pure command := by
  rw [scheduler_eq_posterior]
  have chooseEq : (fun seed => choose seed past view) = fun _ => command := by
    funext seed
    have produced : choose seed past view ∈ (family seed past view).support :=
      (PMF.mem_support_pure_iff _ _).mpr rfl
    rw [common seed] at produced
    exact (PMF.mem_support_pure_iff _ _).mp produced
  rw [chooseEq]
  exact PMF.map_const _ _

private theorem initial_mixed_alice :
    scheduler initialExecution.environmentRecall (initialExecution.observeEnvironment app) =
      PMF.pure (.activate alice) :=
  initial_common_command _ _ _ initial_alice_choice

private theorem initial_mixed_bob (first : app.Action) :
    scheduler (initialAliceCallback.respond app alice first).environmentRecall
      ((initialAliceCallback.respond app alice first).observeEnvironment app) =
        PMF.pure (.activate bob) :=
  initial_common_command _ _ _ (fun seed => initial_bob_choice seed first)

private theorem initial_mixed_carol (first second : app.Action) :
    scheduler ((initialBobCallback first).respond app bob second).environmentRecall
      (((initialBobCallback first).respond app bob second).observeEnvironment app) =
        PMF.pure (.activate carol) :=
  initial_common_command _ _ _ (fun seed => initial_carol_choice seed first second)

private theorem prepared_mixed_advance (execution : app.Execution)
    (original : execution.application.attempt = originalAttempt)
    (position : execution.environmentRecall.length = 3 ∨ execution.environmentRecall.length = 4) :
    scheduler execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure (.application .advanceClock) := by
  apply initial_common_command
  intro seed
  change PMF.pure (choose seed _ _) = _
  rw [choose_original seed _ _ original]
  rcases position with position | position <;> rw [position] <;> rfl

private theorem prepared_mixed_advances (players : Player → app.Policy)
    (first second third : app.Action) :
    (fun law => law.bind (app.controlStep initial horizon scheduler players))^[2]
      (PMF.pure (some ⟨125, none, afterInitialResponses first second third⟩)) =
        PMF.pure (some ⟨123, none, initialClockTwo first second third⟩) := by
  obtain ⟨candidates, frame⟩ := afterInitialResponses_prepared first second third
  have original : (afterInitialResponses first second third).application.attempt =
      originalAttempt := by rw [frame]; exact initialState_attempt
  have nextOriginal : (advance (afterInitialResponses first second third)).application.attempt =
      originalAttempt := by
    rw [advance_prepared _ 0 candidates frame]
    exact initialState_attempt
  have nextLength : (advance (afterInitialResponses first second third)).environmentRecall.length =
      4 := by
    change ((afterInitialResponses first second third).environmentRecall ++ [_]).length = 4
    rw [List.length_append, afterInitialResponses_length]
    rfl
  have firstCommand := prepared_mixed_advance _ original
    (Or.inl (afterInitialResponses_length first second third))
  have secondCommand := prepared_mixed_advance _ nextOriginal (Or.inr nextLength)
  change ((PMF.pure _).bind (app.controlStep initial horizon scheduler players)).bind
    (app.controlStep initial horizon scheduler players) = _
  simp only [PMF.pure_bind, ReactiveApplication.controlStep, ReactiveApplication.actor,
    Option.bind_some, ReactiveApplication.transition, firstCommand, secondCommand,
    advance_law, PMF.pure_map, PMF.pure_bind]
  rfl

private theorem initial_mixed_five_rounds (players : Player → app.Policy) (reference : Seeds) :
    app.runRounds scheduler players 5 initialExecution =
      app.runRounds (family reference) players 5 initialExecution := by
  have actual := app.schedulerMixture_realize nativeSeedLaw family players 5 initialState
  change (nativeSeedLaw.bind fun seed => app.runRounds (family seed) players 5 initialExecution) =
    app.runRounds scheduler players 5 initialExecution at actual
  rw [← actual]
  have same : (fun seed => app.runRounds (family seed) players 5 initialExecution) =
      fun _ => app.runRounds (family reference) players 5 initialExecution :=
    funext (fun seed => first_five_seed_independent seed reference players)
  rw [same, PMF.bind_const]

/-- The actual nine protocol transitions are exactly the original three
callbacks followed by two clock advances. All raw actions and hidden candidate
states remain in the same initialized physical law. -/
theorem prepared_protocol_prefix_state
    (profile : ∀ owner, rawModel.BehavioralPolicy owner) :
    (rawModel.runBehavioral profile 9).map ExecutionProtocol.History.state =
      (app.runRounds scheduler (rawMenu.decodeProfile initial horizon scheduler profile)
        5 initialExecution).map fun frame => some ⟨horizon - 5, none, frame⟩ := by
  let players := rawMenu.decodeProfile initial horizon scheduler profile
  let step := fun law : PMF app.ProtocolState =>
    law.bind (app.controlStep initial horizon scheduler players)
  rw [InformationModel.runBehavioral, rawMenu.run_map_controlSteps]
  change step^[9] (PMF.pure none) = _
  have initialized : step (PMF.pure none) =
      PMF.pure (some ⟨128, none, initialExecution⟩) := by
    simp only [step, PMF.pure_bind, ReactiveApplication.controlStep, ReactiveApplication.actor,
      Option.bind_none, ReactiveApplication.transition, initial, PMF.pure_map]
    rfl
  have aliceRound := app.control_round initial horizon scheduler players 127 initialExecution
    (some alice) (by
      intro command supported
      rw [initial_mixed_alice] at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rfl)
  have bobRound (first : app.Action) := app.control_round initial horizon scheduler players 126
    (initialAliceCallback.respond app alice first) (some bob) (by
      intro command supported
      rw [initial_mixed_bob] at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rfl)
  have carolRound (first second : app.Action) :=
    app.control_round initial horizon scheduler players 125
      ((initialBobCallback first).respond app bob second) (some carol) (by
        intro command supported
        rw [initial_mixed_carol] at supported
        cases (PMF.mem_support_pure_iff _ _).mp supported
        rfl)
  have firstLaw : app.round scheduler players initialExecution =
      (players alice [] (initialAliceCallback.observe app alice)).map
        (initialAliceCallback.respond app alice) := by
    rw [ReactiveApplication.round, initial_mixed_alice, PMF.pure_bind,
      ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind]
    rfl
  have secondLaw (first : app.Action) :
      app.round scheduler players (initialAliceCallback.respond app alice first) =
        (players bob [] ((initialBobCallback first).observe app bob)).map
          ((initialBobCallback first).respond app bob) := by
    rw [ReactiveApplication.round, initial_mixed_bob, PMF.pure_bind,
      ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind]
    rfl
  have thirdLaw (first second : app.Action) :
      app.round scheduler players ((initialBobCallback first).respond app bob second) =
        (players carol [] ((initialCarolCallback first second).observe app carol)).map
          (afterInitialResponses first second) := by
    rw [ReactiveApplication.round, initial_mixed_carol, PMF.pure_bind,
      ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind]
    rfl
  simp only [Option.toList_some, List.length_singleton] at aliceRound bobRound carolRound
  rw [show 9 = 8 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one, initialized,
    show 8 = 6 + 2 from rfl, Function.iterate_add_apply, aliceRound, firstLaw,
    PMF.map_comp, ← PMF.bind_pure_comp, Function.comp_def, iterate_bind]
  rw [initial_mixed_five_rounds players (Classical.choice (inferInstance : Nonempty Seeds)),
    first_five_rounds]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply congrArg (fun kernel =>
    (players alice [] (initialAliceCallback.observe app alice)).bind kernel)
  funext first
  change step^[6] (PMF.pure (some ⟨127, none, _⟩)) = _
  rw [show 6 = 4 + 2 from rfl, Function.iterate_add_apply, bobRound, secondLaw,
    PMF.map_comp, ← PMF.bind_pure_comp, Function.comp_def, iterate_bind]
  apply congrArg (fun kernel =>
    (players bob [] ((initialBobCallback first).observe app bob)).bind kernel)
  funext second
  change step^[4] (PMF.pure (some ⟨126, none, _⟩)) = _
  rw [show 4 = 2 + 2 from rfl, Function.iterate_add_apply, carolRound, thirdLaw,
    PMF.map_comp, ← PMF.bind_pure_comp, Function.comp_def, iterate_bind]
  change _ = (players carol [] ((initialCarolCallback first second).observe app carol)).map _
  rw [← PMF.bind_pure_comp, Function.comp_def]
  apply congrArg (fun kernel =>
    (players carol [] ((initialCarolCallback first second).observe app carol)).bind kernel)
  funext third
  exact prepared_mixed_advances players first second third

/-- The public-word posterior of the actual raw history prefix projects to
the actual prepared-frame posterior. All private preparations and own words
are kept in the frame, and the original history law supplies the weights. -/
theorem prepared_protocol_public_frame_posterior
    (profile : ∀ owner, rawModel.BehavioralPolicy owner)
    (packets : Finset (Message Player app.Payload))
    (present : packets ∈ ((app.runRounds scheduler
      (rawMenu.decodeProfile initial horizon scheduler profile) 5 initialExecution).map
        initialPublicPackets).support) :
    (fiberPosterior (rawModel.runBehavioral profile 9)
      (fun history => (history.state.map fun current =>
        initialPublicPackets current.execution).getD ∅) packets).map
      (fun history => (history.state.map fun current => current.execution).getD initialExecution) =
    fiberPosterior (app.runRounds scheduler
      (rawMenu.decodeProfile initial horizon scheduler profile) 5 initialExecution)
        initialPublicPackets packets := by
  let read := fun history : rawProtocol.History =>
    (history.state.map fun current => current.execution).getD initialExecution
  have actualFrame : (rawModel.runBehavioral profile 9).map read =
      app.runRounds scheduler (rawMenu.decodeProfile initial horizon scheduler profile)
        5 initialExecution := by
    change (rawModel.runBehavioral profile 9).map
      ((fun state : app.ProtocolState =>
        (state.map fun current => current.execution).getD initialExecution) ∘
          ExecutionProtocol.History.state) = _
    rw [← PMF.map_comp, prepared_protocol_prefix_state, PMF.map_comp]
    exact PMF.map_id _
  have oldPresent : packets ∈ ((rawModel.runBehavioral profile 9).map
      (initialPublicPackets ∘ read)).support := by
    rw [← PMF.map_comp, actualFrame]
    exact present
  have sameObservation : (initialPublicPackets ∘ read) = fun history : rawProtocol.History =>
      (history.state.map fun current => initialPublicPackets current.execution).getD ∅ := by
    funext history
    dsimp only [Function.comp_def, read]
    cases history.state <;> rfl
  have posterior := map_fiberPosterior_readout (rawModel.runBehavioral profile 9) read
    initialPublicPackets packets oldPresent
  rw [sameObservation, actualFrame] at posterior
  exact posterior

end Vegas.Examples.CommitSeedBroadcast
