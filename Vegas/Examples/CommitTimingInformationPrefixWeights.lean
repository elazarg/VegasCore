/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitTimingInformationInformation
import Vegas.Examples.CommitTimingInformationChance
import Vegas.Pending.PhaseCountProjection
import Interaction.ReactiveRecordedResponse

/-! # Actual response coefficients before the private timing signal

The initial response coefficient belongs to the original behavioral law.
The passive quiet continuation has no replacement prior or policy premise.
-/

noncomputable section

namespace Vegas.Examples.CommitTimingInformation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

private theorem respond_injective (execution : app.Execution) (owner : Player) :
    Function.Injective (execution.respond app owner) := by
  intro first second equal
  obtain ⟨emittedFirst, firstRecall⟩ := app.respond_recall_entry execution owner first
  obtain ⟨emittedSecond, secondRecall⟩ := app.respond_recall_entry execution owner second
  have records := congrArg (fun next : app.Execution => next.recall owner) equal
  rw [firstRecall, secondRecall] at records
  exact congrArg ReactiveApplication.PlayerEntry.action
    (List.singleton_inj.mp (List.append_cancel_left records))

/-- This is the literal first-response atom in the real native round. -/
theorem first_round_response_mass (seed : Seeds) (bit : Bool)
    (players : Player → app.Policy) (response : app.Action) :
    app.round (family seed) players (initialExecution bit) (aliceResponded bit response) =
      players alice ((aliceFirst bit).recall alice) ((aliceFirst bit).observe app alice)
        response := by
  rw [first_round]
  exact pmf_map_apply_of_injective _ (respond_injective (aliceFirst bit) alice) response

/-- Alice's original WAIT factor is independent of the immutable private bit. -/
theorem initial_wait_mass_independent (players : Player → app.Policy) (first second : Bool) :
    players alice ((aliceFirst first).recall alice) ((aliceFirst first).observe app alice)
        ⟨none⟩ =
      players alice ((aliceFirst second).recall alice) ((aliceFirst second).observe app alice)
        ⟨none⟩ :=
  congrArg (fun input => players alice input.1 input.2 ⟨none⟩)
    (aliceFirst_input_independent first second)

private theorem initial_quiet_application (bit : Bool) :
    (aliceResponded bit ⟨none⟩).application = quietApplication bit 0 := by
  change initialState bit = quietApplication bit 0
  rw [quietApplication, initialState_eq]
  rfl

private theorem quiet_first_advance_family (seed : Seeds) (bit : Bool) :
    family seed (aliceResponded bit ⟨none⟩).environmentRecall
        ((aliceResponded bit ⟨none⟩).observeEnvironment app) =
      PMF.pure (.application .advanceClock) := by
  change PMF.pure (choose seed _ _) = _
  rw [choose_original seed _ _ (initialState_attempt bit)]
  rfl

private theorem quiet_middle_family (seed : Seeds) (bit : Bool) :
    family seed (advance (aliceResponded bit ⟨none⟩)).environmentRecall
        ((advance (aliceResponded bit ⟨none⟩)).observeEnvironment app) = PMF.pure .wait := by
  have state := advance_application _ bit 0 (initial_quiet_application bit)
  have original : (advance (aliceResponded bit ⟨none⟩)).application.attempt =
      originalAttempt := by
    rw [state]
    exact initialState_attempt bit
  change PMF.pure (choose seed _ _) = _
  rw [choose_original seed _ _ original]
  have length : (advance (aliceResponded bit ⟨none⟩)).environmentRecall.length = 2 := rfl
  rw [length]
  simp only [originalCommand]
  have snapshot : (advance (aliceResponded bit ⟨none⟩)).environmentRecall[1]? =
      some ⟨(aliceResponded bit ⟨none⟩).observeEnvironment app,
        .application .advanceClock⟩ := rfl
  rw [earlyCommand, snapshot]
  have empty : (aliceResponded bit ⟨none⟩).network = MessageNetwork.empty :=
    aliceFirst_network bit
  change PMF.pure (match ((aliceResponded bit ⟨none⟩).network.publicView.inputs.find?
      (fun message => message.sender = alice ∧ message.payload.attempt = originalAttempt)) with
    | none => (ReactiveApplication.Command.wait : app.Command)
    | some message => pendingCommand message.id
        ((advance (aliceResponded bit ⟨none⟩)).observeEnvironment app)) = _
  rw [empty]
  rfl

private theorem quiet_second_advance_family (seed : Seeds) (bit : Bool) :
    family seed (pause (advance (aliceResponded bit ⟨none⟩))).environmentRecall
        ((pause (advance (aliceResponded bit ⟨none⟩))).observeEnvironment app) =
      PMF.pure (.application .advanceClock) := by
  have state := advance_application _ bit 0 (initial_quiet_application bit)
  have original : (pause (advance (aliceResponded bit ⟨none⟩))).application.attempt =
      originalAttempt := by
    change (advance (aliceResponded bit ⟨none⟩)).application.attempt = _
    rw [state]
    exact initialState_attempt bit
  change PMF.pure (choose seed _ _) = _
  rw [choose_original seed _ _ original]
  rfl

/-- Conditioned on its literal first WAIT response, the next three original
commands are passive and retain the entire initialized hidden input. -/
theorem quiet_initial_continuation (seed : Seeds) (bit : Bool)
    (players : Player → app.Policy) :
    app.runRounds (family seed) players 3 (aliceResponded bit ⟨none⟩) =
      PMF.pure (quietStart bit) := by
  have first : app.round (family seed) players (aliceResponded bit ⟨none⟩) =
      PMF.pure (advance (aliceResponded bit ⟨none⟩)) := by
    rw [ReactiveApplication.round, quiet_first_advance_family, PMF.pure_bind,
      ReactiveApplication.dispatch, advance_law, PMF.pure_bind]
    rfl
  have middle : app.round (family seed) players (advance (aliceResponded bit ⟨none⟩)) =
      PMF.pure (pause (advance (aliceResponded bit ⟨none⟩))) := by
    rw [ReactiveApplication.round, quiet_middle_family, PMF.pure_bind,
      ReactiveApplication.dispatch, pause_law, PMF.pure_bind]
    rfl
  have last : app.round (family seed) players (pause (advance (aliceResponded bit ⟨none⟩))) =
      PMF.pure (quietStart bit) := by
    rw [ReactiveApplication.round, quiet_second_advance_family, PMF.pure_bind,
      ReactiveApplication.dispatch, advance_law, PMF.pure_bind]
    rfl
  rw [ReactiveApplication.runRounds, first, PMF.pure_bind,
    ReactiveApplication.runRounds, middle, PMF.pure_bind,
    ReactiveApplication.runRounds, last, PMF.pure_bind, ReactiveApplication.runRounds]

private theorem family_good_first_late (final bit : Bool) :
    family (true, final) (quietStart bit).environmentRecall
        ((quietStart bit).observeEnvironment app) = PMF.pure (.activate alice) := by
  change PMF.pure (choose _ _ _) = _
  rw [choose_original _ _ _ (quietStart_attempt bit), quietStart_length]
  change PMF.pure (if true = true then activateReady alice (bindingEvent alice) _ else .wait) = _
  rw [ite_eq_left (rfl : true = true), activateReady, quietStart_ready]
  rfl

private theorem family_bad_skips_first_late (final bit : Bool) :
    family (false, final) (quietStart bit).environmentRecall
        ((quietStart bit).observeEnvironment app) = PMF.pure .wait := by
  change PMF.pure (choose _ _ _) = _
  rw [choose_original _ _ _ (quietStart_attempt bit), quietStart_length]
  rfl

private theorem response_public (execution : app.Execution) (owner : Player)
    (response : app.Action) :
    (execution.respond app owner response).application.publicView =
      execution.application.publicView := by
  rcases response with ⟨material⟩
  cases material with
  | none => rfl
  | some material => exact PhaseCount.submit_publicView execution.application owner material

private theorem family_good_bob (final bit : Bool) (response : app.Action) :
    family (true, final) ((aliceEmptyGood bit).respond app alice response).environmentRecall
        (((aliceEmptyGood bit).respond app alice response).observeEnvironment app) =
      PMF.pure (.activate bob) := by
  have publicEq := response_public (aliceEmptyGood bit) alice response
  have original : ((aliceEmptyGood bit).respond app alice response).application.attempt =
      originalAttempt := by
    exact (congrArg PhasePublicView.attempt publicEq).trans (quietStart_attempt bit)
  change PMF.pure (choose _ _ _) = _
  rw [choose_original _ _ _ original]
  change PMF.pure (activateReady bob (bindingEvent bob) _) = _
  have eligible : ready bob (bindingEvent bob)
      (((aliceEmptyGood bit).respond app alice response).observeEnvironment app) = true := by
    classical
    change decide (PhaseRuntimeState.requests
      ((aliceEmptyGood bit).respond app alice response).application.publicView bob
      ⟨((aliceEmptyGood bit).respond app alice response).application.attempt,
        bindingEvent bob⟩) = true
    rw [original, publicEq]
    have prepared := quietStart_ready bit bob
    change decide (PhaseRuntimeState.requests (quietStart bit).application.publicView bob
      ⟨(quietStart bit).application.attempt, bindingEvent bob⟩) = true at prepared
    rw [quietStart_attempt] at prepared
    exact prepared
  rw [activateReady, eligible]
  rfl

private theorem family_bad_bob (final bit : Bool) :
    family (false, final) (pause (quietStart bit)).environmentRecall
        ((pause (quietStart bit)).observeEnvironment app) = PMF.pure (.activate bob) := by
  change PMF.pure (choose _ _ _) = _
  rw [choose_original _ _ _ (quietStart_attempt bit)]
  change PMF.pure (activateReady bob (bindingEvent bob) _) = _
  have eligible : ready bob (bindingEvent bob)
      ((pause (quietStart bit)).observeEnvironment app) = true := quietStart_ready bit bob
  rw [activateReady, eligible]
  rfl

/-- Good Alice acts before Bob. Both kernels use the literal native callback
inputs, retaining arbitrary raw material and its private registration. -/
theorem good_clock_two_rounds (final bit : Bool) (players : Player → app.Policy) :
    app.runRounds (family (true, final)) players 2 (quietStart bit) =
      (players alice ((aliceEmptyGood bit).recall alice)
        ((aliceEmptyGood bit).observe app alice)).bind fun first =>
      (players bob ((bobAfterGood bit first).recall bob)
        ((bobAfterGood bit first).observe app bob)).map
          ((bobAfterGood bit first).respond app bob) := by
  have first : app.round (family (true, final)) players (quietStart bit) =
      (players alice ((aliceEmptyGood bit).recall alice)
        ((aliceEmptyGood bit).observe app alice)).map
          ((aliceEmptyGood bit).respond app alice) := by
    rw [ReactiveApplication.round, family_good_first_late, PMF.pure_bind,
      ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind]
    rfl
  have second (response : app.Action) :
      app.round (family (true, final)) players
        ((aliceEmptyGood bit).respond app alice response) =
      (players bob ((bobAfterGood bit response).recall bob)
        ((bobAfterGood bit response).observe app bob)).map
          ((bobAfterGood bit response).respond app bob) := by
    rw [ReactiveApplication.round, family_good_bob, PMF.pure_bind,
      ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind]
    rfl
  rw [ReactiveApplication.runRounds, first, PMF.bind_map]
  apply bind_congr_on_support
  intro response _supported
  dsimp only [Function.comp_apply]
  rw [ReactiveApplication.runRounds, second]
  simp only [ReactiveApplication.runRounds, PMF.bind_pure]

/-- Bad Alice has not acted when Bob chooses; the passive poll is an actual
recorded WAIT, and Bob's full input is the same quiet input as above. -/
theorem bad_clock_two_rounds (final bit : Bool) (players : Player → app.Policy) :
    app.runRounds (family (false, final)) players 2 (quietStart bit) =
      (players bob ((bobBeforeBad bit).recall bob)
        ((bobBeforeBad bit).observe app bob)).map ((bobBeforeBad bit).respond app bob) := by
  rw [ReactiveApplication.runRounds, ReactiveApplication.round, family_bad_skips_first_late,
    PMF.pure_bind, ReactiveApplication.dispatch, pause_law, PMF.pure_bind]
  simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume, PMF.pure_bind]
  rw [ReactiveApplication.runRounds, ReactiveApplication.round, family_bad_bob,
    PMF.pure_bind, ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind]
  change ((players bob ((bobBeforeBad bit).recall bob)
    ((bobBeforeBad bit).observe app bob)).map _).bind _ = _
  simp only [ReactiveApplication.runRounds, PMF.bind_pure]
  rfl

/-- The next real scheduler command after poll position four is Bob's
activation; its law is retained before Bob chooses a response. -/
def bobClockTwoActivation (seed : Seeds) (bit : Bool) (players : Player → app.Policy) :
    PMF app.Execution :=
  (app.round (family seed) players (quietStart bit)).bind fun before =>
    (family seed before.environmentRecall (before.observeEnvironment app)).bind fun command =>
      before.environmentStep app command

def bobClockTwoInputLaw (seed : Seeds) (bit : Bool) (players : Player → app.Policy) :
    PMF (List app.PlayerEntry × app.PlayerView) :=
  (bobClockTwoActivation seed bit players).map (nativeInput bob)

theorem good_bob_clock_two_input_law (final bit : Bool) (players : Player → app.Policy) :
    bobClockTwoInputLaw (true, final) bit players =
      (players alice ((aliceEmptyGood bit).recall alice)
        ((aliceEmptyGood bit).observe app alice)).map (fun response =>
          nativeInput bob (bobAfterGood bit response)) := by
  have first : app.round (family (true, final)) players (quietStart bit) =
      (players alice ((aliceEmptyGood bit).recall alice)
        ((aliceEmptyGood bit).observe app alice)).map
          ((aliceEmptyGood bit).respond app alice) := by
    rw [ReactiveApplication.round, family_good_first_late, PMF.pure_bind,
      ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind]
    rfl
  unfold bobClockTwoInputLaw bobClockTwoActivation
  rw [first, PMF.bind_map, PMF.map_bind]
  change (players alice ((aliceEmptyGood bit).recall alice)
    ((aliceEmptyGood bit).observe app alice)).bind _ = _
  rw [← pmf_bind_pure_eq_map]
  apply bind_congr_on_support
  intro response _supported
  dsimp only [Function.comp_apply]
  rw [family_good_bob, PMF.pure_bind, completeActivation_law, PMF.pure_map]
  rfl

theorem bad_bob_clock_two_input_law (final bit : Bool) (players : Player → app.Policy) :
    bobClockTwoInputLaw (false, final) bit players =
      PMF.pure (nativeInput bob (bobBeforeBad bit)) := by
  have first : app.round (family (false, final)) players (quietStart bit) =
      PMF.pure (pause (quietStart bit)) := by
    rw [ReactiveApplication.round, family_bad_skips_first_late, PMF.pure_bind,
      ReactiveApplication.dispatch, pause_law, PMF.pure_bind]
    rfl
  unfold bobClockTwoInputLaw bobClockTwoActivation
  rw [first, PMF.pure_bind, family_bad_bob, PMF.pure_bind,
    completeActivation_law, PMF.pure_map]
  rfl

private theorem bobAfterGood_empty_leaks_iff (bit : Bool) (response : app.Action) :
    ((bobAfterGood bit response).observe app bob).messages.leaked = [] ↔
      response.transmission = none := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      have same := congrArg (fun input => input.2.messages.leaked)
        (bob_clock_two_quiet_input bit)
      have empty : ((bobBeforeBad bit).observe app bob).messages.leaked = [] := by
        simp only [bobBeforeBad, completeActivation, pause,
          ReactiveApplication.Execution.sampledActivation, ReactiveApplication.Execution.observe,
          quietStart_network, MessageNetwork.empty, List.map_nil, List.toFinset_nil,
          MessageNetwork.learn_empty, MessageNetwork.observe]
      exact iff_of_true (same.trans empty) rfl
  | some material =>
      simp [bobAfterGood, aliceEmptyGood, completeActivation,
        ReactiveApplication.Execution.respond, ReactiveApplication.Execution.sampledActivation,
        ReactiveApplication.Execution.observe, quietStart_network, MessageNetwork.submit,
        MessageNetwork.empty, MessageNetwork.learn, MessageNetwork.known,
        MessageNetwork.lookup, MessageNetwork.observe, Message.sender, alice, bob]

/-- Complete pending observation makes the quiet information fiber exact:
no raw transmission, including a malformed or aliased one, can enter it. -/
theorem bob_clock_two_quiet_iff (bit : Bool) (response : app.Action) :
    nativeInput bob (bobAfterGood bit response) = nativeInput bob (bobBeforeBad bit) ↔
      response = ⟨none⟩ := by
  constructor
  · intro same
    have leaked := congrArg (fun input => input.2.messages.leaked) same
    have empty : ((bobBeforeBad bit).observe app bob).messages.leaked = [] := by
      simp only [bobBeforeBad, completeActivation, pause,
        ReactiveApplication.Execution.sampledActivation, ReactiveApplication.Execution.observe,
        quietStart_network, MessageNetwork.empty, List.map_nil, List.toFinset_nil,
        MessageNetwork.learn_empty, MessageNetwork.observe]
    have absent := (bobAfterGood_empty_leaks_iff bit response).mp (leaked.trans empty)
    cases response
    cases absent
    rfl
  · rintro rfl
    exact bob_clock_two_quiet_input bit

/-- The good-seed quiet likelihood is the original Alice WAIT response atom. -/
theorem good_bob_clock_two_quiet_mass (final bit : Bool) (players : Player → app.Policy) :
    bobClockTwoInputLaw (true, final) bit players
        (nativeInput bob (bobBeforeBad bit)) =
      players alice ((aliceEmptyGood bit).recall alice)
        ((aliceEmptyGood bit).observe app alice) ⟨none⟩ := by
  rw [good_bob_clock_two_input_law, ← pmf_bind_pure_eq_map]
  rw [bind_apply_of_unique_branch _ _ _ (⟨none⟩ : app.Action) (by
    intro response _supported member
    have equal := (PMF.mem_support_pure_iff _ _).mp member
    exact (bob_clock_two_quiet_iff bit response).mp equal.symm)]
  rw [bob_clock_two_quiet_input, PMF.pure_apply_self, mul_one]

theorem bad_bob_clock_two_quiet_mass (final bit : Bool) (players : Player → app.Policy) :
    bobClockTwoInputLaw (false, final) bit players
      (nativeInput bob (bobBeforeBad bit)) = 1 := by
  rw [bad_bob_clock_two_input_law, PMF.pure_apply_self]

end Vegas.Examples.CommitTimingInformation
