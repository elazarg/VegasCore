/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.ConditionalObservation
import Vegas.Examples.OpaqueBindingForkImmediate

/-! # Conditional private risk at a rare initialized information input

One admitted policy mixes Alice's initial WAIT with weight alpha and an immediate
canonical binding with the remaining weight. A public builder satisfying the
contract at every RAW history fairly orders a tick and her second activation.
The actual initialized law includes the two delayed and two immediate branches.

Both delayed branches give Bob the same source-compatible full input, with
opposite Alice private-risk flags. Immediate acceptance gives a different public
activation time. The delayed fiber has mass alpha and conditional risk one half
for every positive alpha. This constructed policy is not a rational free-site
completion or an equilibrium counterexample.
-/

noncomputable section

namespace Vegas.OpaqueBindingFork.VanishingWait

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

abbrev BobInput := List app.PlayerEntry × app.PlayerView

def bobInput : BobInput := (cleanBob.recall bob, cleanBob.observe app bob)

def fairRisk : PMF Bool := mix (1 / 2) (by norm_num) (by norm_num)
  (PMF.pure false) (PMF.pure true)

private def tickedWait : app.Execution :=
  WaitRiskConfounding.advance (runtime setup) leaks emptyIncludeExecution

variable (alpha : ℝ) (nonnegative : 0 ≤ alpha) (small : alpha ≤ 1)

/-- One policy shared by equal local inputs: mix WAIT and the canonical first
call, call at the two second inputs, and otherwise remain silent. -/
def players : Player → app.Policy := fun who past view => by
  classical
  exact if who = alice then
    if (past, view) = (firstAliceExecution.recall alice, firstAliceExecution.observe app alice) then
      mix alpha nonnegative small (PMF.pure ⟨none⟩) (PMF.pure bindingResponse)
    else if (past, view) =
        (secondAliceExecution.recall alice, secondAliceExecution.observe app alice) ∨
      (past, view) = (riskySecondAlice.recall alice, riskySecondAlice.observe app alice) then
      PMF.pure bindingResponse
    else PMF.pure ⟨none⟩
  else PMF.pure ⟨none⟩

private theorem first_response_canonical : bindingResponse ∈
    canonicalMenu.actions alice (firstAliceExecution.recall alice)
      (firstAliceExecution.observe app alice) := by
  have canonical : (runtime setup).canonicalServiceDecision leaks alice
      (firstAliceExecution.recall alice) (firstAliceExecution.observe app alice)
      binding (.success true) = bindingResponse := by
    apply (runtime setup).canonicalServiceDecision_binding leaks alice _ _ binding .bool
      binding_output binding_code binding_node 0
    have counted : (firstAliceExecution.observe app alice).application.publicView.bindingCount
        alice = 0 := by decide
    rw [← counted]
    exact canonicalFreshSlot_canonical alice _ (by rfl)
  rw [← canonical]
  exact bounds.canonical_binding_value_retained (runtime setup) leaks alice _ _ binding .bool
    binding_output binding_code binding_node binding_turn binding_actor
    ((PublicView.ownTurn?_spec _ alice binding binding_turn).1)
    (by change 0 - 0 < 3; decide) rfl 0 rfl (by decide) true (by
      apply baseBounds.withInitialValues_preserves_values
      simp [baseBounds])

theorem players_covered (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (response : app.Action) (chosen : response ∈ (players alpha nonnegative small who past
      view).support) : response ∈ riskMenu.actions who past view := by
  classical
  unfold players at chosen
  split at chosen
  · rename_i same
    subst who
    split at chosen
    · rename_i first
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj first
      rcases (support_mix_subset alpha nonnegative small _ _) chosen with wait | call
      · cases (PMF.mem_support_pure_iff _ _).mp wait
        exact bounds.canonicalActions_subset_risk (runtime setup) leaks bound alice _ _
          (bounds.silence_canonical (runtime setup) leaks alice _ _)
      · cases (PMF.mem_support_pure_iff _ _).mp call
        exact bounds.canonicalActions_subset_risk (runtime setup) leaks bound alice _ _
          first_response_canonical
    · split at chosen
      · rename_i second
        cases (PMF.mem_support_pure_iff _ _).mp chosen
        rcases second with early | late
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj early
          exact bounds.canonicalActions_subset_risk (runtime setup) leaks bound alice _ _
            secondAlice_response_canonical
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj late
          exact bounds.canonicalActions_subset_risk (runtime setup) leaks bound alice _ _
            riskyResponse_canonical
      · cases (PMF.mem_support_pure_iff _ _).mp chosen
        exact bounds.canonicalActions_subset_risk (runtime setup) leaks bound alice _ _
          (bounds.silence_canonical (runtime setup) leaks alice _ _)
  · cases (PMF.mem_support_pure_iff _ _).mp chosen
    exact bounds.canonicalActions_subset_risk (runtime setup) leaks bound who past view
      (bounds.silence_canonical (runtime setup) leaks who past view)

theorem players_admissible (who : Player) :
    riskMenu.Admissible (initialLaw setup) horizon scheduler who
      (players alpha nonnegative small who) :=
  riskMenu.admissible_of_covered (initialLaw setup) horizon scheduler
    (players alpha nonnegative small) (players_covered alpha nonnegative small) who

private theorem cleanSecond_not_first :
    (secondAliceExecution.recall alice, secondAliceExecution.observe app alice) ≠
      (firstAliceExecution.recall alice, firstAliceExecution.observe app alice) := by
  intro same
  have lengths := congrArg
    (fun input : List app.PlayerEntry × app.PlayerView => input.1.length) same
  change 1 = 0 at lengths
  omega

private theorem riskySecond_not_first :
    (riskySecondAlice.recall alice, riskySecondAlice.observe app alice) ≠
      (firstAliceExecution.recall alice, firstAliceExecution.observe app alice) := by
  intro same
  have lengths := congrArg
    (fun input : List app.PlayerEntry × app.PlayerView => input.1.length) same
  change 1 = 0 at lengths
  omega

private theorem first_response : players alpha nonnegative small alice
    (firstAliceExecution.recall alice) (firstAliceExecution.observe app alice) =
      mix alpha nonnegative small (PMF.pure ⟨none⟩) (PMF.pure bindingResponse) := by
  simp only [players, ite_true]

private theorem fork_second : players alpha nonnegative small alice
    (secondAliceExecution.recall alice) (secondAliceExecution.observe app alice) =
      PMF.pure bindingResponse := by
  simp only [players, ite_true, cleanSecond_not_first, ite_false, true_or]

private theorem fork_risky : players alpha nonnegative small alice
    (riskySecondAlice.recall alice) (riskySecondAlice.observe app alice) =
      PMF.pure bindingResponse := by
  simp only [players, ite_true, riskySecond_not_first, ite_false, or_true]

private theorem initial_law : initialLaw setup = PMF.pure initialState := by
  rw [initialLaw_eq_inputs]
  change ((PMF.pure sourceInitial).map setup.eventInputs).map
    (State.initial (graph := nativeGraph)) = _
  rw [PMF.pure_map, PMF.pure_map]
  rfl

private theorem round_sample0 : app.round scheduler (players alpha nonnegative small)
    initialExecution = PMF.pure sampled0Execution := by
  change (PMF.pure (.application (.executeSample sample0) : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch, sampled0_environment, PMF.pure_bind]
  rfl

private theorem round_sample1 : app.round scheduler (players alpha nonnegative small)
    sampled0Execution = PMF.pure sampled1Execution := by
  change (PMF.pure (.application (.executeSample sample1) : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch, sampled1_environment, PMF.pure_bind]
  rfl

private theorem round_first : app.round scheduler (players alpha nonnegative small)
    sampled1Execution = mix alpha nonnegative small (PMF.pure waitedExecution)
      (PMF.pure immediateSubmitted) := by
  change (PMF.pure (.activate alice : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch,
    WaitRiskConfounding.activate_empty_law (runtime setup) leaks _ alice rfl, PMF.pure_bind]
  change (players alpha nonnegative small alice (firstAliceExecution.recall alice)
    (firstAliceExecution.observe app alice)).map _ = _
  rw [first_response, mix_map, PMF.pure_map, PMF.pure_map]
  rfl

private theorem round_empty : app.round scheduler (players alpha nonnegative small)
    waitedExecution = PMF.pure emptyIncludeExecution := by
  change (PMF.pure (.wait : app.Command)).bind _ = _
  simp only [PMF.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  rfl

private theorem round_immediate_include : app.round scheduler (players alpha nonnegative small)
    immediateSubmitted = PMF.pure immediateAccepted := by
  change (PMF.pure (.include (alice, 0) : app.Command)).bind _ = _
  simp only [PMF.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  rfl

private theorem rounds4 : app.roundsFrom (initialLaw setup) scheduler
    (players alpha nonnegative small) 4 = mix alpha nonnegative small
      (PMF.pure emptyIncludeExecution) (PMF.pure immediateAccepted) := by
  have zero : app.roundsFrom (initialLaw setup) scheduler (players alpha nonnegative small) 0 =
      PMF.pure initialExecution := by
    simp only [ReactiveApplication.roundsFrom, initial_law, PMF.pure_bind,
      ReactiveApplication.runRounds]
    rfl
  rw [app.roundsFrom_succ (initialLaw setup) scheduler (players alpha nonnegative small) 3,
    app.roundsFrom_succ (initialLaw setup) scheduler (players alpha nonnegative small) 2,
    app.roundsFrom_succ (initialLaw setup) scheduler (players alpha nonnegative small) 1,
    app.roundsFrom_succ (initialLaw setup) scheduler (players alpha nonnegative small) 0,
    zero, PMF.pure_bind, round_sample0, PMF.pure_bind, round_sample1, PMF.pure_bind,
    round_first, mix_bind, PMF.pure_bind, PMF.pure_bind, round_empty, round_immediate_include]

private theorem round_fork :
    app.round scheduler (players alpha nonnegative small) emptyIncludeExecution =
    mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure cleanSubmitted)
      (PMF.pure tickedWait) := by
  change (mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure (.activate alice))
    (PMF.pure (.application .advanceClock : app.Command))).bind _ = _
  rw [mix_bind, PMF.pure_bind, PMF.pure_bind]
  congr 1
  · rw [ReactiveApplication.dispatch,
      WaitRiskConfounding.activate_empty_law (runtime setup) leaks _ alice rfl, PMF.pure_bind]
    change ((players alpha nonnegative small) alice (secondAliceExecution.recall alice)
      (secondAliceExecution.observe app alice)).map _ = _
    rw [fork_second, PMF.pure_map]
    rfl
  · rw [ReactiveApplication.dispatch,
      WaitRiskConfounding.advance_law (runtime setup) leaks, PMF.pure_bind]
    rfl

private theorem round_clean_tick :
    app.round scheduler (players alpha nonnegative small) cleanSubmitted =
    PMF.pure cleanTicked := by
  change (PMF.pure (.application .advanceClock : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch,
    WaitRiskConfounding.advance_law (runtime setup) leaks, PMF.pure_bind]
  rfl

private theorem round_risky_response :
    app.round scheduler (players alpha nonnegative small) tickedWait =
    PMF.pure riskySubmitted := by
  change (PMF.pure (.activate alice : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch,
    WaitRiskConfounding.activate_empty_law (runtime setup) leaks _ alice rfl, PMF.pure_bind]
  change ((players alpha nonnegative small) alice (riskySecondAlice.recall alice)
    (riskySecondAlice.observe app alice)).map _ = _
  rw [fork_risky, PMF.pure_map]
  rfl

private theorem round_clean_include :
    app.round scheduler (players alpha nonnegative small) cleanTicked =
    PMF.pure cleanAccepted := by
  change (PMF.pure (.include (alice, 0) : app.Command)).bind _ = _
  simp only [PMF.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  rfl

private theorem round_risky_include :
    app.round scheduler (players alpha nonnegative small) riskySubmitted =
    PMF.pure riskyAccepted := by
  change (PMF.pure (.include (alice, 0) : app.Command)).bind _ = _
  simp only [PMF.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  rfl

private theorem round_clean_tick1 :
    app.round scheduler (players alpha nonnegative small) cleanAccepted =
    PMF.pure cleanTick1 := by
  change (PMF.pure (.application .advanceClock : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch,
    WaitRiskConfounding.advance_law (runtime setup) leaks, PMF.pure_bind]
  rfl

private theorem round_risky_tick1 :
    app.round scheduler (players alpha nonnegative small) riskyAccepted =
    PMF.pure riskyTick1 := by
  change (PMF.pure (.application .advanceClock : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch,
    WaitRiskConfounding.advance_law (runtime setup) leaks, PMF.pure_bind]
  rfl

private theorem round_clean_tick2 :
    app.round scheduler (players alpha nonnegative small) cleanTick1 =
    PMF.pure cleanBeforeExpiry := by
  change (PMF.pure (.application .advanceClock : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch,
    WaitRiskConfounding.advance_law (runtime setup) leaks, PMF.pure_bind]
  rfl

private theorem round_risky_tick2 :
    app.round scheduler (players alpha nonnegative small) riskyTick1 =
    PMF.pure riskyBeforeExpiry := by
  change (PMF.pure (.application .advanceClock : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch,
    WaitRiskConfounding.advance_law (runtime setup) leaks, PMF.pure_bind]
  rfl

private theorem risky_expiry : riskyBeforeExpiry.environmentStep app
    (.application (.expire binding)) = PMF.pure riskyAfterExpiry := by
  have notReady : ¬riskyBeforeExpiry.application.config.cut.Ready binding := by
    intro ready
    have completed : binding ∈ riskyAccepted.application.config.cut.completed := by
      rw [← accepted_application_eq]
      exact cleanAccepted_binding_completed
    exact ready.1 completed
  change ((environmentStep (runtime setup) riskyBeforeExpiry.application (.expire binding)).map
    _).map _ = _
  rw [environmentStep_expire_of_not_ready (runtime setup) _ binding notReady,
    PMF.pure_map, PMF.pure_map]
  rfl

private theorem round_clean_expiry :
    app.round scheduler (players alpha nonnegative small) cleanBeforeExpiry =
    PMF.pure cleanAfterExpiry := by
  change (PMF.pure (.application (.expire binding) : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch, cleanAfterExpiry_environment, PMF.pure_bind]
  rfl

private theorem round_risky_expiry :
    app.round scheduler (players alpha nonnegative small) riskyBeforeExpiry =
    PMF.pure riskyAfterExpiry := by
  change (PMF.pure (.application (.expire binding) : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch, risky_expiry, PMF.pure_bind]
  rfl

def immediateTickBefore : app.Execution :=
  WaitRiskConfounding.advance (runtime setup) leaks immediateAccepted

def immediateOtherSecond : app.Execution :=
  (WaitRiskConfounding.activate (runtime setup) leaks immediateTickBefore alice).respond app alice
    ⟨none⟩

def immediateOtherEmpty : app.Execution :=
  { immediateOtherSecond with environmentRecall := immediateOtherSecond.environmentRecall ++
      [⟨immediateOtherSecond.observeEnvironment app, .wait⟩] }

def immediateOtherTick1 : app.Execution :=
  WaitRiskConfounding.advance (runtime setup) leaks immediateOtherEmpty

def immediateOtherBeforeExpiry : app.Execution :=
  WaitRiskConfounding.advance (runtime setup) leaks immediateOtherTick1

def immediateOtherAfterExpiry : app.Execution := expiredExecution immediateOtherBeforeExpiry

def immediateOtherBob : app.Execution :=
  WaitRiskConfounding.activate (runtime setup) leaks immediateOtherAfterExpiry bob

private theorem immediate_second_response : players alpha nonnegative small alice
    ((WaitRiskConfounding.activate (runtime setup) leaks immediateAccepted alice).recall alice)
    ((WaitRiskConfounding.activate (runtime setup) leaks immediateAccepted alice).observe
      app alice) = PMF.pure ⟨none⟩ := by
  have first :
      ((WaitRiskConfounding.activate (runtime setup) leaks immediateAccepted alice).recall alice,
        (WaitRiskConfounding.activate (runtime setup) leaks immediateAccepted alice).observe
          app alice)
      ≠ (firstAliceExecution.recall alice, firstAliceExecution.observe app alice) := by
    intro same
    have lengths := congrArg
      (fun input : List app.PlayerEntry × app.PlayerView => input.1.length) same
    change 1 = 0 at lengths
    omega
  have both : ¬(
      ((WaitRiskConfounding.activate (runtime setup) leaks immediateAccepted alice).recall alice,
        (WaitRiskConfounding.activate (runtime setup) leaks immediateAccepted alice).observe
          app alice)
      = (secondAliceExecution.recall alice, secondAliceExecution.observe app alice) ∨
      ((WaitRiskConfounding.activate (runtime setup) leaks immediateAccepted alice).recall alice,
        (WaitRiskConfounding.activate (runtime setup) leaks immediateAccepted alice).observe
          app alice)
      = (riskySecondAlice.recall alice, riskySecondAlice.observe app alice)) := by
    intro same
    rcases same with same | same
    all_goals
      have actions := congrArg (fun input : List app.PlayerEntry × app.PlayerView =>
        input.1.map ReactiveApplication.PlayerEntry.action) same
      change [bindingResponse] = [⟨none⟩] at actions
      cases actions
  simp only [players, ite_true, first, ite_false, both]

private theorem immediate_other_response : players alpha nonnegative small alice
    ((WaitRiskConfounding.activate (runtime setup) leaks immediateTickBefore alice).recall alice)
    ((WaitRiskConfounding.activate (runtime setup) leaks immediateTickBefore alice).observe
      app alice) = PMF.pure ⟨none⟩ := by
  have first :
      ((WaitRiskConfounding.activate (runtime setup) leaks immediateTickBefore alice).recall alice,
        (WaitRiskConfounding.activate (runtime setup) leaks immediateTickBefore alice).observe
          app alice) ≠
      (firstAliceExecution.recall alice, firstAliceExecution.observe app alice) := by
    intro same
    have lengths := congrArg
      (fun input : List app.PlayerEntry × app.PlayerView => input.1.length) same
    change 1 = 0 at lengths
    omega
  have both : ¬(
      ((WaitRiskConfounding.activate (runtime setup) leaks immediateTickBefore alice).recall alice,
        (WaitRiskConfounding.activate (runtime setup) leaks immediateTickBefore alice).observe
          app alice) = (secondAliceExecution.recall alice, secondAliceExecution.observe app alice) ∨
      ((WaitRiskConfounding.activate (runtime setup) leaks immediateTickBefore alice).recall alice,
        (WaitRiskConfounding.activate (runtime setup) leaks immediateTickBefore alice).observe
          app alice) = (riskySecondAlice.recall alice, riskySecondAlice.observe app alice)) := by
    intro same
    rcases same with same | same
    all_goals
      have actions := congrArg (fun input : List app.PlayerEntry × app.PlayerView =>
        input.1.map ReactiveApplication.PlayerEntry.action) same
      change [bindingResponse] = [⟨none⟩] at actions
      cases actions
  simp only [players, ite_true, first, ite_false, both]

private theorem round_immediate_fork : app.round scheduler (players alpha nonnegative small)
    immediateAccepted = mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure immediateSecond)
      (PMF.pure immediateTickBefore) := by
  change (mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure (.activate alice))
    (PMF.pure (.application .advanceClock : app.Command))).bind _ = _
  rw [mix_bind, PMF.pure_bind, PMF.pure_bind]
  congr 1
  · rw [ReactiveApplication.dispatch,
      WaitRiskConfounding.activate_empty_law (runtime setup) leaks _ alice rfl, PMF.pure_bind]
    change (players alpha nonnegative small alice
      ((WaitRiskConfounding.activate (runtime setup) leaks immediateAccepted alice).recall alice)
      ((WaitRiskConfounding.activate (runtime setup) leaks immediateAccepted alice).observe
        app alice)).map _ = _
    rw [immediate_second_response, PMF.pure_map]
    rfl
  · rw [ReactiveApplication.dispatch,
      WaitRiskConfounding.advance_law (runtime setup) leaks, PMF.pure_bind]
    rfl

private theorem round_immediate_tick : app.round scheduler (players alpha nonnegative small)
    immediateSecond = PMF.pure immediateTicked := by
  change (PMF.pure (.application .advanceClock : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch,
    WaitRiskConfounding.advance_law (runtime setup) leaks, PMF.pure_bind]
  rfl

private theorem round_immediate_other : app.round scheduler (players alpha nonnegative small)
    immediateTickBefore = PMF.pure immediateOtherSecond := by
  change (PMF.pure (.activate alice : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch,
    WaitRiskConfounding.activate_empty_law (runtime setup) leaks _ alice rfl, PMF.pure_bind]
  change (players alpha nonnegative small alice
    ((WaitRiskConfounding.activate (runtime setup) leaks immediateTickBefore alice).recall alice)
    ((WaitRiskConfounding.activate (runtime setup) leaks immediateTickBefore alice).observe
      app alice)).map _ = _
  rw [immediate_other_response, PMF.pure_map]
  rfl

private theorem round_immediate_empty : app.round scheduler (players alpha nonnegative small)
    immediateTicked = PMF.pure immediateEmptyInclude := by
  change (PMF.pure (.wait : app.Command)).bind _ = _
  simp only [PMF.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  rfl

private theorem round_immediate_other_empty : app.round scheduler (players alpha nonnegative small)
    immediateOtherSecond = PMF.pure immediateOtherEmpty := by
  change (PMF.pure (.wait : app.Command)).bind _ = _
  simp only [PMF.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  rfl

private theorem round_immediate_tick1 : app.round scheduler (players alpha nonnegative small)
    immediateEmptyInclude = PMF.pure immediateTick1 := by
  change (PMF.pure (.application .advanceClock : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch,
    WaitRiskConfounding.advance_law (runtime setup) leaks, PMF.pure_bind]
  rfl

private theorem round_immediate_other_tick1 : app.round scheduler (players alpha nonnegative small)
    immediateOtherEmpty = PMF.pure immediateOtherTick1 := by
  change (PMF.pure (.application .advanceClock : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch,
    WaitRiskConfounding.advance_law (runtime setup) leaks, PMF.pure_bind]
  rfl

private theorem round_immediate_tick2 : app.round scheduler (players alpha nonnegative small)
    immediateTick1 = PMF.pure immediateBeforeExpiry := by
  change (PMF.pure (.application .advanceClock : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch,
    WaitRiskConfounding.advance_law (runtime setup) leaks, PMF.pure_bind]
  rfl

private theorem round_immediate_other_tick2 : app.round scheduler (players alpha nonnegative small)
    immediateOtherTick1 = PMF.pure immediateOtherBeforeExpiry := by
  change (PMF.pure (.application .advanceClock : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch,
    WaitRiskConfounding.advance_law (runtime setup) leaks, PMF.pure_bind]
  rfl

private theorem immediate_expiry : immediateBeforeExpiry.environmentStep app
    (.application (.expire binding)) = PMF.pure immediateAfterExpiry := by
  have completed : binding ∈ immediateAccepted.application.config.cut.completed := by
    rw [immediateAccepted_config]
    decide
  have notReady : ¬immediateBeforeExpiry.application.config.cut.Ready binding :=
    fun ready => ready.1 completed
  change ((environmentStep (runtime setup) immediateBeforeExpiry.application (.expire binding)).map
    _).map _ = _
  rw [environmentStep_expire_of_not_ready (runtime setup) _ binding notReady,
    PMF.pure_map, PMF.pure_map]
  rfl

private theorem immediate_other_expiry : immediateOtherBeforeExpiry.environmentStep app
    (.application (.expire binding)) = PMF.pure immediateOtherAfterExpiry := by
  have notReady : ¬immediateOtherBeforeExpiry.application.config.cut.Ready binding := by
    intro ready
    have bad : ¬immediateBeforeExpiry.application.config.cut.Ready binding := by
      change ¬immediateAccepted.application.config.cut.Ready binding
      rw [immediateAccepted_config]
      decide
    exact bad ready
  change ((environmentStep (runtime setup) immediateOtherBeforeExpiry.application
    (.expire binding)).map _).map _ = _
  rw [environmentStep_expire_of_not_ready (runtime setup) _ binding notReady,
    PMF.pure_map, PMF.pure_map]
  rfl

private theorem round_immediate_expiry : app.round scheduler (players alpha nonnegative small)
    immediateBeforeExpiry = PMF.pure immediateAfterExpiry := by
  change (PMF.pure (.application (.expire binding) : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch, immediate_expiry, PMF.pure_bind]
  rfl

private theorem round_immediate_other_expiry : app.round scheduler (players alpha nonnegative small)
    immediateOtherBeforeExpiry = PMF.pure immediateOtherAfterExpiry := by
  change (PMF.pure (.application (.expire binding) : app.Command)).bind _ = _
  rw [PMF.pure_bind, ReactiveApplication.dispatch, immediate_other_expiry, PMF.pure_bind]
  rfl

/-- All four branches of the actual initialized ten-round law. -/
theorem rounds10 :
    app.roundsFrom (initialLaw setup) scheduler (players alpha nonnegative small) 10 =
    mix alpha nonnegative small
      (mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure cleanAfterExpiry)
        (PMF.pure riskyAfterExpiry))
      (mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure immediateAfterExpiry)
        (PMF.pure immediateOtherAfterExpiry)) := by
  rw [app.roundsFrom_succ (initialLaw setup) scheduler (players alpha nonnegative small) 9,
    app.roundsFrom_succ (initialLaw setup) scheduler (players alpha nonnegative small) 8,
    app.roundsFrom_succ (initialLaw setup) scheduler (players alpha nonnegative small) 7,
    app.roundsFrom_succ (initialLaw setup) scheduler (players alpha nonnegative small) 6,
    app.roundsFrom_succ (initialLaw setup) scheduler (players alpha nonnegative small) 5,
    app.roundsFrom_succ (initialLaw setup) scheduler (players alpha nonnegative small) 4,
    rounds4, mix_bind, PMF.pure_bind, PMF.pure_bind, round_fork, round_immediate_fork]
  simp only [mix_bind, PMF.pure_bind, round_clean_tick, round_risky_response,
    round_immediate_tick, round_immediate_other, round_clean_include, round_risky_include,
    round_immediate_empty, round_immediate_other_empty, round_clean_tick1, round_risky_tick1,
    round_immediate_tick1, round_immediate_other_tick1, round_clean_tick2, round_risky_tick2,
    round_immediate_tick2, round_immediate_other_tick2, round_clean_expiry, round_risky_expiry,
    round_immediate_expiry, round_immediate_other_expiry]

/-- The actual next scheduler/environment step, before Bob responds. -/
def beforeBob : PMF app.Execution :=
  (app.roundsFrom (initialLaw setup) scheduler (players alpha nonnegative small) 10).bind
    fun execution => (scheduler execution.environmentRecall (execution.observeEnvironment app)).bind
      (execution.environmentStep app)

theorem beforeBob_eq : beforeBob alpha nonnegative small = mix alpha nonnegative small
    (mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure cleanBob) (PMF.pure riskyBob))
    (mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure immediateBob)
      (PMF.pure immediateOtherBob)) := by
  rw [beforeBob, rounds10]
  simp_rw [mix_bind, PMF.pure_bind]
  change mix alpha nonnegative small (mix (1 / 2) _ _
    ((PMF.pure (.activate bob : app.Command)).bind (cleanAfterExpiry.environmentStep app))
    ((PMF.pure (.activate bob : app.Command)).bind (riskyAfterExpiry.environmentStep app)))
    (mix (1 / 2) _ _
      ((PMF.pure (.activate bob : app.Command)).bind (immediateAfterExpiry.environmentStep app))
      ((PMF.pure (.activate bob : app.Command)).bind
        (immediateOtherAfterExpiry.environmentStep app))) = _
  simp_rw [PMF.pure_bind, WaitRiskConfounding.activate_empty_law (runtime setup) leaks _ bob rfl]
  rfl

theorem immediateOtherBob_input_eq :
    (immediateOtherBob.recall bob, immediateOtherBob.observe app bob) =
      (immediateBob.recall bob, immediateBob.observe app bob) := rfl

def immediateInput : BobInput := (immediateBob.recall bob, immediateBob.observe app bob)

def riskReadout (execution : app.Execution) : BobInput × Bool :=
  ((execution.recall bob, execution.observe app bob),
    (runtime setup).persistentServiceRisk leaks bound alice
      (execution.recall alice) (execution.observe app alice))

def joint : PMF (BobInput × Bool) := (beforeBob alpha nonnegative small).map riskReadout

def immediateJoint : PMF (BobInput × Bool) :=
  mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure (riskReadout immediateBob))
    (PMF.pure (riskReadout immediateOtherBob))

/-- The actual rare delayed fiber is accompanied by both private-risk outcomes,
while the more frequent immediate branch has a different observed input. -/
theorem joint_eq : joint alpha nonnegative small = mix alpha nonnegative small
    (fairRisk.map (fun risk => (bobInput, risk))) immediateJoint := by
  rw [joint, beforeBob_eq, mix_map, mix_map, mix_map,
    PMF.pure_map, PMF.pure_map, PMF.pure_map, PMF.pure_map]
  change mix alpha nonnegative small
    (mix (1 / 2) _ _ (PMF.pure ((cleanBob.recall bob, cleanBob.observe app bob),
      (runtime setup).persistentServiceRisk leaks bound alice (cleanBob.recall alice)
        (cleanBob.observe app alice)))
      (PMF.pure ((riskyBob.recall bob, riskyBob.observe app bob),
        (runtime setup).persistentServiceRisk leaks bound alice (riskyBob.recall alice)
          (riskyBob.observe app alice)))) _ = _
  rw [cleanBob_persistent_clear alice, riskyBob_persistent_risk, ← bob_input_eq]
  simp only [fairRisk, mix_map, PMF.pure_map]
  rfl

private theorem immediate_ne_late : immediateInput ≠ bobInput := immediateBob_input_ne_clean

private theorem immediateJoint_marginal_zero :
    (immediateJoint.map Prod.fst) bobInput = 0 := by
  classical
  have same : (riskReadout immediateOtherBob).1 = immediateInput := immediateOtherBob_input_eq
  simp only [immediateJoint, mix_map, PMF.pure_map]
  change mix (1 / 2) _ _ (PMF.pure immediateInput)
    (PMF.pure (riskReadout immediateOtherBob).1) bobInput = 0
  rw [same]
  simp [PMF.pure_apply, Ne.symm immediate_ne_late]

private theorem immediateJoint_atom_zero (risk : Bool) : immediateJoint (bobInput, risk) = 0 := by
  classical
  have first : (bobInput, risk) ≠ riskReadout immediateBob := by
    intro same
    exact immediate_ne_late (congrArg Prod.fst same).symm
  have second : (bobInput, risk) ≠ riskReadout immediateOtherBob := by
    intro same
    have projected := congrArg Prod.fst same
    change bobInput = (immediateOtherBob.recall bob, immediateOtherBob.observe app bob) at projected
    rw [immediateOtherBob_input_eq] at projected
    exact immediate_ne_late projected.symm
  simp [immediateJoint, PMF.pure_apply, first, second]

/-- The delayed information fiber has exactly the initial WAIT mass. -/
theorem joint_late_mass : ((joint alpha nonnegative small).map Prod.fst) bobInput =
    ENNReal.ofReal alpha := by
  rw [joint_eq, mix_map, PMF.map_comp]
  have mapped : fairRisk.map (Prod.fst ∘ fun risk => (bobInput, risk)) =
      PMF.pure bobInput := by
    exact PMF.map_const fairRisk bobInput
  rw [mapped, mix_apply, immediateJoint_marginal_zero]
  simp only [PMF.pure_apply_self, mul_one, mul_zero, add_zero]

/-- Conditioning on that actual fiber cancels the initial WAIT mass. -/
theorem joint_late_posterior (positive : 0 < alpha) :
    (fiberPosterior (joint alpha nonnegative small) Prod.fst bobInput).map Prod.snd = fairRisk := by
  classical
  have support : bobInput ∈ ((joint alpha nonnegative small).map Prod.fst).support := by
    rw [PMF.mem_support_iff, joint_late_mass]
    exact (ENNReal.ofReal_pos.mpr positive).ne'
  ext risk
  rw [fiberPosterior_map_snd_apply _ _ support, joint_late_mass,
    joint_eq, mix_apply, immediateJoint_atom_zero, mul_zero, add_zero]
  have atom : (fairRisk.map (fun risk => (bobInput, risk))) (bobInput, risk) = fairRisk risk := by
    rw [PMF.map_apply, tsum_eq_single risk]
    · simp
    · intro other different
      have pair : (bobInput, risk) ≠ (bobInput, other) := by simpa using Ne.symm different
      simp [pair]
  rw [atom]
  have nonzero : ENNReal.ofReal alpha ≠ 0 := (ENNReal.ofReal_pos.mpr positive).ne'
  calc
    ENNReal.ofReal alpha * fairRisk risk * (ENNReal.ofReal alpha)⁻¹ =
        (ENNReal.ofReal alpha * (ENNReal.ofReal alpha)⁻¹) * fairRisk risk := by ac_rfl
    _ = fairRisk risk := by rw [ENNReal.mul_inv_cancel nonzero ENNReal.ofReal_ne_top, one_mul]

/-- At every positive initial WAIT rate, the actual conditional private-risk
mass is one half; this says nothing about rational free continuation. -/
theorem joint_late_risk_half (positive : 0 < alpha) :
    (((fiberPosterior (joint alpha nonnegative small) Prod.fst bobInput).map Prod.snd)
      true).toReal = 1 / 2 := by
  rw [joint_late_posterior alpha nonnegative small positive]
  simp only [fairRisk, mix_apply_toReal, PMF.pure_apply,
    Bool.true_eq_false, ite_false, ite_true, ENNReal.toReal_zero, ENNReal.toReal_one]
  norm_num

end Vegas.OpaqueBindingFork.VanishingWait
