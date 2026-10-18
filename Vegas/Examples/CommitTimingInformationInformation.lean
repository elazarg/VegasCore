/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitTimingInformationInitialGeometry
import Interaction.ReactiveCompleteObservation
import Interaction.ReactiveMessageReadout
import Interaction.ReactiveRoundTrace

/-! # Full native inputs on the two sides of the private clock-two poll

The executions retain their different environment histories and foreign own
words. The equalities concern the entire focal own word and native view.
-/

noncomputable section

namespace Vegas.Examples.CommitTimingInformation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

/-- The deterministic complete-pending activation of the existing runtime. -/
def completeActivation (execution : app.Execution) (owner : Player) : app.Execution :=
  execution.sampledActivation app owner (execution.network.pending.map Message.id).toFinset

theorem completeActivation_law (execution : app.Execution) (owner : Player) :
    execution.environmentStep app (.activate owner) =
      PMF.pure (completeActivation execution owner) := by
  rw [ReactiveApplication.Execution.activation_samples]
  change (MessageNetwork.completePendingObservation owner execution.network.pending).map _ = _
  simp only [MessageNetwork.completePendingObservation, PMF.pure_map, completeActivation]

/-- An actual passive command records its full environment entry. -/
def pause (execution : app.Execution) : app.Execution :=
  { execution with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .wait⟩] }

theorem pause_law (execution : app.Execution) :
    execution.environmentStep app .wait = PMF.pure (pause execution) := by
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map, pause]

/-- The actual native clock transition, including phase normalization. -/
def advance (execution : app.Execution) : app.Execution :=
  PhaseRuntimeState.normalizeExecution runtime leaks (PhaseBindingRepair.rawClock runtime leaks
    execution)

theorem advance_law (execution : app.Execution) :
    execution.environmentStep app (.application .advanceClock) = PMF.pure (advance execution) :=
  PhaseBindingRepair.clock_environment runtime leaks execution

theorem advance_application (execution : app.Execution) (bit : Bool) (clock : Nat)
    (state : execution.application = quietApplication bit clock) :
    (advance execution).application = quietApplication bit (clock + 1) := by
  change (PhaseBindingRepair.rawClock runtime leaks execution).application.normalize = _
  have updated : (PhaseBindingRepair.rawClock runtime leaks execution).application =
      quietApplication bit (clock + 1) := by
    change { execution.application with current := { execution.application.current with native :=
      { execution.application.current.native with
        clock := execution.application.current.native.clock + 1 } } } = _
    rw [state]
    rfl
  rw [updated, quietApplication_normalize]

def nativeInput (owner : Player) (execution : app.Execution) :
    List app.PlayerEntry × app.PlayerView :=
  (execution.recall owner, execution.observe app owner)

def aliceFirst (bit : Bool) : app.Execution :=
  completeActivation (initialExecution bit) alice

def aliceResponded (bit : Bool) (response : app.Action) : app.Execution :=
  (aliceFirst bit).respond app alice response

/-- The real four-command prefix, with Alice's initial action retained. -/
def quietStart (bit : Bool) : app.Execution :=
  advance (pause (advance (aliceResponded bit ⟨none⟩)))

def aliceEmptyGood (bit : Bool) : app.Execution :=
  completeActivation (quietStart bit) alice

def bobAfterGood (bit : Bool) (response : app.Action) : app.Execution :=
  completeActivation ((aliceEmptyGood bit).respond app alice response) bob

def bobBeforeBad (bit : Bool) : app.Execution :=
  completeActivation (pause (quietStart bit)) bob

def aliceEmptyBad (bit : Bool) : app.Execution :=
  completeActivation (pause ((bobBeforeBad bit).respond app bob ⟨none⟩)) alice

theorem aliceFirst_application (bit : Bool) :
    (aliceFirst bit).application = initialState bit := rfl

theorem aliceFirst_network (bit : Bool) :
    (aliceFirst bit).network = MessageNetwork.empty := by
  simp only [aliceFirst, completeActivation, initialExecution,
    ReactiveApplication.Execution.initial, ReactiveApplication.Execution.sampledActivation,
    MessageNetwork.empty, List.map_nil, List.toFinset_nil, MessageNetwork.learn_empty]

theorem aliceFirst_recall (bit : Bool) (owner : Player) :
    (aliceFirst bit).recall owner = [] := rfl

theorem aliceFirst_length (bit : Bool) :
    (aliceFirst bit).environmentRecall.length = 1 := rfl

theorem aliceResponded_public (bit : Bool) (response : app.Action) :
    (aliceResponded bit response).application.publicView = (initialState bit).publicView := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some submission =>
      change (PhaseRuntimeState.submit (initialState bit) alice submission).publicView = _
      simp only [PhaseRuntimeState.submit, PhaseRuntimeState.publicView, RecoveryState.submit,
        submitStep_publicView, (submission.call.register_facts alice
          (initialState bit).current.native).2, PhaseRuntimeState.attempt]

theorem quietStart_application (bit : Bool) :
    (quietStart bit).application = quietApplication bit 2 := by
  apply advance_application _ bit 1
  change (advance (aliceResponded bit ⟨none⟩)).application = quietApplication bit 1
  apply advance_application _ bit 0
  change initialState bit = quietApplication bit 0
  rw [quietApplication, initialState_eq]
  rfl

theorem quietStart_network (bit : Bool) :
    (quietStart bit).network = MessageNetwork.empty := by
  change (aliceFirst bit).network = _
  exact aliceFirst_network bit

theorem quietStart_receipts (bit : Bool) : (quietStart bit).receipts = [] := rfl

theorem quietStart_length (bit : Bool) :
    (quietStart bit).environmentRecall.length = 4 := rfl

theorem quietStart_attempt (bit : Bool) :
    (quietStart bit).application.attempt = originalAttempt := by
  rw [quietStart_application]
  exact initialState_attempt bit

theorem quietStart_ready (bit : Bool) (owner : Player) :
    ready owner (bindingEvent owner) ((quietStart bit).observeEnvironment app) = true := by
  classical
  change decide (PhaseRuntimeState.requests (quietStart bit).application.publicView owner
    ⟨(quietStart bit).application.attempt, bindingEvent owner⟩) = true
  rw [quietStart_application]
  change ready owner (bindingEvent owner) ((initialExecution bit).observeEnvironment app) = true
  exact initial_bindings_ready bit owner

/-- A passive command may alter the environment log but no player input. -/
theorem nativeInput_pause (owner : Player) (execution : app.Execution) :
    nativeInput owner (pause execution) = nativeInput owner execution := rfl

private theorem initial_native_alice_observation (first second : Bool) :
    graph.playerObserve alice (Config.initial (encodeInputs (sourceInitial first))) =
      graph.playerObserve alice (Config.initial (encodeInputs (sourceInitial second))) := by
  refine graph.playerObserve_congr alice _ _ rfl ?_
  intro field visible
  cases field with
  | inl input =>
      change Fin 1 at input
      fin_cases input
      change bob = alice at visible
      exact False.elim ((show bob ≠ alice by decide) visible)
  | inr event => rfl

theorem initial_alice_playerView (first second : Bool) :
    (initialState first).playerView alice = (initialState second).playerView alice := by
  have observed := initial_native_alice_observation first second
  have publics := State.initial_publicView_eq_of_observation alice _ _ observed
  have candidates := State.initial_candidates_eq_of_observation alice _ _ observed
  have native :
      (State.initial (graph := graph) (encodeInputs (sourceInitial first))).playerView alice =
      (State.initial (graph := graph) (encodeInputs (sourceInitial second))).playerView alice := by
    change PlayerView.mk alice (State.initial (graph := graph) _).publicView
      (graph.playerObserve alice (Config.initial (encodeInputs (sourceInitial first))))
      (fun slot => (State.initial (graph := graph) _).candidates.lookup (alice, slot)) =
        PlayerView.mk alice (State.initial (graph := graph) _).publicView
          (graph.playerObserve alice (Config.initial (encodeInputs (sourceInitial second))))
          (fun slot => (State.initial (graph := graph) _).candidates.lookup (alice, slot))
    rw [publics, observed, candidates]
  rw [initialState_eq, initialState_eq]
  change ((State.initial (graph := graph) (encodeInputs (sourceInitial first))).playerView alice,
    PhasePublicView.mk
      (State.initial (graph := graph) (encodeInputs (sourceInitial first))).publicView
      ∅ (some (.commitment, 0, 2)) originalAttempt []) =
    ((State.initial (graph := graph) (encodeInputs (sourceInitial second))).playerView alice,
      PhasePublicView.mk
        (State.initial (graph := graph) (encodeInputs (sourceInitial second))).publicView
        ∅ (some (.commitment, 0, 2)) originalAttempt [])
  rw [native, publics]

theorem aliceFirst_input_independent (first second : Bool) :
    nativeInput alice (aliceFirst first) = nativeInput alice (aliceFirst second) := by
  unfold nativeInput
  rw [aliceFirst_recall, aliceFirst_recall]
  unfold ReactiveApplication.Execution.observe
  rw [aliceFirst_network, aliceFirst_network, aliceFirst_application, aliceFirst_application]
  exact congrArg (fun view => ([], ReactiveApplication.PlayerView.mk
    (MessageNetwork.empty.observe alice) view [])) (initial_alice_playerView first second)

/-- Before Bob's decision and after his literal WAIT, Alice has identical
complete native information, including her retained initial WAIT record. -/
theorem alice_clock_two_empty_input (bit : Bool) :
    nativeInput alice (aliceEmptyGood bit) = nativeInput alice (aliceEmptyBad bit) := by
  have network := quietStart_network bit
  simp only [aliceEmptyGood, aliceEmptyBad, bobBeforeBad, completeActivation, pause,
    ReactiveApplication.Execution.sampledActivation, ReactiveApplication.Execution.respond,
    nativeInput, ReactiveApplication.Execution.observe, ite_false,
    show alice ≠ bob by decide,
    network, MessageNetwork.empty, List.map_nil, List.toFinset_nil,
    MessageNetwork.learn_empty]

/-- Bob cannot distinguish good Alice having waited from bad Alice not yet
having her clock-two callback. His immutable private bit remains unchanged. -/
theorem bob_clock_two_quiet_input (bit : Bool) :
    nativeInput bob (bobAfterGood bit ⟨none⟩) =
      nativeInput bob (bobBeforeBad bit) := by
  have network := quietStart_network bit
  simp only [bobAfterGood, aliceEmptyGood, bobBeforeBad, completeActivation, pause,
    ReactiveApplication.Execution.sampledActivation, ReactiveApplication.Execution.respond,
    nativeInput, ReactiveApplication.Execution.observe, ite_false,
    show bob ≠ alice by decide,
    network, MessageNetwork.empty, List.map_nil, List.toFinset_nil,
    MessageNetwork.learn_empty]

theorem family_first (seed : Seeds) (bit : Bool) :
    family seed (initialExecution bit).environmentRecall
      ((initialExecution bit).observeEnvironment app) = PMF.pure (.activate alice) := by
  change PMF.pure (choose seed _ _) = _
  rw [choose_original seed _ _ (initialState_attempt bit)]
  change PMF.pure (activateReady alice (bindingEvent alice) _) = _
  rw [activateReady, initial_bindings_ready]
  rfl

/-- The first action law is evaluated at Alice's actual uninformed full input. -/
theorem first_round (seed : Seeds) (bit : Bool) (players : Player → app.Policy) :
    app.round (family seed) players (initialExecution bit) =
      (players alice ((aliceFirst bit).recall alice) ((aliceFirst bit).observe app alice)).map
        ((aliceFirst bit).respond app alice) := by
  rw [ReactiveApplication.round, family_first, PMF.pure_bind,
    ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind]
  rfl

end Vegas.Examples.CommitTimingInformation
