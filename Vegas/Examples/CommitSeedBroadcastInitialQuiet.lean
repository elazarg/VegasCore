/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastService
import Vegas.Pending.PhaseBindingClockReplay
import Interaction.ReactiveCompleteObservation

/-! # The actual quiet initial prefix before the independent callback groups -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

def initialExecution : app.Execution := ReactiveApplication.Execution.initial app initialState

def completeActivation (execution : app.Execution) (owner : Player) : app.Execution :=
  execution.sampledActivation app owner (execution.network.pending.map Message.id).toFinset

theorem completeActivation_law (execution : app.Execution) (owner : Player) :
    execution.environmentStep app (.activate owner) =
      PMF.pure (completeActivation execution owner) := by
  rw [ReactiveApplication.Execution.activation_samples]
  change (MessageNetwork.completePendingObservation owner execution.network.pending).map _ = _
  simp only [MessageNetwork.completePendingObservation, PMF.pure_map, completeActivation]

def quietResponse (execution : app.Execution) (owner : Player) : app.Execution :=
  (completeActivation execution owner).respond app owner ⟨none⟩

def quietAfterCallbacks : app.Execution :=
  quietResponse (quietResponse (quietResponse initialExecution alice) bob) carol

def initialBefore (owner : Player) : app.Execution :=
  if owner = alice then initialExecution else
    if owner = bob then quietResponse initialExecution alice else
      quietResponse (quietResponse initialExecution alice) bob

def initialCallback (owner : Player) : app.Execution :=
  completeActivation (initialBefore owner) owner

private theorem quietResponse_application (execution : app.Execution) (owner : Player) :
    (quietResponse execution owner).application = execution.application := rfl

private theorem quietResponse_environmentRecall (execution : app.Execution) (owner : Player) :
    (quietResponse execution owner).environmentRecall = execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .activate owner⟩] := rfl

private theorem initialBefore_application (owner : Player) :
    (initialBefore owner).application = initialState := by
  fin_cases owner <;> rfl

private theorem initialBefore_length (owner : Player) :
    (initialBefore owner).environmentRecall.length = owner.val := by
  fin_cases owner <;> rfl

private theorem ready_initial (owner : Player) :
    ready owner (bindingEvent owner) (initialExecution.observeEnvironment app) = true := by
  simp only [ready, decide_eq_true_eq]
  change PhaseRuntimeState.requests initialState.publicView owner
    ⟨initialState.attempt, bindingEvent owner⟩
  rw [initialState_attempt]
  exact initial_bindings_ready owner

theorem family_initial_callback (seed : Seeds) (owner : Player) :
    family seed (initialBefore owner).environmentRecall
      ((initialBefore owner).observeEnvironment app) = PMF.pure (.activate owner) := by
  classical
  have original : ((initialBefore owner).observeEnvironment app).application.attempt =
      originalAttempt := by
    change (initialBefore owner).application.attempt = originalAttempt
    rw [initialBefore_application, initialState_attempt]
  change PMF.pure (choose seed _ _) = _
  rw [choose_original seed _ _ original, initialBefore_length]
  have eligible : ready owner (bindingEvent owner)
      ((initialBefore owner).observeEnvironment app) = true := by
    change decide (PhaseRuntimeState.requests (initialBefore owner).application.publicView owner
      ⟨(initialBefore owner).application.attempt, bindingEvent owner⟩) = true
    rw [initialBefore_application]
    exact ready_initial owner
  have activated : activateReady owner (bindingEvent owner)
      ((initialBefore owner).observeEnvironment app) = .activate owner := by
    rw [activateReady, eligible]
    rfl
  fin_cases owner <;> exact congrArg PMF.pure activated

/-- The clock update uses the existing application transition and normalizer. -/
def advance (execution : app.Execution) : app.Execution :=
  PhaseRuntimeState.normalizeExecution runtime leaks (PhaseBindingRepair.rawClock runtime leaks
    execution)

theorem advance_law (execution : app.Execution) :
    execution.environmentStep app (.application .advanceClock) = PMF.pure (advance execution) :=
  PhaseBindingRepair.clock_environment runtime leaks execution

def quietApplication (clock : Nat) : app.State :=
  { initialState with current := { initialState.current with native :=
      { initialState.current.native with clock := clock } } }

private theorem quietApplication_normalize (clock : Nat) :
    (quietApplication clock).normalize = quietApplication clock := by
  let native : EventGraphRuntime.State graph :=
    { State.initial (encodeInputs (Env.empty (CellVal simpleExpr))) with clock := clock }
  have shaped : quietApplication clock =
      ⟨[commitmentPhase, publicationPhase], 0,
        ⟨State.initial (encodeInputs (Env.empty (CellVal simpleExpr))), ∅⟩,
        ⟨native, ∅⟩, []⟩ := by rw [quietApplication, initialState_eq]
  have drained : commitmentPhase.drain (⟨native, ∅⟩ : RecoveryState graph) = ⟨native, ∅⟩ := by
    apply RuntimePhase.drain_eq_of_clear
    intro event eligible
    rcases eligible.2 with ⟨_ready, excluded⟩
    cases actor : graph.actor? event <;> simp [actor] at excluded
  have unfinished : ¬ commitmentPhase.Finished (⟨native, ∅⟩ : RecoveryState graph) := by
    intro finished
    have inside : bindingEvent alice ∈ commitmentPhase.events := by
      apply (RuntimePhase.mem_events commitmentPhase _).mpr
      change 0 ≤ 0 ∧ 0 < 3
      omega
    have member := finished inside
    change bindingEvent alice ∈ (∅ : Finset graph.EventId) at member
    exact Finset.notMem_empty _ member
  rw [shaped, PhaseRuntimeState.normalize, PhaseRuntimeState.settle, drained,
    ite_eq_right unfinished]

private theorem advance_application (execution : app.Execution) (clock : Nat)
    (state : execution.application = quietApplication clock) :
    (advance execution).application = quietApplication (clock + 1) := by
  change (PhaseBindingRepair.rawClock runtime leaks execution).application.normalize = _
  have updated : (PhaseBindingRepair.rawClock runtime leaks execution).application =
      quietApplication (clock + 1) := by
    change { execution.application with current := { execution.application.current with native :=
      { execution.application.current.native with
        clock := execution.application.current.native.clock + 1 } } } = _
    rw [state]
    rfl
  rw [updated, quietApplication_normalize]

private theorem advance_network (execution : app.Execution) :
    (advance execution).network = execution.network := rfl

private theorem advance_recall (execution : app.Execution) (owner : Player) :
    (advance execution).recall owner = execution.recall owner := rfl

private theorem advance_environmentRecall (execution : app.Execution) :
    (advance execution).environmentRecall = execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .application .advanceClock⟩] := rfl

def quietStart : app.Execution := advance (advance quietAfterCallbacks)

private theorem quietAfterCallbacks_application :
    quietAfterCallbacks.application = quietApplication 0 := by
  change initialState = quietApplication 0
  rw [quietApplication, initialState_eq]
  rfl

theorem quietStart_application : quietStart.application = quietApplication 2 :=
  advance_application _ 1 (advance_application _ 0 quietAfterCallbacks_application)

theorem quietStart_clock : quietStart.application.current.native.clock = 2 := by
  rw [quietStart_application]
  rfl

theorem quietStart_attempt : quietStart.application.attempt = originalAttempt := by
  rw [quietStart_application]
  exact initialState_attempt

theorem quietStart_requests (owner : Player) :
    quietStart.application.SeedRequest owner (originalCoordinate owner) := by
  rw [quietStart_application]
  have original := initial_bindings_ready owner
  have valid := (PhaseRuntimeState.initial_invariant plan
    (encodeInputs (Env.empty (CellVal simpleExpr)))).1
  rw [initialState.requests_publicView valid] at original
  exact original

theorem quietStart_public_requests (owner : Player) :
    PhaseRuntimeState.requests quietStart.application.publicView owner
      (originalCoordinate owner) := by
  rw [quietStart_application]
  exact initial_bindings_ready owner

theorem quietStart_network : quietStart.network = MessageNetwork.empty := by
  simp only [quietStart, advance_network, quietAfterCallbacks, quietResponse,
    ReactiveApplication.Execution.respond, completeActivation,
    ReactiveApplication.Execution.sampledActivation, initialExecution,
    ReactiveApplication.Execution.initial, MessageNetwork.empty, List.map_nil,
    List.toFinset_nil, MessageNetwork.learn_empty]

theorem quietStart_length : quietStart.environmentRecall.length = 5 := by
  rw [quietStart, advance_environmentRecall, List.length_append, List.length_singleton,
    advance_environmentRecall, List.length_append, List.length_singleton]
  rfl

theorem quietStart_inputs : quietStart.network.inputs = [] := by
  rw [quietStart_network]
  rfl

theorem quietStart_early_snapshot : ∃ entry, quietStart.environmentRecall[3]? = some entry ∧
    entry.beforeView.network.inputs = [] := by
  refine ⟨⟨quietAfterCallbacks.observeEnvironment app, .application .advanceClock⟩, rfl, ?_⟩
  change quietAfterCallbacks.network.inputs = []
  have empty : quietAfterCallbacks.network = MessageNetwork.empty := by
    simpa only [quietStart, advance_network] using quietStart_network
  rw [empty]
  rfl

private theorem initial_quiet_round (seed : Seeds) (players : Player → app.Policy)
    (owner : Player)
    (waited : players owner ((initialCallback owner).recall owner)
      ((initialCallback owner).observe app owner) = PMF.pure ⟨none⟩) :
    app.round (family seed) players (initialBefore owner) =
      PMF.pure (quietResponse (initialBefore owner) owner) := by
  rw [ReactiveApplication.round, family_initial_callback, PMF.pure_bind,
    ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind]
  change (players owner ((initialCallback owner).recall owner)
    ((initialCallback owner).observe app owner)).map
      ((initialCallback owner).respond app owner) = _
  rw [waited, PMF.pure_map]
  rfl

/-- Three actual player WAIT laws give the literal quiet callback prefix. -/
theorem quiet_callbacks_law (seed : Seeds) (players : Player → app.Policy)
    (waited : ∀ owner, players owner ((initialCallback owner).recall owner)
      ((initialCallback owner).observe app owner) = PMF.pure ⟨none⟩) :
    app.runRounds (family seed) players 3 initialExecution = PMF.pure quietAfterCallbacks := by
  have first := initial_quiet_round seed players alice (waited alice)
  have second := initial_quiet_round seed players bob (waited bob)
  have third := initial_quiet_round seed players carol (waited carol)
  change app.round (family seed) players initialExecution =
    PMF.pure (quietResponse initialExecution alice) at first
  change app.round (family seed) players (quietResponse initialExecution alice) =
    PMF.pure (quietResponse (quietResponse initialExecution alice) bob) at second
  change app.round (family seed) players
    (quietResponse (quietResponse initialExecution alice) bob) = PMF.pure quietAfterCallbacks
      at third
  rw [ReactiveApplication.runRounds, first, PMF.pure_bind,
    ReactiveApplication.runRounds, second, PMF.pure_bind,
    ReactiveApplication.runRounds, third, PMF.pure_bind, ReactiveApplication.runRounds]

private theorem family_initial_advance (seed : Seeds) (execution : app.Execution)
    (original : execution.application.attempt = originalAttempt)
    (length : execution.environmentRecall.length = 3 ∨ execution.environmentRecall.length = 4) :
    family seed execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure (.application .advanceClock) := by
  change PMF.pure (choose seed _ _) = _
  rw [choose_original seed _ _ original]
  rcases length with length | length <;> rw [length] <;> rfl

private theorem quiet_advance_round (seed : Seeds) (players : Player → app.Policy)
    (execution : app.Execution) (original : execution.application.attempt = originalAttempt)
    (length : execution.environmentRecall.length = 3 ∨ execution.environmentRecall.length = 4) :
    app.round (family seed) players execution = PMF.pure (advance execution) := by
  rw [ReactiveApplication.round, family_initial_advance seed execution original length,
    PMF.pure_bind, ReactiveApplication.dispatch, advance_law, PMF.pure_bind]
  rfl

/-- No Nature or timing table is refreshed: the real first five rounds are pure. -/
theorem quietStart_law (seed : Seeds) (players : Player → app.Policy)
    (waited : ∀ owner, players owner ((initialCallback owner).recall owner)
      ((initialCallback owner).observe app owner) = PMF.pure ⟨none⟩) :
    app.runRounds (family seed) players 5 initialExecution = PMF.pure quietStart := by
  have first := quiet_advance_round seed players quietAfterCallbacks (by
    change initialState.attempt = originalAttempt
    exact initialState_attempt) (Or.inl rfl)
  have second := quiet_advance_round seed players (advance quietAfterCallbacks) (by
    rw [advance_application _ 0 quietAfterCallbacks_application]
    exact initialState_attempt) (Or.inr (by
    rw [advance_environmentRecall, List.length_append, List.length_singleton]
    rfl))
  rw [show 5 = 3 + 2 by decide, app.runRounds_add, quiet_callbacks_law seed players waited,
    PMF.pure_bind, ReactiveApplication.runRounds, first, PMF.pure_bind,
    ReactiveApplication.runRounds, second, PMF.pure_bind, ReactiveApplication.runRounds]
  rfl

end Vegas.Examples.CommitSeedBroadcast
