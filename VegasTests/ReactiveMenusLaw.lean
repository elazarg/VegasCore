/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.ReactiveMenus

/-! # The reactive continuation loses access to every third binding value -/

noncomputable section

namespace VegasTests.ReactiveMenus

open GameTheory.Protocol GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime

def beforeResponse (bit : Bool) : app.Execution := activate (delivered contested bit)
def response (bit : Bool) (action : app.Action) : app.Execution :=
  (beforeResponse bit).respond app () action
def selected (bit : Bool) (action : app.Action) : app.Execution :=
  included (response bit action) (selectedId (response bit action).network)
def selectedValue (bit : Bool) (action : app.Action) : Int :=
  if ((response bit action).network.lookup ((), 2)).isSome == signal (response bit action).network
    then 1 else 2

private theorem respond_lookup (execution : app.Execution) (action : app.Action)
    (id : MessageId Unit) (message : Message Unit (Payload graph))
    (pending : execution.network.lookup id = some message) :
    (execution.respond app () action).network.lookup id = some message := by
  change execution.network.pending.find? (fun message => message.id = id) = some message at pending
  rcases action with ⟨memory, transmission⟩
  cases transmission with
  | none => exact pending
  | some transmission =>
      cases transmission with
      | submit material =>
          simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit,
            MessageNetwork.lookup, List.find?_append, pending, Option.some_or]
      | replay replayId =>
          change (execution.network.replay () replayId).2.lookup id = some message
          unfold MessageNetwork.replay
          split
          · exact pending
          · simp only [MessageNetwork.lookup, List.find?_append, pending, Option.some_or]

private theorem old_pending (bit : Bool) (action : app.Action) :
    (response bit action).network.lookup ((), 0) =
        some ⟨((), 0), .commitment 0 ((), .prepared 0)⟩ ∧
      (response bit action).network.lookup ((), 1) =
        some ⟨((), 1), .commitment 0 ((), .prepared 1)⟩ := by
  constructor <;> apply respond_lookup
  all_goals cases bit <;> rfl

private theorem include_value (bit : Bool) (action : app.Action) (serial : Nat) (value : Int)
    (pending : (response bit action).network.lookup ((), serial) =
      some ⟨((), serial), .commitment 0 ((), .prepared serial)⟩)
    (candidate : contested.application.candidates.lookup ((), .prepared serial) =
      .openable ⟨.int, value⟩) :
    (included (response bit action) ((), serial)).application.config.outputs 0 =
      some (.success value) := by
  have facts := runtime.reactive_respond_application (beforeResponse bit) () action
  have initialEq : (beforeResponse bit).application = contested.application := rfl
  rw [initialEq] at facts
  change (response bit action).application.config = contested.application.config ∧
    (response bit action).application.publicView = contested.application.publicView at facts
  have ready : (response bit action).application.config.cut.Ready 0 := by
    exact facts.1 ▸ (by decide : contested.application.config.cut.Ready 0)
  have timely : (response bit action).application.WithinDeadline runtime 0 := by
    have clockEq := congrArg PublicView.clock facts.2
    have activatedEq := congrArg PublicView.activatedAt facts.2
    change (response bit action).application.clock = 0 at clockEq
    change (response bit action).application.activatedAt = _ at activatedEq
    simp only [State.WithinDeadline, clockEq, activatedEq]
    change 0 < 2
    decide
  have vacant : (response bit action).application.accepted (.inr 0) = none :=
    congrArg (fun view : PublicView graph => view.accepted (.inr 0)) facts.2
  have unused : (response bit action).application.HandleUnused ((), .prepared serial) := by
    intro field
    have handles := congrArg (fun view : PublicView graph => view.accepted field) facts.2
    cases field with
    | inl input => exact Fin.elim0 input
    | inr event =>
        change (response bit action).application.accepted (.inr event) = none at handles
        rw [handles]
        intro impossible
        cases impossible
  have meaning := runtime.reactive_respond_candidate_fixed (beforeResponse bit) () action
    ((), .prepared serial) (by rw [initialEq, candidate]; intro impossible; cases impossible)
  rw [initialEq, candidate] at meaning
  change (response bit action).application.candidates.lookup ((), .prepared serial) =
    .openable ⟨.int, value⟩ at meaning
  have valueEq : (response bit action).application.bindingResult
      ((), .prepared serial) .int = .success value := by
    simp only [State.bindingResult, meaning, Raw.as?_mk, Option.elim_some]
  have accepted := handle_commitment_eq runtime (response bit action).application
    ((), serial) 0 ((), .prepared serial) () .int rfl rfl rfl ready timely rfl rfl vacant unused
  change (ReactiveApplication.Execution.includePending app (response bit action)
    ((), serial)).application.config.outputs 0 = _
  simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending, pending]
  change ((handle runtime (response bit action).application
    ⟨((), serial), .commitment 0 ((), .prepared serial)⟩).getD
      (response bit action).application).config.outputs 0 = some (.success value)
  rw [accepted, Option.getD_some]
  change ((response bit action).application.config.complete 0 ready _ _).outputs 0 = _
  rw [EventGraph.Config.complete_output_same, valueEq]
  rfl

theorem selected_binding (bit : Bool) (action : app.Action) :
    (selected bit action).application.config.outputs 0 =
      some (.success (selectedValue bit action)) := by
  unfold selected selectedId selectedValue
  split
  · exact include_value bit action 0 1 (old_pending bit action).1 rfl
  · exact include_value bit action 1 2 (old_pending bit action).2 rfl

theorem contested_invariant : contested.application.Invariant input := by
  have valid := (runtime.reactiveStateInvariant input).history initialLaw horizon scheduler
    (fun state supported => by
      cases FinDist.mem_support_pure.mp supported
      exact State.initial_invariant input) (rootHistory first second).trace
  exact valid

theorem selected_invariant (bit : Bool) (action : app.Action) :
    (selected bit action).application.Invariant input := by
  exact (runtime.reactiveStateInvariant input).includePending (response bit action) _
    ((runtime.reactiveStateInvariant input).respond
      (beforeResponse bit) () action contested_invariant)

theorem selected_rounds_sum_le (bit : Bool) (action : app.Action)
    (players : Unit → app.Policy) (count : Nat) (final : app.Execution)
    (supported : final ∈ (app.runRounds scheduler players count (selected bit action)).support) :
    PendingMenus.publicUtility true (final.application.config.outputs 1) +
      PendingMenus.publicUtility false (final.application.config.outputs 1) ≤ 3 := by
  have valid := ((runtime.reactiveStateInvariant input).policyInvariant app players).runRounds
    scheduler count _ final (selected_invariant bit action) supported
  have stored := ((runtime.reactiveStoreInvariant (.inr 0)
    (.success (selectedValue bit action))).policyInvariant app players).runRounds
      scheduler count _ final (selected_binding bit action) supported
  cases published : final.application.config.outputs 1 with
  | none => norm_num [PendingMenus.publicUtility]
  | some result =>
      cases result with
      | failure => norm_num [PendingMenus.publicUtility]
      | success value =>
          have bindingEq := PendingMenus.publication_matches_binding
            _ valid.reachable value published
          change final.application.config.outputs 0 = some (.success (selectedValue bit action))
            at stored
          have same := PublicationResult.success.inj (Option.some.inj (bindingEq.symm.trans stored))
          rw [same]
          unfold selectedValue
          split <;> norm_num [PendingMenus.publicUtility]

theorem scheduler_three (execution : app.Execution)
    (length : execution.environmentRecall.length = 3) :
    scheduler execution.environmentRecall (execution.observeEnvironment app) =
      (FinDist.uniformOfFintype (α := Bool)).map
        (fun bit => .deliver () (signalId bit)) := by
  unfold scheduler interactionScheduler
  simp only [length]
  change (network execution.environmentRecall (execution.observeEnvironment app)).map
    (NetworkChoice.command runtime) = _
  simp only [network, length]
  change ((FinDist.uniformOfFintype (α := Bool)).map
    (fun bit => NetworkChoice.deliver () (signalId bit))).map _ = _
  rw [FinDist.map_comp]
  rfl

theorem scheduler_four (execution : app.Execution)
    (length : execution.environmentRecall.length = 4) :
    scheduler execution.environmentRecall (execution.observeEnvironment app) =
      FinDist.pure (.activate ()) := by
  unfold scheduler interactionScheduler
  simp only [length]
  change (network execution.environmentRecall (execution.observeEnvironment app)).map
    (NetworkChoice.command runtime) = _
  simp only [network, length]
  change (FinDist.pure (.activate () : NetworkChoice Unit)).map _ = _
  rw [FinDist.map_pure]
  rfl

theorem scheduler_five (execution : app.Execution)
    (length : execution.environmentRecall.length = 5) :
    scheduler execution.environmentRecall (execution.observeEnvironment app) =
      FinDist.pure (.include (selectedId execution.network)) := by
  unfold scheduler interactionScheduler
  simp only [length]
  change (network execution.environmentRecall (execution.observeEnvironment app)).map
    (NetworkChoice.command runtime) = _
  simp only [network, length]
  change (FinDist.pure (.include (selectedId execution.network) : NetworkChoice Unit)).map _ = _
  rw [FinDist.map_pure]
  rfl

theorem include_step (execution : app.Execution) (id : MessageId Unit) :
    execution.environmentStep app (.include id) = FinDist.pure (included execution id) := by
  simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
  rfl

theorem deliver_step (execution : app.Execution) (bit : Bool) :
    execution.environmentStep app (.deliver () (signalId bit)) =
      FinDist.pure (delivered execution bit) := by
  simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
  rfl

theorem round_signal (players : Unit → app.Policy) :
    app.round scheduler players contested =
      (FinDist.uniformOfFintype (α := Bool)).map (delivered contested) := by
  rw [ReactiveApplication.round, scheduler_three contested rfl, FinDist.bind_map,
    FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro bit _
  rw [ReactiveApplication.dispatch, deliver_step, FinDist.pure_bind]
  rfl

theorem round_response (players : Unit → app.Policy) (bit : Bool) :
    app.round scheduler players (delivered contested bit) =
      (players () ((beforeResponse bit).recall ()) ((beforeResponse bit).observe app ())).map
        (response bit) := by
  rw [ReactiveApplication.round, scheduler_four _ rfl, FinDist.pure_bind,
    ReactiveApplication.dispatch, activate_step, FinDist.pure_bind]
  rfl

theorem round_selection (players : Unit → app.Policy) (bit : Bool) (action : app.Action) :
    app.round scheduler players (response bit action) = FinDist.pure (selected bit action) := by
  have length : (response bit action).environmentRecall.length = 5 := by
    rw [response, app.respond_environmentRecall]
    rfl
  rw [ReactiveApplication.round, scheduler_five _ length, FinDist.pure_bind,
    ReactiveApplication.dispatch, include_step, FinDist.pure_bind]
  rfl

/-- The exact law includes delivery, the response informed by delivery, and
selection before any further decision. No strategy restrictions occur here. -/
theorem first_three_rounds (players : Unit → app.Policy) :
    app.runRounds scheduler players 3 contested =
      (FinDist.uniformOfFintype (α := Bool)).bind (fun bit =>
        (players () ((beforeResponse bit).recall ()) ((beforeResponse bit).observe app ())).map
          (selected bit)) := by
  rw [ReactiveApplication.runRounds, round_signal, FinDist.bind_map]
  apply FinDist.bind_congr
  intro bit _
  rw [ReactiveApplication.runRounds, round_response, FinDist.bind_map]
  rw [FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro action _
  rw [ReactiveApplication.runRounds, round_selection, FinDist.pure_bind]
  rfl

theorem rounds_value_sum_le (players : Unit → app.Policy) (extra : Nat) :
    (app.runRounds scheduler players (3 + extra) contested).expect
      (fun final => PendingMenus.publicUtility true (final.application.config.outputs 1)) +
    (app.runRounds scheduler players (3 + extra) contested).expect
      (fun final => PendingMenus.publicUtility false (final.application.config.outputs 1)) ≤ 3 := by
  rw [← FinDist.expect_add]
  apply FinDist.expect_le_of_forall
  intro final supported
  rw [app.runRounds_add, first_three_rounds, FinDist.bind_bind] at supported
  obtain ⟨bit, _, afterBit⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  rw [FinDist.bind_map] at afterBit
  obtain ⟨action, _, suffix⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ afterBit)
  exact selected_rounds_sum_le bit action players extra final suffix

end VegasTests.ReactiveMenus
