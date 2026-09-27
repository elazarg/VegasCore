/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRoundReachability
import Interaction.ReactiveResponseEvaluation

/-! # Exact protocol prefixes under a fixed activation schedule

One scheduler command and its optional player response account for the exact
number of protocol transitions. The law retains the complete execution.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal]

private theorem iterate_bind {A B : Type} (kernel : B → FinDist B)
    (count : Nat) (law : FinDist A) (start : A → FinDist B) :
    (fun distribution => distribution.bind kernel)^[count] (law.bind start) =
      law.bind (fun value => (fun distribution => distribution.bind kernel)^[count]
        (start value)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [Function.iterate_succ_apply', ih, FinDist.bind_bind]

theorem control_round (app : ReactiveApplication Principal)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (remaining : Nat) (execution : app.Execution)
    (actor : Option Principal)
    (scheduled : ∀ command ∈
      (scheduler execution.environmentRecall (execution.observeEnvironment app)).support,
      command.actor? app = actor) :
    (fun law => law.bind (app.controlStep initial horizon scheduler players))^[
        1 + actor.toList.length] (FinDist.pure (some ⟨remaining + 1, none, execution⟩)) =
      (app.round scheduler players execution).map
        (fun next => some ⟨remaining, none, next⟩) := by
  classical
  cases actor with
  | none =>
      simp only [Option.toList_none, List.length_nil, Nat.add_zero, Function.iterate_one,
        FinDist.pure_bind, ReactiveApplication.controlStep, ReactiveApplication.actor,
        Option.bind_some, ReactiveApplication.transition, ReactiveApplication.round,
        FinDist.map_bind]
      apply FinDist.bind_congr
      intro command supported
      rw [scheduled command supported]
      simp only [ReactiveApplication.dispatch, scheduled command supported]
      change _ = ((execution.environmentStep app command).bind FinDist.pure).map _
      rw [FinDist.bind_pure]
  | some who =>
      simp only [Option.toList_some, List.length_singleton]
      rw [show 1 + 1 = 1 + 1 from rfl, Function.iterate_add_apply,
        Function.iterate_one, FinDist.pure_bind]
      simp only [ReactiveApplication.controlStep, ReactiveApplication.actor,
        Option.bind_some, ReactiveApplication.transition, ReactiveApplication.round,
        FinDist.map_bind, FinDist.bind_bind, FinDist.bind_map]
      apply FinDist.bind_congr
      intro command supported
      rw [scheduled command supported]
      simp only [ReactiveApplication.dispatch, scheduled command supported,
        ReactiveApplication.resume, FinDist.map_bind]
      apply FinDist.bind_congr
      intro observed _
      simp only [↓reduceIte, Option.getD_some, ReactiveApplication.invoke,
        FinDist.map_eq_bind, FinDist.bind_bind, FinDist.pure_bind]


theorem scheduled_segment_control_steps (app : ReactiveApplication Principal)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (schedule : List (Option Principal))
    (scheduled : ∀ past view command, command ∈ (scheduler past view).support →
      command.actor? app = (schedule[past.length]?).join)
    (players : Principal → app.Policy)
    (before segment rest : List (Option Principal))
    (split : schedule = before ++ segment ++ rest)
    (execution : app.Execution) (position : execution.environmentRecall.length = before.length) :
    (fun law => law.bind (app.controlStep initial horizon scheduler players))^[
        segment.length + (segment.filterMap id).length]
        (FinDist.pure (some ⟨segment.length + rest.length, none, execution⟩)) =
      (app.runRounds scheduler players segment.length execution).map
        (fun next => some ⟨rest.length, none, next⟩) := by
  induction segment generalizing before execution with
  | nil => simp only [List.length_nil, List.filterMap_nil, Nat.zero_add,
      Function.iterate_zero_apply, runRounds, FinDist.map_pure]
  | cons actor segment ih =>
      let first := 1 + actor.toList.length
      let later := segment.length + (segment.filterMap id).length
      have count : (actor :: segment).length +
          ((actor :: segment).filterMap id).length = later + first := by
        cases actor <;> simp [first, later] <;> omega
      have located : schedule[before.length]? = some actor := by
        rw [split, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      have actorEq : ∀ command ∈
          (scheduler execution.environmentRecall (execution.observeEnvironment app)).support,
          command.actor? app = actor := by
        intro command supported
        rw [scheduled _ _ command supported, position, located]
        rfl
      have one := app.control_round initial horizon scheduler players
        (segment.length + rest.length) execution actor actorEq
      have start : (actor :: segment).length + rest.length =
          segment.length + rest.length + 1 := by simp only [List.length_cons]; omega
      rw [count, start, Function.iterate_add_apply, one,
        FinDist.map_eq_bind, iterate_bind]
      change _ = ((app.round scheduler players execution).bind
        (app.runRounds scheduler players segment.length)).map _
      rw [FinDist.map_bind]
      apply FinDist.bind_congr
      intro next reached
      apply ih (before ++ [actor])
      · simpa only [List.append_assoc, List.singleton_append] using split
      · obtain ⟨command, _, dispatched⟩ :=
          Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
        rw [app.dispatch_environmentRecall players command execution next dispatched]
        simp only [List.length_append, List.length_singleton, position]

/-- Initialization and any complete scheduler prefix have an exact protocol
depth. This is independent of the response policy or observation samples. -/
theorem scheduled_prefix_control_steps (app : ReactiveApplication Principal)
    (initial : FinDist app.State) (scheduler : app.Scheduler)
    (schedule : List (Option Principal))
    (scheduled : ∀ past view command, command ∈ (scheduler past view).support →
      command.actor? app = (schedule[past.length]?).join)
    (players : Principal → app.Policy) (count : Nat) (within : count ≤ schedule.length) :
    (fun law => law.bind (app.controlStep initial schedule.length scheduler players))^[
      count + ((schedule.take count).filterMap id).length + 1] (FinDist.pure none) =
      (app.roundsFrom initial scheduler players count).map
        (fun next => some ⟨schedule.length - count, none, next⟩) := by
  rw [Function.iterate_succ_apply, FinDist.pure_bind]
  change (fun law => law.bind (app.controlStep initial schedule.length scheduler players))^[
      count + ((schedule.take count).filterMap id).length]
      (initial.map (fun state => some ⟨schedule.length, none, Execution.initial app state⟩)) = _
  rw [FinDist.map_eq_bind, iterate_bind, roundsFrom, FinDist.map_bind]
  apply FinDist.bind_congr
  intro state _
  have result := app.scheduled_segment_control_steps initial schedule.length scheduler schedule
    scheduled players [] (schedule.take count) (schedule.drop count)
      (by simp only [List.nil_append, List.take_append_drop]) (Execution.initial app state) rfl
  have length : (schedule.take count).length = count := List.length_take_of_le within
  rw [length, List.length_drop, Nat.add_sub_of_le within] at result
  exact result

end Interaction.ReactiveApplication

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : FinDist app.State) (scheduler : app.Scheduler)
  (schedule : List (Option Principal))
  (scheduled : ∀ past view command, command ∈ (scheduler past view).support →
    command.actor? app = (schedule[past.length]?).join)
  (players : Principal → app.Policy)
  (covered : ∀ who, menu.Admissible initial schedule.length scheduler who (players who))

include scheduled in
/-- Legal-history coverage suffices for the exact finite-game prefix law. -/
theorem restrict_scheduled_prefix_state (count : Nat) (within : count ≤ schedule.length) :
    ((menu.information initial schedule.length scheduler).runBehavioral
      (fun who => menu.restrictPolicy initial schedule.length scheduler who
        (players who) (covered who))
      (count + ((schedule.take count).filterMap id).length + 1)).map History.state =
      (app.roundsFrom initial scheduler players count).map
        (fun next => some ⟨schedule.length - count, none, next⟩) := by
  rw [InformationModel.runBehavioral, menu.run_restrict_control_steps]
  exact app.scheduled_prefix_control_steps initial scheduler schedule scheduled players count within

include scheduled covered in
omit [Fintype Principal] in
/-- Every physically supported prefix has a legal retained history. The
uniform retained policy therefore also supports the same complete execution. -/
theorem restrict_scheduled_prefix_support [Finite Principal]
    (count : Nat) (within : count ≤ schedule.length)
    (execution : app.Execution)
    (supported : execution ∈ (app.roundsFrom initial scheduler players count).support) :
    execution ∈ (app.roundsFrom initial scheduler menu.uniformResponses count).support := by
  let _ := Fintype.ofFinite Principal
  have law := menu.restrict_scheduled_prefix_state initial scheduler schedule scheduled
    players covered count within
  have reached : some ⟨schedule.length - count, none, execution⟩ ∈
      (((menu.information initial schedule.length scheduler).runBehavioral
        (fun who => menu.restrictPolicy initial schedule.length scheduler who
          (players who) (covered who))
        (count + ((schedule.take count).filterMap id).length + 1)).map History.state).support := by
    rw [law, FinDist.support_map]
    exact ⟨execution, supported, rfl⟩
  obtain ⟨history, _, stateEq⟩ := FinDist.support_map .. ▸ reached
  have trace := menu.roundSupported_uniform initial schedule.length scheduler
    (stateEq ▸ history.trace)
  have length := app.roundsFrom_recall initial scheduler players count execution supported
  exact length ▸ trace.2

end Interaction.ReactiveApplication.ResponseMenu
