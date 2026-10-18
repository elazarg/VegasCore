/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastInitialQuiet
import Vegas.Pending.PhaseCountProjection
import Vegas.Pending.PhaseReadyResolution
import Interaction.ReactiveObservation
import Interaction.ReactiveRounds

/-! # Exact native replay of the first late callbacks without an early packet -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

/-- Erase only the builder's command transcript. Native preparation, all
candidate state, both packet pools, receipts and every player's own word remain. -/
def physicalExecution (execution : app.Execution) : app.Execution :=
  { execution with environmentRecall := [] }

theorem physicalExecution_idempotent (execution : app.Execution) :
    physicalExecution (physicalExecution execution) = physicalExecution execution := rfl

theorem physicalExecution_player_input (execution : app.Execution) (owner : Player) :
    ((physicalExecution execution).recall owner,
      (physicalExecution execution).observe app owner) =
        (execution.recall owner, execution.observe app owner) := rfl

private theorem physicalExecution_respond (execution : app.Execution) (owner : Player)
    (action : app.Action) :
    physicalExecution (execution.respond app owner action) =
      physicalExecution ((physicalExecution execution).respond app owner action) := by
  rcases action with ⟨transmission⟩
  cases transmission <;> rfl

private theorem physicalExecution_dispatch (players : Player → app.Policy)
    (command : app.Command) (execution : app.Execution) :
    (app.dispatch players command execution).map physicalExecution =
      (app.dispatch players command (physicalExecution execution)).map physicalExecution := by
  cases command with
  | activate owner =>
      simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume,
        ReactiveApplication.invoke, PMF.map_bind, PMF.bind_map, PMF.map_comp,
        Function.comp_def]
      congr 1
  | «include» identifier =>
      simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume, PMF.pure_map,
        PMF.pure_bind]
      simp only [physicalExecution, ReactiveApplication.Execution.includePending]
      split <;> rfl
  | application command =>
      simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume, PMF.bind_map,
        PMF.map_bind, PMF.pure_map, PMF.map_comp, Function.comp_def]
      congr 1
  | wait =>
      simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume, PMF.pure_map,
        PMF.pure_bind]
      rfl

/-- Finite Kleisli composition of the existing native dispatcher. This is
the physical command kernel, not a second transition or game semantics. -/
def commandComposition (players : Player → app.Policy) (commands : List app.Command) :
    app.Execution → PMF app.Execution :=
  commands.foldr (fun command next execution =>
    (app.dispatch players command execution).bind next) PMF.pure

theorem commandComposition_physical (players : Player → app.Policy)
    (commands : List app.Command) (execution : app.Execution) :
    (commandComposition players commands execution).map physicalExecution =
      (commandComposition players commands (physicalExecution execution)).map
        physicalExecution := by
  induction commands generalizing execution with
  | nil =>
      simp only [commandComposition, List.foldr_nil, PMF.pure_map,
        physicalExecution_idempotent]
  | cons command commands ih =>
      change ((app.dispatch players command execution).bind
        (commandComposition players commands)).map physicalExecution = _
      calc
        _ = (app.dispatch players command execution).bind
            (fun next => (commandComposition players commands next).map physicalExecution) :=
          PMF.map_bind ..
        _ = (app.dispatch players command execution).bind
            (fun next => (commandComposition players commands
              (physicalExecution next)).map physicalExecution) := by
          apply bind_congr_on_support
          intro next _
          exact ih next
        _ = ((app.dispatch players command execution).map physicalExecution).bind
            (fun next => (commandComposition players commands next).map physicalExecution) :=
          (PMF.bind_map (app.dispatch players command execution) physicalExecution
            (fun next => (commandComposition players commands next).map physicalExecution)).symm
        _ = ((app.dispatch players command (physicalExecution execution)).map
            physicalExecution).bind
              (fun next => (commandComposition players commands next).map physicalExecution) := by
          rw [physicalExecution_dispatch]
        _ = (app.dispatch players command (physicalExecution execution)).bind
            (fun next => (commandComposition players commands
              (physicalExecution next)).map physicalExecution) :=
          PMF.bind_map (app.dispatch players command (physicalExecution execution))
            physicalExecution (fun next =>
              (commandComposition players commands next).map physicalExecution)
        _ = (app.dispatch players command (physicalExecution execution)).bind
            (fun next => (commandComposition players commands next).map physicalExecution) := by
          apply bind_congr_on_support
          intro next _
          exact (ih next).symm
        _ = _ := (PMF.map_bind ..).symm

/-- The exact callback composition, retaining all native preparation and
player recall while discarding only invisible builder stutters. -/
def physicalCallbacks (players : Player → app.Policy) (owners : List Player)
    (execution : app.Execution) : PMF app.Execution :=
  (commandComposition players (owners.map ReactiveApplication.Command.activate)
    (physicalExecution execution)).map physicalExecution

private theorem physicalCallbacks_physical (players : Player → app.Policy)
    (owners : List Player) (execution : app.Execution) :
    physicalCallbacks players owners (physicalExecution execution) =
      physicalCallbacks players owners execution := rfl

private theorem commandComposition_wait (players : Player → app.Policy)
    (commands : List app.Command) (execution : app.Execution) :
    (commandComposition players (.wait :: commands) execution).map physicalExecution =
      (commandComposition players commands execution).map physicalExecution := by
  change ((app.dispatch players .wait execution).bind
    (commandComposition players commands)).map physicalExecution = _
  simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume, PMF.pure_map,
    PMF.pure_bind]
  rw [commandComposition_physical players commands,
    commandComposition_physical players commands execution]
  rfl

private theorem commandComposition_callbacks (players : Player → app.Policy)
    (commands : List app.Command)
    (permitted : ∀ command ∈ commands, command = .wait ∨ ∃ owner, command = .activate owner)
    (execution : app.Execution) :
    (commandComposition players commands execution).map physicalExecution =
      physicalCallbacks players (commands.filterMap fun command => command.actor? app)
        execution := by
  induction commands generalizing execution with
  | nil =>
      simp only [physicalCallbacks, commandComposition, List.filterMap_nil, List.map_nil,
        List.foldr_nil, PMF.pure_map, physicalExecution_idempotent]
  | cons command commands ih =>
      have tail : ∀ next ∈ commands, next = .wait ∨ ∃ owner, next = .activate owner := by
        intro next member
        exact permitted next (List.mem_cons_of_mem command member)
      rcases permitted command (List.mem_cons_self ..) with rfl | ⟨owner, rfl⟩
      · rw [commandComposition_wait]
        exact ih tail execution
      · change ((app.dispatch players (.activate owner) execution).bind
          (commandComposition players commands)).map physicalExecution = _
        let owners := commands.filterMap fun command => command.actor? app
        calc
          _ = (app.dispatch players (.activate owner) execution).bind
              (fun next => physicalCallbacks players owners next) := by
            rw [PMF.map_bind]
            apply bind_congr_on_support
            intro next _
            exact ih tail next
          _ = ((app.dispatch players (.activate owner) execution).map physicalExecution).bind
              (fun next => physicalCallbacks players owners next) := by
            rw [PMF.bind_map]
            rfl
          _ = ((app.dispatch players (.activate owner) (physicalExecution execution)).map
              physicalExecution).bind (fun next => physicalCallbacks players owners next) := by
            rw [physicalExecution_dispatch]
          _ = ((app.dispatch players (.activate owner) (physicalExecution execution)).bind
              (commandComposition players (owners.map ReactiveApplication.Command.activate))).map
                physicalExecution := by
            rw [PMF.bind_map, PMF.map_bind]
            apply bind_congr_on_support
            intro next _
            exact (commandComposition_physical players _ next).symm
          _ = _ := rfl

/-- These are the actual nine command slots of the original clock-two block
when there was no initial packet, including all three invisible middle slots. -/
def firstLateCommands (seed : Seeds) : List app.Command :=
  [if seed.2 (seed.1 0) then .activate (seed.1 0) else .wait,
    if seed.2 (seed.1 1) then .activate (seed.1 1) else .wait,
    if seed.2 (seed.1 2) then .activate (seed.1 2) else .wait,
    .wait, .wait, .wait,
    if seed.2 (seed.1 0) then .wait else .activate (seed.1 0),
    if seed.2 (seed.1 1) then .wait else .activate (seed.1 1),
    if seed.2 (seed.1 2) then .wait else .activate (seed.1 2)]

theorem firstLateCommands_callbacks (seed : Seeds) :
    (firstLateCommands seed).filterMap (fun command => command.actor? app) =
      nativePartitionedOrder seed := by
  change _ = ([seed.1 0, seed.1 1, seed.1 2].filter seed.2 ++
    [seed.1 0, seed.1 1, seed.1 2].filter fun owner => !(seed.2 owner))
  cases first : seed.2 (seed.1 0) <;> cases second : seed.2 (seed.1 1) <;>
    cases third : seed.2 (seed.1 2) <;>
      simp [firstLateCommands, first, second, third, ReactiveApplication.Command.actor?]

/-- The frozen initial snapshot is empty even if a later callback has already
submitted a packet. The middle block therefore never treats late traffic as early. -/
def EmptyEarlySnapshot (execution : app.Execution) : Prop :=
  ∀ entry ∈ execution.environmentRecall[3]?, entry.beforeView.network.inputs = []

private theorem earlyCommand_wait (execution : app.Execution)
    (empty : EmptyEarlySnapshot execution) (owner : Player) :
    earlyCommand owner execution.environmentRecall (execution.observeEnvironment app) = .wait := by
  unfold earlyCommand
  cases found : execution.environmentRecall[3]? with
  | none => rfl
  | some entry =>
      have inputs := empty entry (by rw [found]; exact Option.mem_def.mpr rfl)
      change (match entry.beforeView.network.inputs.find? (fun message :
        Message Player (CommitAttemptPacket graph) =>
          message.sender = owner ∧ message.payload.attempt = originalAttempt) with
        | none => (.wait : app.Command)
        | some message => pendingCommand message.id (execution.observeEnvironment app)) =
          (.wait : app.Command)
      rw [inputs]
      rfl

private theorem respond_publicView (execution : app.Execution) (owner : Player)
    (action : app.Action) :
    (execution.respond app owner action).application.publicView =
      execution.application.publicView := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material => exact PhaseCount.submit_publicView execution.application owner material

private def NoHelperBlock (execution : app.Execution) : Prop :=
  execution.application.publicView = quietStart.application.publicView ∧
    EmptyEarlySnapshot execution ∧ 5 ≤ execution.environmentRecall.length

private theorem noHelperBlock_command (seed : Seeds) (count : Nat) (inside : count < 9)
    (execution : app.Execution) (valid : NoHelperBlock execution)
    (position : execution.environmentRecall.length = 5 + count) :
    family seed execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure (((firstLateCommands seed)[count]?).getD .wait) := by
  have original : execution.application.attempt = originalAttempt := by
    have same := congrArg PhasePublicView.attempt valid.1
    exact same.trans quietStart_attempt
  have readyAll (owner : Player) :
      ready owner (bindingEvent owner) (execution.observeEnvironment app) = true := by
    simp only [ready, decide_eq_true_eq]
    change PhaseRuntimeState.requests execution.application.publicView owner
      ⟨execution.application.attempt, bindingEvent owner⟩
    rw [original, valid.1]
    exact quietStart_public_requests owner
  have middle (owner : Player) := earlyCommand_wait execution valid.2.1 owner
  rw [family, choose_original seed _ _ original, position]
  interval_cases count <;>
    simp only [originalCommand, firstLateCommands, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, pollCommand, activateReady, readyAll,
      ite_true, middle]
  all_goals split_ifs <;> simp_all

private theorem firstLateCommands_permitted (seed : Seeds) :
    ∀ command ∈ firstLateCommands seed,
      command = .wait ∨ ∃ owner, command = .activate owner := by
  intro command member
  simp only [firstLateCommands, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with member | member | member | member | member | member | member | member |
    member <;> subst command
  all_goals first
  | exact Or.inl rfl
  | (split_ifs <;> first | exact Or.inl rfl | exact Or.inr ⟨_, rfl⟩)

private theorem noHelperBlock_dispatch (players : Player → app.Policy)
    (command : app.Command)
    (permitted : command = .wait ∨ ∃ owner, command = .activate owner)
    (execution next : app.Execution) (valid : NoHelperBlock execution)
    (reached : next ∈ (app.dispatch players command execution).support) :
    NoHelperBlock next := by
  have recalled := app.dispatch_environmentRecall players command execution next reached
  have atLeast : 5 ≤ execution.environmentRecall.length := valid.2.2
  have publicView : next.application.publicView = execution.application.publicView := by
    rcases permitted with rfl | ⟨owner, rfl⟩
    · simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume, PMF.pure_map,
        PMF.pure_bind, PMF.mem_support_pure_iff] at reached
      subst next
      rfl
    · rw [ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind] at reached
      change next ∈ ((players owner ((completeActivation execution owner).recall owner)
        ((completeActivation execution owner).observe app owner)).map
          ((completeActivation execution owner).respond app owner)).support at reached
      obtain ⟨action, _supported, same⟩ := PMF.support_map .. ▸ reached
      subst next
      exact respond_publicView (completeActivation execution owner) owner action
  refine ⟨publicView.trans valid.1, ?_, ?_⟩
  · intro entry present
    rw [recalled, List.getElem?_append_left (by omega : 3 < execution.environmentRecall.length)]
      at present
    exact valid.2.1 entry present
  · rw [recalled, List.length_append, List.length_singleton]
    omega

private theorem noHelperBlock_run (seed : Seeds) (players : Player → app.Policy)
    (execution : app.Execution) (valid : NoHelperBlock execution)
    (position : execution.environmentRecall.length = 5) (count : Nat) (within : count ≤ 9)
    (next : app.Execution)
    (reached : next ∈ (app.runRounds (family seed) players count execution).support) :
    NoHelperBlock next := by
  induction count generalizing next with
  | zero =>
      have same := (PMF.mem_support_pure_iff _ _).mp reached
      subst next
      exact valid
  | succ count ih =>
      rw [app.runRounds_add (family seed) players count 1, PMF.support_bind] at reached
      obtain ⟨before, prefixReached, last⟩ := Set.mem_iUnion₂.mp reached
      have beforeValid := ih (by omega) before prefixReached
      have length := app.runRounds_environmentRecall_length (family seed) players count execution
        before prefixReached
      rw [position] at length
      have selected := noHelperBlock_command seed count (by omega) before beforeValid length
      have round : next ∈ (app.round (family seed) players before).support := by
        simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using last
      rw [ReactiveApplication.round, selected, PMF.pure_bind] at round
      have inside : count < (firstLateCommands seed).length := by
        simp only [firstLateCommands, List.length_cons, List.length_nil]
        omega
      have member : ((firstLateCommands seed)[count]?).getD .wait ∈ firstLateCommands seed := by
        rw [List.getElem?_eq_getElem inside, Option.getD_some]
        exact List.getElem_mem inside
      exact noHelperBlock_dispatch players _ (firstLateCommands_permitted seed _ member) before
        next beforeValid round

private theorem runRounds_commandComposition (seed : Seeds) (players : Player → app.Policy)
    (commands : List app.Command) (execution : app.Execution)
    (selected : ∀ count < commands.length, ∀ next ∈
      (app.runRounds (family seed) players count execution).support,
      family seed next.environmentRecall (next.observeEnvironment app) =
        PMF.pure ((commands[count]?).getD .wait)) :
    app.runRounds (family seed) players commands.length execution =
      commandComposition players commands execution := by
  induction commands generalizing execution with
  | nil => rfl
  | cons command commands ih =>
      have first := selected 0 (by simp) execution (PMF.mem_support_pure_iff _ _ |>.mpr rfl)
      simp only [List.getElem?_cons_zero, Option.getD_some] at first
      have round : app.round (family seed) players execution =
          app.dispatch players command execution := by
        rw [ReactiveApplication.round, first, PMF.pure_bind]
      change (app.round (family seed) players execution).bind
          (app.runRounds (family seed) players commands.length) =
        (app.dispatch players command execution).bind (commandComposition players commands)
      rw [round]
      apply bind_congr_on_support
      intro before reached
      apply ih before
      intro count inside next later
      have joined : next ∈ (app.runRounds (family seed) players (count + 1) execution).support := by
        rw [show count + 1 = 1 + count by omega, app.runRounds_add, PMF.support_bind]
        apply Set.mem_iUnion₂.mpr
        refine ⟨before, ?_, later⟩
        simpa only [ReactiveApplication.runRounds, PMF.bind_pure, round] using reached
      have nextInside : count + 1 < (command :: commands).length := by
        simp only [List.length_cons]
        omega
      have actual := selected (count + 1) nextInside next joined
      simpa only [List.getElem?_cons_succ] using actual

/-- The full native physical kernel of the original first-late block is a
function only of the stable partition order. Every raw preparation and exact
pending packet word is retained; no service-posterior premise is supplied. -/
theorem nohelper_first_late_physical_kernel (seed : Seeds) (players : Player → app.Policy) :
    (app.runRounds (family seed) players 9 quietStart).map physicalExecution =
      physicalCallbacks players (nativePartitionedOrder seed) quietStart := by
  have empty : EmptyEarlySnapshot quietStart := by
    obtain ⟨entry, found, inputs⟩ := quietStart_early_snapshot
    intro actual present
    rw [found] at present
    have same := Option.mem_def.mp present
    cases same
    exact inputs
  have valid : NoHelperBlock quietStart := ⟨rfl, empty, by rw [quietStart_length]⟩
  have actual := runRounds_commandComposition seed players (firstLateCommands seed) quietStart
    (by
      intro count inside next reached
      have within : count < 9 := by simpa only [firstLateCommands, List.length_cons,
        List.length_nil] using inside
      have nextValid := noHelperBlock_run seed players quietStart valid quietStart_length count
        (by omega) next reached
      have length := app.runRounds_environmentRecall_length (family seed) players count quietStart
        next reached
      rw [quietStart_length] at length
      exact noHelperBlock_command seed count within next nextValid length)
  change app.runRounds (family seed) players 9 quietStart = _ at actual
  rw [actual, commandComposition_callbacks players _ (firstLateCommands_permitted seed),
    firstLateCommands_callbacks]

/-- The complete first-late input is retained by the last own response record
after this block: its before-view and the exact preceding own word. -/
def firstLateInput (owner : Player) (execution : app.Execution) : Option
    (List app.PlayerEntry × app.PlayerView) :=
  (execution.recall owner).getLast?.map fun entry =>
    ((execution.recall owner).dropLast, entry.beforeView)

/-- Consequently the actual initialized first-late input law, with all private
state and recall kept, uses only the partition order and no hidden cut count. -/
theorem nohelper_first_late_input_kernel (seed : Seeds) (players : Player → app.Policy)
    (owner : Player) :
    (app.runRounds (family seed) players 9 quietStart).map (firstLateInput owner) =
      (physicalCallbacks players (nativePartitionedOrder seed) quietStart).map
        (firstLateInput owner) := by
  have actual := congrArg (fun law => law.map (firstLateInput owner))
    (nohelper_first_late_physical_kernel seed players)
  have same : firstLateInput owner ∘ physicalExecution = firstLateInput owner := rfl
  simpa only [PMF.map_comp, same] using actual

/-- The same law starts from the actual original initialized experiment whose
three initial responses are literal WAIT, rather than an independent entry prior. -/
theorem initialized_quiet_first_late_input_kernel (seed : Seeds)
    (players : Player → app.Policy)
    (waited : ∀ owner, players owner ((initialCallback owner).recall owner)
      ((initialCallback owner).observe app owner) = PMF.pure ⟨none⟩)
    (owner : Player) :
    (app.runRounds (family seed) players 14 initialExecution).map (firstLateInput owner) =
      (physicalCallbacks players (nativePartitionedOrder seed) quietStart).map
        (firstLateInput owner) := by
  rw [show 14 = 5 + 9 by decide, app.runRounds_add, quietStart_law seed players waited,
    PMF.pure_bind]
  exact nohelper_first_late_input_kernel seed players owner

end Vegas.Examples.CommitSeedBroadcast
