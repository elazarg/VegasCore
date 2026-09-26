/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealService
import GameTheory.Analysis.Protocol.CounterfactualDecomposition

/-! # Decision positions in the revelation service calendar

Each source event contributes one owner activation and one watcher activation.
The counts below concern the existing service plan and raw protocol traces;
they do not add a clock or a scheduler cursor to player observations.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open EventGraphRuntime Interaction GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The fixed actor of a revelation-service instruction. Report wire turns
only include or wait, and therefore do not activate another player. -/
def instructionActor {graph : Vegas.EventGraph Player L} : ServiceInstruction graph → Option Player
  | .player who => some who
  | _ => none

private def instructionGrant {graph : Vegas.EventGraph Player L} :
    ServiceInstruction graph → Option graph.EventId
  | .grant event => some event
  | _ => none

/-- The actual service instructions before a given source rank. -/
def planPrefix (setup : Setup (Player := Player) (L := L)) (watcher : Player) (rank : Nat) :
    List (ServiceInstruction (graph setup)) :=
  ((List.finRange (graph setup).order.eventCount).take rank).flatMap (block setup watcher)

/-- Scheduler instructions preceding source rank `rank`. -/
def blockOffset (rank : Nat) : Nat := (Finset.range rank).sum fun index => index + 7

theorem blockOffset_succ (rank : Nat) : blockOffset (rank + 1) = blockOffset rank + rank + 7 := by
  simp only [blockOffset, Finset.sum_range_succ]
  omega

theorem planPrefix_succ (setup : Setup (Player := Player) (L := L)) (watcher : Player)
    (event : (graph setup).EventId) :
    planPrefix setup watcher (event.val + 1) =
      planPrefix setup watcher event.val ++ block setup watcher event := by
  simp only [planPrefix, List.take_add_one, List.flatMap_append]
  have selected : (List.finRange (graph setup).order.eventCount)[event.val]? = some event := by
    rw [List.getElem?_eq_getElem (by simpa only [List.length_finRange] using event.isLt),
      List.getElem_finRange]
    exact congrArg some (Fin.ext rfl)
  simp only [selected, Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem planPrefix_length (setup : Setup (Player := Player) (L := L)) (watcher : Player)
    (reveals : setup.program.RevealOnly) (rank : Nat)
    (within : rank ≤ (graph setup).order.eventCount) :
    (planPrefix setup watcher rank).length = blockOffset rank := by
  induction rank with
  | zero => rfl
  | succ rank ih =>
      have inside : rank < (graph setup).order.eventCount := by omega
      rw [planPrefix_succ setup watcher ⟨rank, inside⟩, List.length_append,
        ih (by omega), block_length setup watcher reveals, blockOffset_succ]
      change blockOffset rank + (rank + 7) = blockOffset rank + rank + 7
      omega

theorem block_actors (setup : Setup (Player := Player) (L := L)) (watcher owner : Player)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner) :
    (block setup watcher event).filterMap instructionActor = [owner, watcher] := by
  rw [block_of_owner setup watcher owner event owned]
  simp [instructionActor]

theorem planPrefix_actors_length (setup : Setup (Player := Player) (L := L)) (watcher : Player)
    (reveals : setup.program.RevealOnly) (rank : Nat)
    (within : rank ≤ (graph setup).order.eventCount) :
    ((planPrefix setup watcher rank).filterMap instructionActor).length = 2 * rank := by
  induction rank with
  | zero => rfl
  | succ rank ih =>
      have inside : rank < (graph setup).order.eventCount := by omega
      obtain ⟨owner, owned⟩ := source_owner setup reveals ⟨rank, inside⟩
      rw [planPrefix_succ setup watcher ⟨rank, inside⟩, List.filterMap_append, List.length_append,
        block_actors setup watcher owner ⟨rank, inside⟩ owned, ih (by omega)]
      simp only [List.length_cons, List.length_nil]
      omega

/-- The concrete calendar splits at each source event, with the earlier
instructions given by `planPrefix`. -/
theorem plan_split_at (setup : Setup (Player := Player) (L := L)) (watcher : Player)
    (event : (graph setup).EventId) :
    ∃ suffix, plan setup watcher =
      planPrefix setup watcher event.val ++ block setup watcher event ++ suffix := by
  let events := List.finRange (graph setup).order.eventCount
  refine ⟨(events.drop (event.val + 1)).flatMap (block setup watcher), ?_⟩
  have split := congrArg (List.flatMap (block setup watcher))
    (events.take_append_drop (event.val + 1))
  rw [List.flatMap_append] at split
  change planPrefix setup watcher (event.val + 1) ++ _ = plan setup watcher at split
  rw [planPrefix_succ] at split
  exact split.symm

/-- The owner is activated after the grant, before any watcher step. -/
theorem plan_take_owner (setup : Setup (Player := Player) (L := L)) (watcher owner : Player)
    (reveals : setup.program.RevealOnly) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner) :
    (plan setup watcher).take (blockOffset event.val + 2) =
      planPrefix setup watcher event.val ++ [.grant event, .player owner] := by
  obtain ⟨suffix, split⟩ := plan_split_at setup watcher event
  have length := planPrefix_length setup watcher reveals event.val event.isLt.le
  rw [split, List.append_assoc, List.take_append,
    List.take_of_length_le (by omega), length, Nat.add_sub_cancel_left]
  rw [block_of_owner setup watcher owner event owned]
  rfl

/-- The watcher is activated after the owner's reserved inclusion. -/
theorem plan_take_watcher (setup : Setup (Player := Player) (L := L)) (watcher owner : Player)
    (reveals : setup.program.RevealOnly) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner) :
    (plan setup watcher).take (blockOffset event.val + 4) =
      planPrefix setup watcher event.val ++
        [.grant event, .player owner, .includeLatest event owner, .player watcher] := by
  obtain ⟨suffix, split⟩ := plan_split_at setup watcher event
  have length := planPrefix_length setup watcher reveals event.val event.isLt.le
  rw [split, List.append_assoc, List.take_append,
    List.take_of_length_le (by omega), length, Nat.add_sub_cancel_left]
  rw [block_of_owner setup watcher owner event owned]
  rfl

private theorem block_actor_position (setup : Setup (Player := Player) (L := L))
    (watcher owner who : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner) (index : Nat)
    (active : ((block setup watcher event)[index]?).bind instructionActor = some who) :
    (index = 1 ∧ who = owner) ∨ (index = 3 ∧ who = watcher) := by
  rw [block_of_owner setup watcher owner event owned] at active
  rcases index with _ | _ | _ | _ | _ | index
  · cases active
  · exact Or.inl ⟨rfl, (Option.some.inj active).symm⟩
  · cases active
  · exact Or.inr ⟨rfl, (Option.some.inj active).symm⟩
  · cases active
  · change (((List.replicate (event.val + 1) ServiceInstruction.tick ++
        [.expire event])[index]?).bind instructionActor) = some who at active
    obtain ⟨instruction, found, actor⟩ := Option.bind_eq_some_iff.mp active
    have member := List.mem_of_getElem? found
    rcases List.mem_append.mp member with tick | expiry
    · have same := (List.mem_replicate.mp tick).2
      subst instruction
      cases actor
    · have same := List.mem_singleton.mp expiry
      subst instruction
      cases actor

private theorem offset_interval (count index : Nat) (inside : index < blockOffset count) :
    ∃ rank, rank < count ∧ blockOffset rank ≤ index ∧ index < blockOffset (rank + 1) := by
  induction count with
  | zero => simp [blockOffset] at inside
  | succ count ih =>
      by_cases earlier : index < blockOffset count
      · obtain ⟨rank, before, lower, upper⟩ := ih earlier
        exact ⟨rank, by omega, lower, upper⟩
      · exact ⟨count, by omega, by omega, inside⟩

/-- The actual plan can activate only the current owner or watcher, at the
two fixed positions inside that source block. -/
theorem plan_activation_position (setup : Setup (Player := Player) (L := L))
    (watcher who : Player) (reveals : setup.program.RevealOnly) (index : Nat)
    (active : ((plan setup watcher)[index]?).bind instructionActor = some who) :
    ∃ event : (graph setup).EventId,
      (index = blockOffset event.val + 1 ∧ (graph setup).actor? event = some who) ∨
      (index = blockOffset event.val + 3 ∧ who = watcher) := by
  obtain ⟨instruction, found, actor⟩ := Option.bind_eq_some_iff.mp active
  have inPlan := (List.getElem?_eq_some_iff.mp found).1
  have fullPrefix : planPrefix setup watcher (graph setup).order.eventCount =
      plan setup watcher := by
    unfold planPrefix plan
    rw [List.take_of_length_le (by simp only [List.length_finRange]; exact le_rfl)]
  have length : (plan setup watcher).length = blockOffset (graph setup).order.eventCount := by
    rw [← fullPrefix]
    exact planPrefix_length setup watcher reveals _ le_rfl
  obtain ⟨rank, inRange, lower, upper⟩ := offset_interval _ index (length ▸ inPlan)
  let event : (graph setup).EventId := ⟨rank, inRange⟩
  obtain ⟨owner, owned⟩ := source_owner setup reveals event
  obtain ⟨suffix, split⟩ := plan_split_at setup watcher event
  change plan setup watcher = planPrefix setup watcher rank ++ block setup watcher event ++
    suffix at split
  have prefixLength := planPrefix_length setup watcher reveals rank inRange.le
  have blockLength := block_length setup watcher reveals event
  have blockBound : index - blockOffset rank < (block setup watcher event).length := by
    rw [blockLength]
    change index - blockOffset rank < rank + 7
    rw [blockOffset_succ] at upper
    omega
  have selected : (block setup watcher event)[index - blockOffset rank]? = some instruction := by
    rw [split, List.append_assoc, List.getElem?_append_right (by omega), prefixLength,
      List.getElem?_append_left blockBound] at found
    exact found
  have located := block_actor_position setup watcher owner who event owned
    (index - blockOffset rank) (by rw [selected]; exact actor)
  refine ⟨event, ?_⟩
  rcases located with ⟨position, same⟩ | ⟨position, same⟩
  · refine Or.inl ⟨?_, same ▸ owned⟩
    change index = blockOffset rank + 1
    omega
  · refine Or.inr ⟨?_, same⟩
    change index = blockOffset rank + 3
    omega

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- Number of actual player activations among the first `count` service steps. -/
def activationCount (watcher : Player) (count : Nat) : Nat :=
  (((plan setup watcher).take count).filterMap instructionActor).length

private def calendarGrant (watcher : Player) (count : Nat) : Option (graph setup).EventId :=
  (((plan setup watcher).take count).filterMap instructionGrant).getLast?

private def commandGrant : (application setup leaks).Command → Option (graph setup).EventId
  | .application (.grant event) => some event
  | _ => none

private theorem calendarGrant_owner (watcher owner : Player) (reveals : setup.program.RevealOnly)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner) :
    calendarGrant setup watcher (blockOffset event.val + 2) = some event := by
  rw [calendarGrant, plan_take_owner setup watcher owner reveals event owned]
  simp [instructionGrant]

private theorem calendarGrant_watcher (watcher owner : Player)
    (reveals : setup.program.RevealOnly) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner) :
    calendarGrant setup watcher (blockOffset event.val + 4) = some event := by
  rw [calendarGrant, plan_take_watcher setup watcher owner reveals event owned]
  simp [instructionGrant]

theorem owner_activation_count (watcher owner : Player) (reveals : setup.program.RevealOnly)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner) :
    activationCount setup watcher (blockOffset event.val + 2) = 2 * event.val + 1 := by
  rw [activationCount, plan_take_owner setup watcher owner reveals event owned,
    List.filterMap_append, List.length_append,
    planPrefix_actors_length setup watcher reveals event.val event.isLt.le]
  rfl

theorem watcher_activation_count (watcher owner : Player) (reveals : setup.program.RevealOnly)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner) :
    activationCount setup watcher (blockOffset event.val + 4) = 2 * event.val + 2 := by
  rw [activationCount, plan_take_watcher setup watcher owner reveals event owned,
    List.filterMap_append, List.length_append,
    planPrefix_actors_length setup watcher reveals event.val event.isLt.le]
  rfl

theorem instruction_actor (watcher : Player)
    (history : List (application setup leaks).EnvironmentEntry)
    (view : (application setup leaks).EnvironmentView)
    (instruction : ServiceInstruction (graph setup)) (command : (application setup leaks).Command)
    (supported : command ∈ ((runtime setup).interactionInstruction leaks
      ((runtime setup).reportNetwork leaks watcher) history view instruction).support) :
    command.actor? (application setup leaks) = instructionActor instruction := by
  cases instruction with
  | player who | grant event | sample event | tick | expire event =>
      simp only [EventGraphRuntime.interactionInstruction, FinDist.mem_support_pure] at supported
      subst command
      rfl
  | includeLatest event owner =>
      simp only [EventGraphRuntime.interactionInstruction, FinDist.mem_support_pure] at supported
      subst command
      unfold reactiveLatest
      split <;> rfl
  | wire =>
      rw [(runtime setup).reportNetwork_instruction leaks watcher history view,
        FinDist.mem_support_pure] at supported
      subst command
      unfold ReactiveApplication.includeReported
      split
      · rfl
      · split
        · simp only [ReactiveApplication.atMostOnceCommand]
          split <;> rfl
        · rfl

private theorem instruction_grant (watcher : Player)
    (history : List (application setup leaks).EnvironmentEntry)
    (view : (application setup leaks).EnvironmentView)
    (instruction : ServiceInstruction (graph setup)) (command : (application setup leaks).Command)
    (supported : command ∈ ((runtime setup).interactionInstruction leaks
      ((runtime setup).reportNetwork leaks watcher) history view instruction).support) :
    commandGrant setup leaks command = instructionGrant instruction := by
  cases instruction with
  | player who | grant event | sample event | tick | expire event =>
      simp only [EventGraphRuntime.interactionInstruction, FinDist.mem_support_pure] at supported
      subst command
      rfl
  | includeLatest event owner =>
      simp only [EventGraphRuntime.interactionInstruction, FinDist.mem_support_pure] at supported
      subst command
      unfold reactiveLatest
      split <;> rfl
  | wire =>
      rw [(runtime setup).reportNetwork_instruction leaks watcher history view,
        FinDist.mem_support_pure] at supported
      subst command
      unfold ReactiveApplication.includeReported
      split
      · rfl
      · split
        · simp only [ReactiveApplication.atMostOnceCommand]
          split <;> rfl
        · rfl

private theorem scheduled_grant (watcher : Player)
    (history : List (application setup leaks).EnvironmentEntry)
    (view : (application setup leaks).EnvironmentView) (command : (application setup leaks).Command)
    (supported : command ∈ (scheduler setup leaks watcher history view).support) :
    calendarGrant setup watcher (history.length + 1) =
      (commandGrant setup leaks command).or (calendarGrant setup watcher history.length) := by
  unfold scheduler at supported
  cases selected : (plan setup watcher)[history.length]? with
  | none =>
      rw [selected, FinDist.mem_support_pure] at supported
      subst command
      simp only [calendarGrant, List.take_add_one, selected, Option.toList_none,
        List.append_nil, commandGrant, Option.none_or]
  | some instruction =>
      rw [selected] at supported
      rw [instruction_grant setup leaks watcher history view instruction command supported]
      simp only [calendarGrant, List.take_add_one, selected, Option.toList_some,
        List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
      cases instructionGrant instruction <;> simp

private theorem respond_grant (execution : (application setup leaks).Execution) (who : Player)
    (response : (application setup leaks).Action) :
    (execution.respond (application setup leaks) who response).application.serviceGrant =
      execution.application.serviceGrant := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | replay id => rfl
      | submit submission =>
          have visible := submission.call.register_facts who execution.application |>.2.2
          change (submitStep (submission.call.register execution.application who) who
            submission.call.packet).serviceGrant = execution.application.serviceGrant
          rw [submitStep_serviceGrant]
          exact congrArg PublicView.serviceGrant visible

private theorem environment_grant (before after : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (reached : after ∈ (before.environmentStep (application setup leaks) command).support) :
    after.application.serviceGrant =
      (commandGrant setup leaks command).or before.application.serviceGrant := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      rfl
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨sample, _, rfl⟩ := FinDist.support_map .. ▸ supported
      rfl
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      change (before.includePending (application setup leaks) id).application.serviceGrant = _
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : before.network.lookup id with
      | none => rfl
      | some message =>
          change (((runtime setup).handle before.application
            ⟨message.id, message.payload.call⟩).getD before.application).serviceGrant = _
          cases accepted : (runtime setup).handle before.application
              ⟨message.id, message.payload.call⟩ with
          | none => rfl
          | some next => exact (runtime setup).handle_serviceGrant _ _ _ accepted
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := FinDist.support_map .. ▸ supported
      have preserved := (runtime setup).environmentStep_serviceGrant
        before.application state command changed
      cases command <;> exact preserved

private def GrantCalendar (watcher : Player) : (application setup leaks).ProtocolState → Prop
  | none => True
  | some control => control.execution.application.serviceGrant =
      calendarGrant setup watcher control.execution.environmentRecall.length

private theorem trace_grant_calendar (watcher : Player) :
    ∀ {state} (_trace : ((application setup leaks).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).Trace state),
      GrantCalendar setup leaks watcher state
  | _, .start => trivial
  | _, @Trace.extend _ _ source target before joint legal realized => by
      have inherited := trace_grant_calendar watcher before
      have reached : target ∈ ((application setup leaks).transition (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher) source joint).support := realized
      cases source with
      | none =>
          obtain ⟨initial, supported, rfl⟩ := FinDist.support_map .. ▸ reached
          obtain ⟨initial, _, rfl⟩ := FinDist.support_map .. ▸ supported
          rfl
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases FinDist.mem_support_pure.mp reached
              change
                (execution.respond (application setup leaks) who _).application.serviceGrant = _
              rw [respond_grant, (application setup leaks).respond_environmentRecall]
              exact inherited
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := FinDist.support_map .. ▸ moved
                  have recall : next.environmentRecall = execution.environmentRecall ++
                      [⟨execution.observeEnvironment (application setup leaks), command⟩] := by
                    obtain ⟨updated, _, equal⟩ := FinDist.support_map .. ▸ supported
                    cases equal
                    rfl
                  change next.application.serviceGrant = _
                  rw [recall, List.length_append, List.length_singleton,
                    scheduled_grant setup leaks watcher _ _ command selected,
                    environment_grant setup leaks execution next command supported]
                  exact congrArg ((commandGrant setup leaks command).or) inherited

private theorem scheduler_activation_position (watcher who : Player)
    (reveals : setup.program.RevealOnly)
    (history : List (application setup leaks).EnvironmentEntry)
    (view : (application setup leaks).EnvironmentView) (command : (application setup leaks).Command)
    (supported : command ∈ (scheduler setup leaks watcher history view).support)
    (active : command.actor? (application setup leaks) = some who) :
    ∃ event : (graph setup).EventId,
      (history.length = blockOffset event.val + 1 ∧ (graph setup).actor? event = some who) ∨
      (history.length = blockOffset event.val + 3 ∧ who = watcher) := by
  unfold scheduler at supported
  cases selected : (plan setup watcher)[history.length]? with
  | none =>
      rw [selected, FinDist.mem_support_pure] at supported
      subst command
      cases active
  | some instruction =>
      rw [selected] at supported
      apply plan_activation_position setup watcher who reveals history.length
      rw [selected]
      exact (instruction_actor setup leaks watcher history view instruction command supported).symm
        |>.trans active

private def ActiveCalendar (watcher : Player) : (application setup leaks).ProtocolState → Prop
  | none => True
  | some control => ∀ who, control.actor = some who →
      ∃ event : (graph setup).EventId, control.execution.application.serviceGrant = some event ∧
        ((control.execution.environmentRecall.length = blockOffset event.val + 2 ∧
            (graph setup).actor? event = some who) ∨
          (control.execution.environmentRecall.length = blockOffset event.val + 4 ∧ who = watcher))

private theorem trace_active_calendar (watcher : Player) (reveals : setup.program.RevealOnly) :
    ∀ {state} (_trace : ((application setup leaks).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).Trace state),
      ActiveCalendar setup leaks watcher state
  | _, .start => trivial
  | _, @Trace.extend _ _ source target before joint legal realized => by
      have inherited := trace_grant_calendar setup leaks watcher before
      have reached : target ∈ ((application setup leaks).transition (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher) source joint).support := realized
      cases source with
      | none =>
          obtain ⟨initial, _, rfl⟩ := FinDist.support_map .. ▸ reached
          intro who active
          cases active
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases FinDist.mem_support_pure.mp reached
              intro who active
              cases active
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := FinDist.support_map .. ▸ moved
                  have recall : next.environmentRecall = execution.environmentRecall ++
                      [⟨execution.observeEnvironment (application setup leaks), command⟩] := by
                    obtain ⟨updated, _, equal⟩ := FinDist.support_map .. ▸ supported
                    cases equal
                    rfl
                  have granted : next.application.serviceGrant = calendarGrant setup watcher
                      (execution.environmentRecall.length + 1) := by
                    rw [environment_grant setup leaks execution next command supported,
                      scheduled_grant setup leaks watcher _ _ command selected]
                    exact congrArg ((commandGrant setup leaks command).or) inherited
                  intro who active
                  obtain ⟨event, located⟩ := scheduler_activation_position setup leaks watcher who
                    reveals execution.environmentRecall
                    (execution.observeEnvironment (application setup leaks)) command selected active
                  refine ⟨event, ?_, ?_⟩
                  · rcases located with ⟨position, owned⟩ | ⟨position, same⟩
                    · rw [granted, position]
                      exact calendarGrant_owner setup watcher who reveals event owned
                    · obtain ⟨owner, owned⟩ := source_owner setup reveals event
                      rw [granted, position]
                      exact calendarGrant_watcher setup watcher owner reveals event owned
                  · change (next.environmentRecall.length = _ ∧ _) ∨
                      (next.environmentRecall.length = _ ∧ _)
                    rw [recall, List.length_append, List.length_singleton]
                    rcases located with ⟨position, owned⟩ | ⟨position, same⟩
                    · exact Or.inl ⟨by omega, owned⟩
                    · exact Or.inr ⟨by omega, same⟩

/-- Every raw decision occurs at one of the two declared positions of its
visible grant. Repeated source owners are permitted. -/
theorem raw_decision_calendar (watcher who : Player) (reveals : setup.program.RevealOnly)
    (control : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).Trace (some control))
    (active : control.actor = some who) :
    ∃ event : (graph setup).EventId, control.execution.application.serviceGrant = some event ∧
      ((control.execution.environmentRecall.length = blockOffset event.val + 2 ∧
          (graph setup).actor? event = some who) ∨
        (control.execution.environmentRecall.length = blockOffset event.val + 4 ∧ who = watcher)) :=
  trace_active_calendar setup leaks watcher reveals trace who active

theorem scheduled_activation_count (watcher : Player)
    (history : List (application setup leaks).EnvironmentEntry)
    (view : (application setup leaks).EnvironmentView) (command : (application setup leaks).Command)
    (supported : command ∈ (scheduler setup leaks watcher history view).support) :
    activationCount setup watcher (history.length + 1) =
      activationCount setup watcher history.length +
        (command.actor? (application setup leaks)).toList.length := by
  unfold scheduler at supported
  cases selected : (plan setup watcher)[history.length]? with
  | none =>
      rw [selected, FinDist.mem_support_pure] at supported
      subst command
      simp only [activationCount, List.take_add_one, selected, Option.toList_none,
        List.append_nil, ReactiveApplication.Command.actor?, List.length_nil, Nat.add_zero]
  | some instruction =>
      rw [selected] at supported
      have actor := instruction_actor setup leaks watcher history view instruction command supported
      simp only [activationCount, List.take_add_one, selected, Option.toList_some,
        List.filterMap_append, List.length_append, List.filterMap_cons, List.filterMap_nil]
      rw [actor]
      cases instructionActor instruction <;> rfl

private def CountedDepth (watcher : Player) (state : (application setup leaks).ProtocolState)
    (depth : Nat) : Prop :=
  match state with
  | none => depth = 0
  | some control => depth + control.actor.toList.length =
      1 + control.execution.environmentRecall.length +
        activationCount setup watcher control.execution.environmentRecall.length

private theorem trace_counted_depth (watcher : Player) :
    ∀ {state} (trace : ((application setup leaks).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).Trace state),
      CountedDepth setup leaks watcher state trace.length
  | _, .start => rfl
  | _, @Trace.extend _ _ source target before joint legal realized => by
      have inherited := trace_counted_depth watcher before
      have reached : target ∈ ((application setup leaks).transition (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher) source joint).support := realized
      cases source with
      | none =>
          obtain ⟨initial, _, rfl⟩ := FinDist.support_map .. ▸ reached
          have counted : before.length = 0 := inherited
          simpa only [CountedDepth, Trace.length, ReactiveApplication.Execution.initial,
            List.length_nil, Option.toList_none, Nat.add_zero, activationCount,
            List.take_zero, List.filterMap_nil] using congrArg (· + 1) counted
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases FinDist.mem_support_pure.mp reached
              simpa only [CountedDepth, Trace.length,
                (application setup leaks).respond_environmentRecall, Option.toList_some,
                Option.toList_none, List.length_singleton, List.length_nil, Nat.add_zero]
                using inherited
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := FinDist.support_map .. ▸ moved
                  have schedulerRecall : next.environmentRecall = execution.environmentRecall ++
                      [⟨execution.observeEnvironment (application setup leaks), command⟩] := by
                    obtain ⟨updated, _, equal⟩ := FinDist.support_map .. ▸ supported
                    cases equal
                    rfl
                  have activations := scheduled_activation_count setup leaks watcher
                    execution.environmentRecall
                    (execution.observeEnvironment (application setup leaks))
                    command selected
                  simp only [CountedDepth, Option.toList_none, List.length_nil, Nat.add_zero]
                    at inherited
                  simp only [CountedDepth, Trace.length, schedulerRecall, List.length_append,
                    List.length_singleton, activations]
                  omega

/-- Actual raw decision histories have the service cursor plus the number of
preceding activations as their depth. No strategy restrictions are needed. -/
theorem raw_decision_depth (watcher who : Player) (control : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).Trace (some control))
    (active : control.actor = some who) :
    trace.length = control.execution.environmentRecall.length +
      activationCount setup watcher control.execution.environmentRecall.length := by
  have counted := trace_counted_depth setup leaks watcher trace
  simp only [CountedDepth, active, Option.toList_some, List.length_singleton] at counted
  omega

/-- Exact owner decision depth at its actual calendar position, including all
previous owner and watcher response steps. -/
theorem raw_owner_decision_depth (watcher owner : Player) (reveals : setup.program.RevealOnly)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner)
    (control : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).Trace (some control))
    (active : control.actor = some owner)
    (position : control.execution.environmentRecall.length = blockOffset event.val + 2) :
    trace.length = blockOffset event.val + 2 * event.val + 3 := by
  rw [raw_decision_depth setup leaks watcher owner control trace active, position,
    owner_activation_count setup watcher owner reveals event owned]
  omega

/-- Exact watcher decision depth at its actual calendar position. -/
theorem raw_watcher_decision_depth (watcher owner : Player) (reveals : setup.program.RevealOnly)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner)
    (control : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).Trace (some control))
    (active : control.actor = some watcher)
    (position : control.execution.environmentRecall.length = blockOffset event.val + 4) :
    trace.length = blockOffset event.val + 2 * event.val + 6 := by
  rw [raw_decision_depth setup leaks watcher watcher control trace active, position,
    watcher_activation_count setup watcher owner reveals event owned]
  omega

/-- A theorem-side depth computed from information already visible to the
acting player. No field is added to the native observation. -/
def decisionDepth (watcher who : Player) : (application setup leaks).Info → Nat
  | none => 0
  | some (_, view) => match view.application.publicView.serviceGrant with
    | none => 0
    | some event => blockOffset event.val + 2 * event.val + if who = watcher then 6 else 3

theorem raw_decision_depth_observed (watcher who : Player)
    (reveals : setup.program.RevealOnly)
    (separate : ∀ event, (graph setup).actor? event ≠ some watcher)
    (control : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).Trace (some control))
    (active : control.actor = some who) :
    trace.length = decisionDepth setup leaks watcher who
      ((application setup leaks).observe who (some control)) := by
  obtain ⟨event, granted, located⟩ := raw_decision_calendar setup leaks watcher who reveals
    control trace active
  simp only [ReactiveApplication.observe, active, ↓reduceIte, decisionDepth]
  change trace.length = match control.execution.application.serviceGrant with
    | none => 0
    | some current => blockOffset current.val + 2 * current.val +
        if who = watcher then 6 else 3
  rw [granted]
  rcases located with ⟨position, owned⟩ | ⟨position, same⟩
  · have different : who ≠ watcher := by
      intro same
      exact separate event (same ▸ owned)
    rw [ite_eq_right different]
    exact raw_owner_decision_depth setup leaks watcher who reveals event owned control
      trace active position
  · subst who
    rw [ite_eq_left rfl]
    obtain ⟨owner, owned⟩ := source_owner setup reveals event
    exact raw_watcher_decision_depth setup leaks watcher owner reveals event owned control
      trace active position

/-- Every information site has one actual trace depth, including sites reached
only after arbitrary malformed traffic, passive leaks or reports. -/
theorem raw_common_decision_depth (watcher : Player) (reveals : setup.program.RevealOnly)
    (separate : ∀ event, (graph setup).actor? event ≠ some watcher)
    (who : Player) (site : ((application setup leaks).information (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).InformationSite who) :
    InformationModel.InformationSite.CommonDepth
      ((application setup leaks).information (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher)) site
      (decisionDepth setup leaks watcher who site.1) := by
  intro history
  have active := InformationModel.InformationSite.active _ site history
  rcases history with ⟨⟨state, trace⟩, observed⟩
  cases state with
  | none => cases active
  | some control =>
      change control.actor = some who at active
      change ((application setup leaks).signals _ _ _).infoOf who trace = site.1 at observed
      rw [(application setup leaks).info] at observed
      change trace.length = decisionDepth setup leaks watcher who site.1
      rw [← observed]
      exact raw_decision_depth_observed setup leaks watcher who reveals separate
        control trace active

/-- The same certificate applies to every finite response menu of this exact
service, including C, W, the normalized menu and the full bounded raw menu. -/
theorem menu_common_decision_depth (responses : (application setup leaks).ResponseMenu)
    (watcher : Player) (reveals : setup.program.RevealOnly)
    (separate : ∀ event, (graph setup).actor? event ≠ some watcher)
    (who : Player) (site : (responses.information (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).InformationSite who) :
    InformationModel.InformationSite.CommonDepth
      (responses.information (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher)) site
      (decisionDepth setup leaks watcher who site.1) := by
  intro history
  have active := InformationModel.InformationSite.active _ site history
  rcases history with ⟨⟨state, trace⟩, observed⟩
  cases state with
  | none => cases active
  | some control =>
      change control.actor = some who at active
      change (responses.signals _ _ _).infoOf who trace = site.1 at observed
      rw [responses.info] at observed
      change trace.length = decisionDepth setup leaks watcher who site.1
      rw [← observed, ← responses.toRawTrace_length]
      exact raw_decision_depth_observed setup leaks watcher who reveals separate control
        (responses.toRawTrace _ _ _ trace) active

end Vegas.SourceProgram.RevealService
