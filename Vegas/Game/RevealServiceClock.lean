/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealService
import GameTheory.Analysis.Protocol.CounterfactualDecomposition

/-! # Decision positions in the revelation service calendar

Each source event contributes one owner activation and one watcher activation.
The counts below concern the existing service plan and raw protocol traces;
they do not add a clock or a scheduler cursor to player observations.
-/

noncomputable section

namespace Vegas

open SourceProgram

open EventGraphRuntime Interaction GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The fixed actor of a revelation-service instruction. Wire turns only
include or wait, and therefore do not activate another player. -/
def instructionActor {graph : Vegas.EventGraph Player L} : ServiceInstruction graph → Option Player
  | .player who => some who
  | _ => none

/-- The actual service instructions before a given source rank. -/
def planPrefix (setup : Setup (Player := Player) (L := L)) (watcher : Player) (rank : Nat) :
    List (ServiceInstruction (graph setup)) :=
  ((List.finRange (graph setup).order.eventCount).take rank).flatMap (block setup watcher)

/-- Scheduler instructions preceding source rank `rank`. -/
def blockOffset (rank : Nat) : Nat := (Finset.range rank).sum fun index => index + 6

theorem blockOffset_succ (rank : Nat) : blockOffset (rank + 1) = blockOffset rank + rank + 6 := by
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
      change blockOffset rank + (rank + 6) = blockOffset rank + rank + 6
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

/-- The owner is activated first in its block, before any watcher step. -/
theorem plan_take_owner (setup : Setup (Player := Player) (L := L)) (watcher owner : Player)
    (reveals : setup.program.RevealOnly) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner) :
    (plan setup watcher).take (blockOffset event.val + 1) =
      planPrefix setup watcher event.val ++ [.player owner] := by
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
    (plan setup watcher).take (blockOffset event.val + 3) =
      planPrefix setup watcher event.val ++
        [.player owner, .includeLatest event owner, .player watcher] := by
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
    (index = 0 ∧ who = owner) ∨ (index = 2 ∧ who = watcher) := by
  rw [block_of_owner setup watcher owner event owned] at active
  rcases index with _ | _ | _ | _ | index
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
      (index = blockOffset event.val ∧ (graph setup).actor? event = some who) ∨
      (index = blockOffset event.val + 2 ∧ who = watcher) := by
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
    change index - blockOffset rank < rank + 6
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
    change index = blockOffset rank
    omega
  · refine Or.inr ⟨?_, same⟩
    change index = blockOffset rank + 2
    omega

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- Number of actual player activations among the first `count` service steps. -/
def activationCount (watcher : Player) (count : Nat) : Nat :=
  (((plan setup watcher).take count).filterMap instructionActor).length

theorem owner_activation_count (watcher owner : Player) (reveals : setup.program.RevealOnly)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner) :
    activationCount setup watcher (blockOffset event.val + 1) = 2 * event.val + 1 := by
  rw [activationCount, plan_take_owner setup watcher owner reveals event owned,
    List.filterMap_append, List.length_append,
    planPrefix_actors_length setup watcher reveals event.val event.isLt.le]
  rfl

theorem watcher_activation_count (watcher owner : Player) (reveals : setup.program.RevealOnly)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner) :
    activationCount setup watcher (blockOffset event.val + 3) = 2 * event.val + 2 := by
  rw [activationCount, plan_take_watcher setup watcher owner reveals event owned,
    List.filterMap_append, List.length_append,
    planPrefix_actors_length setup watcher reveals event.val event.isLt.le]
  rfl

theorem instruction_actor
    (history : List (application setup leaks).EnvironmentEntry)
    (view : (application setup leaks).EnvironmentView)
    (instruction : ServiceInstruction (graph setup)) (command : (application setup leaks).Command)
    (supported : command ∈ ((runtime setup).interactionInstruction leaks
      ((runtime setup).idleNetwork leaks) history view instruction).support) :
    command.actor? (application setup leaks) = instructionActor instruction := by
  cases instruction with
  | player who | sample event | tick | expire event =>
      simp only [EventGraphRuntime.interactionInstruction, PMF.mem_support_pure_iff _ _]
        at supported
      subst command
      rfl
  | includeLatest event owner =>
      simp only [EventGraphRuntime.interactionInstruction, PMF.mem_support_pure_iff _ _]
        at supported
      subst command
      unfold reactiveLatest
      split <;> rfl
  | wire =>
      rw [(runtime setup).idleNetwork_instruction leaks history view,
        PMF.mem_support_pure_iff _ _] at supported
      subst command
      rfl

private theorem scheduler_activation_position (watcher who : Player)
    (reveals : setup.program.RevealOnly)
    (history : List (application setup leaks).EnvironmentEntry)
    (view : (application setup leaks).EnvironmentView) (command : (application setup leaks).Command)
    (supported : command ∈ (scheduler setup leaks watcher history view).support)
    (active : command.actor? (application setup leaks) = some who) :
    ∃ event : (graph setup).EventId,
      (history.length = blockOffset event.val ∧ (graph setup).actor? event = some who) ∨
      (history.length = blockOffset event.val + 2 ∧ who = watcher) := by
  unfold scheduler at supported
  cases selected : (plan setup watcher)[history.length]? with
  | none =>
      rw [selected, PMF.mem_support_pure_iff _ _] at supported
      subst command
      cases active
  | some instruction =>
      rw [selected] at supported
      apply plan_activation_position setup watcher who reveals history.length
      rw [selected]
      exact (instruction_actor setup leaks history view instruction command supported).symm
        |>.trans active

private def ActiveCalendar (watcher : Player) : (application setup leaks).ProtocolState → Prop
  | none => True
  | some control => ∀ who, control.actor = some who →
      ∃ event : (graph setup).EventId,
        (control.execution.environmentRecall.length = blockOffset event.val + 1 ∧
            (graph setup).actor? event = some who) ∨
          (control.execution.environmentRecall.length = blockOffset event.val + 3 ∧ who = watcher)

private theorem trace_active_calendar (watcher : Player) (reveals : setup.program.RevealOnly) :
    ∀ {state} (_trace : ((application setup leaks).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).Trace state),
      ActiveCalendar setup leaks watcher state
  | _, .start => trivial
  | _, @Trace.extend _ _ source target before joint legal realized => by
      have reached : target ∈ ((application setup leaks).transition (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher) source joint).support := realized
      cases source with
      | none =>
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ reached
          intro who active
          cases active
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              intro who active
              cases active
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  have recall : next.environmentRecall = execution.environmentRecall ++
                      [⟨execution.observeEnvironment (application setup leaks), command⟩] := by
                    obtain ⟨updated, _, equal⟩ := PMF.support_map .. ▸ supported
                    cases equal
                    rfl
                  intro who active
                  obtain ⟨event, located⟩ := scheduler_activation_position setup leaks watcher who
                    reveals execution.environmentRecall
                    (execution.observeEnvironment (application setup leaks)) command selected active
                  refine ⟨event, ?_⟩
                  change (next.environmentRecall.length = _ ∧ _) ∨
                    (next.environmentRecall.length = _ ∧ _)
                  rw [recall, List.length_append, List.length_singleton]
                  rcases located with ⟨position, owned⟩ | ⟨position, same⟩
                  · exact Or.inl ⟨by omega, owned⟩
                  · exact Or.inr ⟨by omega, same⟩

/-- Every raw decision occurs at one of the two declared positions of a source
event's block. Repeated source owners are permitted. -/
theorem raw_decision_calendar (watcher who : Player) (reveals : setup.program.RevealOnly)
    (control : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).Trace (some control))
    (active : control.actor = some who) :
    ∃ event : (graph setup).EventId,
      (control.execution.environmentRecall.length = blockOffset event.val + 1 ∧
          (graph setup).actor? event = some who) ∨
        (control.execution.environmentRecall.length = blockOffset event.val + 3 ∧ who = watcher) :=
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
      rw [selected, PMF.mem_support_pure_iff _ _] at supported
      subst command
      simp only [activationCount, List.take_add_one, selected, Option.toList_none,
        List.append_nil, ReactiveApplication.Command.actor?, List.length_nil, Nat.add_zero]
  | some instruction =>
      rw [selected] at supported
      have actor := instruction_actor setup leaks history view instruction command supported
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
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ reached
          have counted : before.length = 0 := inherited
          simpa only [CountedDepth, Trace.length, ReactiveApplication.Execution.initial,
            List.length_nil, Option.toList_none, Nat.add_zero, activationCount,
            List.take_zero, List.filterMap_nil] using congrArg (· + 1) counted
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              simpa only [CountedDepth, Trace.length,
                (application setup leaks).respond_environmentRecall, Option.toList_some,
                Option.toList_none, List.length_singleton, List.length_nil, Nat.add_zero]
                using inherited
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  have schedulerRecall : next.environmentRecall = execution.environmentRecall ++
                      [⟨execution.observeEnvironment (application setup leaks), command⟩] := by
                    obtain ⟨updated, _, equal⟩ := PMF.support_map .. ▸ supported
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
    (position : control.execution.environmentRecall.length = blockOffset event.val + 1) :
    trace.length = blockOffset event.val + 2 * event.val + 2 := by
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
    (position : control.execution.environmentRecall.length = blockOffset event.val + 3) :
    trace.length = blockOffset event.val + 2 * event.val + 5 := by
  rw [raw_decision_depth setup leaks watcher watcher control trace active, position,
    watcher_activation_count setup watcher owner reveals event owned]
  omega

/-- The clock ticks of the service plan before a source rank. -/
def ticksBefore (watcher : Player) (rank : Nat) : Nat :=
  serviceTicks (planPrefix setup watcher rank)

theorem ticksBefore_succ (watcher : Player) (event : (graph setup).EventId) :
    ticksBefore setup watcher (event.val + 1) =
      ticksBefore setup watcher event.val + (event.val + 1) := by
  unfold ticksBefore
  rw [planPrefix_succ, serviceTicks_append]
  congr 1
  unfold block
  cases (graph setup).actor? event <;>
    simp [serviceTicks, ServiceInstruction.ticks, runtime]

private theorem ticksBefore_lt (watcher : Player) (rank later : Nat) (earlier : rank < later)
    (within : later ≤ (graph setup).order.eventCount) :
    ticksBefore setup watcher rank < ticksBefore setup watcher later := by
  induction later with
  | zero => omega
  | succ later ih =>
      have inside : later < (graph setup).order.eventCount := by omega
      have step := ticksBefore_succ setup watcher ⟨later, inside⟩
      change ticksBefore setup watcher (later + 1) =
        ticksBefore setup watcher later + (later + 1) at step
      by_cases same : rank = later
      · subst rank
        omega
      · have below := ih (by omega) (by omega)
        omega

private theorem rank_le_ticksBefore (watcher : Player) (rank : Nat)
    (within : rank ≤ (graph setup).order.eventCount) : rank ≤ ticksBefore setup watcher rank := by
  induction rank with
  | zero => omega
  | succ rank ih =>
      have inside : rank < (graph setup).order.eventCount := by omega
      have step := ticksBefore_succ setup watcher ⟨rank, inside⟩
      change ticksBefore setup watcher (rank + 1) =
        ticksBefore setup watcher rank + (rank + 1) at step
      have below := ih (by omega)
      omega

/-- The source rank of a block whose decisions see the public clock `clock`. -/
def clockRank (watcher : Player) (clock : Nat) : Nat :=
  Nat.findGreatest (fun rank => ticksBefore setup watcher rank ≤ clock) clock

theorem clockRank_ticksBefore (watcher : Player) (event : (graph setup).EventId) :
    clockRank setup watcher (ticksBefore setup watcher event.val) = event.val := by
  unfold clockRank
  apply (Nat.findGreatest_eq_iff).mpr
  refine ⟨rank_le_ticksBefore setup watcher event.val event.isLt.le, fun _ => le_rfl, ?_⟩
  intro later earlier bounded
  by_cases inside : later ≤ (graph setup).order.eventCount
  · exact not_le.mpr (ticksBefore_lt setup watcher event.val later earlier inside)
  · intro atMost
    have monotone := ticksBefore_lt setup watcher event.val
      (graph setup).order.eventCount event.isLt le_rfl
    have full : ticksBefore setup watcher later = ticksBefore setup watcher
        (graph setup).order.eventCount := by
      unfold ticksBefore planPrefix
      rw [List.take_of_length_le (by simp only [List.length_finRange]; omega),
        List.take_of_length_le (by simp only [List.length_finRange]; exact le_rfl)]
    omega

private def commandTicks : (application setup leaks).Command → Nat
  | .application command => command.clockTicks
  | _ => 0

private theorem instruction_ticks
    (history : List (application setup leaks).EnvironmentEntry)
    (view : (application setup leaks).EnvironmentView)
    (instruction : ServiceInstruction (graph setup)) (command : (application setup leaks).Command)
    (supported : command ∈ ((runtime setup).interactionInstruction leaks
      ((runtime setup).idleNetwork leaks) history view instruction).support) :
    commandTicks setup leaks command = instruction.ticks := by
  cases instruction with
  | player who | sample event | tick | expire event =>
      simp only [EventGraphRuntime.interactionInstruction, PMF.mem_support_pure_iff _ _]
        at supported
      subst command
      rfl
  | includeLatest event owner =>
      simp only [EventGraphRuntime.interactionInstruction, PMF.mem_support_pure_iff _ _]
        at supported
      subst command
      unfold reactiveLatest
      split <;> rfl
  | wire =>
      rw [(runtime setup).idleNetwork_instruction leaks history view,
        PMF.mem_support_pure_iff _ _] at supported
      subst command
      rfl

private def calendarTicks (watcher : Player) (count : Nat) : Nat :=
  serviceTicks ((plan setup watcher).take count)

private theorem scheduled_ticks (watcher : Player)
    (history : List (application setup leaks).EnvironmentEntry)
    (view : (application setup leaks).EnvironmentView) (command : (application setup leaks).Command)
    (supported : command ∈ (scheduler setup leaks watcher history view).support) :
    calendarTicks setup watcher (history.length + 1) =
      calendarTicks setup watcher history.length + commandTicks setup leaks command := by
  unfold scheduler at supported
  cases selected : (plan setup watcher)[history.length]? with
  | none =>
      rw [selected, PMF.mem_support_pure_iff _ _] at supported
      subst command
      simp only [calendarTicks, List.take_add_one, selected, Option.toList_none,
        List.append_nil, commandTicks, Nat.add_zero]
  | some instruction =>
      rw [selected] at supported
      rw [instruction_ticks setup leaks history view instruction command supported]
      simp only [calendarTicks, List.take_add_one, selected, Option.toList_some,
        serviceTicks_append, serviceTicks_cons, serviceTicks_nil, Nat.add_zero]

private theorem respond_clock (execution : (application setup leaks).Execution) (who : Player)
    (response : (application setup leaks).Action) :
    (execution.respond (application setup leaks) who response).application.clock =
      execution.application.clock := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some submission =>
      have visible := submission.call.register_facts who execution.application |>.2
      change (submitStep (submission.call.register execution.application who) who
        submission.call.packet).clock = execution.application.clock
      rw [submitStep_clock]
      exact congrArg PublicView.clock visible

private theorem environment_clock (before after : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (reached : after ∈ (before.environmentStep (application setup leaks) command).support) :
    after.application.clock = before.application.clock + commandTicks setup leaks command := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨sample, _, rfl⟩ := PMF.support_map .. ▸ supported
      rfl
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      change (before.includePending (application setup leaks) id).application.clock = _ + 0
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : before.network.lookup id with
      | none => rfl
      | some message =>
          change (((application setup leaks).handle before.application
            message).getD before.application).clock = _ + 0
          cases accepted : (application setup leaks).handle before.application
              message with
          | none => rfl
          | some next =>
              exact ((runtime setup).handle_clock_activated _ _ _
                (reactiveHandle_call accepted)).1
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      exact (runtime setup).environmentStep_clock before.application state command changed

private def ClockCalendar (watcher : Player) : (application setup leaks).ProtocolState → Prop
  | none => True
  | some control => control.execution.application.clock =
      calendarTicks setup watcher control.execution.environmentRecall.length

private theorem trace_clock_calendar (watcher : Player) :
    ∀ {state} (_trace : ((application setup leaks).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).Trace state),
      ClockCalendar setup leaks watcher state
  | _, .start => trivial
  | _, @Trace.extend _ _ source target before joint legal realized => by
      have inherited := trace_clock_calendar watcher before
      have reached : target ∈ ((application setup leaks).transition (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher) source joint).support := realized
      cases source with
      | none =>
          obtain ⟨initial, supported, rfl⟩ := PMF.support_map .. ▸ reached
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
          rfl
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              change
                (execution.respond (application setup leaks) who _).application.clock = _
              rw [respond_clock, (application setup leaks).respond_environmentRecall]
              exact inherited
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  have recall : next.environmentRecall = execution.environmentRecall ++
                      [⟨execution.observeEnvironment (application setup leaks), command⟩] := by
                    obtain ⟨updated, _, equal⟩ := PMF.support_map .. ▸ supported
                    cases equal
                    rfl
                  change next.application.clock = _
                  rw [recall, List.length_append, List.length_singleton,
                    scheduled_ticks setup leaks watcher _ _ command selected,
                    environment_clock setup leaks execution next command supported]
                  change execution.application.clock = _ at inherited
                  rw [inherited]

/-- A theorem-side depth computed from information already visible to the
acting player: the public clock fixes the source block, since the clock only
advances after both decisions of a block. No field is added to the native
observation. -/
def decisionDepth (watcher who : Player) : (application setup leaks).Info → Nat
  | none => 0
  | some (_, view) =>
      let rank := clockRank setup watcher view.application.publicView.clock
      blockOffset rank + 2 * rank + if who = watcher then 5 else 2

theorem raw_decision_depth_observed (watcher who : Player)
    (reveals : setup.program.RevealOnly)
    (separate : ∀ event, (graph setup).actor? event ≠ some watcher)
    (control : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).Trace (some control))
    (active : control.actor = some who) :
    trace.length = decisionDepth setup leaks watcher who
      ((application setup leaks).observe who (some control)) := by
  obtain ⟨event, located⟩ := raw_decision_calendar setup leaks watcher who reveals
    control trace active
  have clocked := trace_clock_calendar setup leaks watcher trace
  change control.execution.application.clock =
    calendarTicks setup watcher control.execution.environmentRecall.length at clocked
  obtain ⟨owner, owned⟩ := source_owner setup reveals event
  have rank : clockRank setup watcher control.execution.application.clock = event.val := by
    rw [clocked]
    rcases located with ⟨position, _⟩ | ⟨position, _⟩
    · rw [position, calendarTicks, plan_take_owner setup watcher owner reveals event owned,
        serviceTicks_append]
      simpa only [serviceTicks_cons, serviceTicks_nil, ServiceInstruction.ticks, Nat.add_zero,
        ticksBefore] using clockRank_ticksBefore setup watcher event
    · rw [position, calendarTicks, plan_take_watcher setup watcher owner reveals event owned,
        serviceTicks_append]
      simpa only [serviceTicks_cons, serviceTicks_nil, ServiceInstruction.ticks, Nat.add_zero,
        ticksBefore] using clockRank_ticksBefore setup watcher event
  simp only [ReactiveApplication.observe, active, ↓reduceIte, decisionDepth]
  change trace.length = blockOffset (clockRank setup watcher control.execution.application.clock) +
      2 * clockRank setup watcher control.execution.application.clock +
        if who = watcher then 5 else 2
  rw [rank]
  rcases located with ⟨position, actor⟩ | ⟨position, same⟩
  · have different : who ≠ watcher := by
      intro same
      exact separate event (same ▸ actor)
    rw [ite_eq_right different]
    exact raw_owner_decision_depth setup leaks watcher who reveals event actor control
      trace active position
  · subst who
    rw [ite_eq_left rfl]
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

end Vegas
