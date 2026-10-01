/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SelectiveAssociation.History

/-! # The owner's response count determines the native decision cursor

These facts apply to every legal history, including histories outside an
assessment's support. Each player's activations follow the fixed calendar, so
a player's own count of earlier responses identifies which of its scheduled
decisions is current: the two ambient prelude responses and each owner's
service turn are told apart by the owner's recall, with no service
announcement.
-/

noncomputable section

namespace Vegas.Examples.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

variable {observation : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph)}

def nativeInstructionPlayer : ServiceInstruction nativeGraph → Option Player
  | .player who => some who
  | _ => none

theorem native_instruction_actor (instruction : ServiceInstruction nativeGraph)
    (history : List (serviceApp observation).EnvironmentEntry) (view : (serviceApp
      observation).EnvironmentView)
    (command : (serviceApp observation).Command)
    (supported : command ∈ (nativeRuntime.interactionInstruction observation (serviceNetwork
      observation)
      history view instruction).support) :
    command.actor? (serviceApp observation) = nativeInstructionPlayer instruction := by
  cases instruction with
  | player who | sample event | tick | expire event =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rfl
  | wire =>
      simp only [interactionInstruction, serviceNetwork, PMF.pure_map,
        PMF.mem_support_pure_iff _ _] at supported
      subst command
      rfl
  | includeLatest event owner =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      unfold reactiveLatest
      split <;> rfl

def nativeResponseCount (who : Player) (plan : List (ServiceInstruction nativeGraph)) : Nat :=
  (plan.map fun instruction => if nativeInstructionPlayer instruction = some who then 1 else 0).sum

private theorem dispatch_recall_count (players : Player → (serviceApp observation).Policy)
    (execution next : (serviceApp observation).Execution) (command : (serviceApp
      observation).Command) (who : Player)
    (reached : next ∈ ((serviceApp observation).dispatch players command execution).support) :
    (next.recall who).length = (execution.recall who).length +
      if command.actor? (serviceApp observation) = some who then 1 else 0 := by
  obtain ⟨observed, observedMem, resumed⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have same := (serviceApp observation).environmentStep_recall execution observed command
    observedMem
  cases actor : command.actor? (serviceApp observation) with
  | none =>
      simp only [actor, ReactiveApplication.resume, PMF.mem_support_pure_iff _ _] at resumed
      subst next
      simp only [same, reduceCtorEq, ↓reduceIte, Nat.add_zero]
  | some owner =>
      rw [actor] at resumed
      obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
      by_cases identical : who = owner
      · subst who
        have count := congrArg List.length ((serviceApp observation).respond_actions observed
          owner response)
        simp only [List.length_map, List.length_append, List.length_singleton] at count
        simpa only [same, ↓reduceIte] using count
      · rw [(serviceApp observation).respond_recall_other observed owner who identical response,
        same]
        simp only [Option.some.injEq, Ne.symm identical, ↓reduceIte, Nat.add_zero]

theorem native_step_recall_count (players : Player → (serviceApp observation).Policy)
    (instruction : ServiceInstruction nativeGraph) (execution next : (serviceApp
      observation).Execution)
    (who : Player)
    (reached : next ∈ (nativeRuntime.interactionStep observation players (serviceNetwork
      observation)
      instruction execution).support) :
    (next.recall who).length = (execution.recall who).length +
      if nativeInstructionPlayer instruction = some who then 1 else 0 := by
  obtain ⟨command, commandMem, dispatched⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have count := dispatch_recall_count players execution next command who dispatched
  rw [native_instruction_actor instruction _ _ command commandMem] at count
  exact count

theorem native_plan_recall_count (players : Player → (serviceApp observation).Policy)
    (plan : List (ServiceInstruction nativeGraph)) (execution next : (serviceApp
      observation).Execution)
    (who : Player)
    (reached : next ∈ (nativeRuntime.runInteractionPlan observation players (serviceNetwork
      observation)
      plan execution).support) :
    (next.recall who).length = (execution.recall who).length + nativeResponseCount who plan := by
  induction plan generalizing execution with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      simp [nativeResponseCount]
  | cons instruction rest ih =>
      obtain ⟨middle, first, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      rw [ih middle later, native_step_recall_count players instruction execution middle who first]
      simp only [nativeResponseCount, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- Every player's recall after a legal prefix of `count` rounds counts that
player's scheduled responses in the prefix. -/
theorem native_rounds_recall_count (players : Player → (serviceApp observation).Policy)
    (count : Nat) (bounded : count ≤ nativePlan.length)
    (execution : (serviceApp observation).Execution)
    (reached : execution ∈ ((serviceApp observation).roundsFrom (PMF.pure nativeInitial)
      (serviceScheduler observation) players count).support) (who : Player) :
    (execution.recall who).length = nativeResponseCount who (nativePlan.take count) := by
  have split := native_roundsFrom_prefix players (nativePlan.take count) (nativePlan.drop count)
    (List.take_append_drop count nativePlan).symm
  rw [List.length_take_of_le bounded] at split
  rw [split] at reached
  simpa only [nativeRoot, ReactiveApplication.Execution.initial, List.length_nil,
    Nat.zero_add] using native_plan_recall_count players _ nativeRoot execution who reached

/-- The owner's response count at `event`'s service turn. -/
def nativeTurnCount (event : nativeGraph.EventId) : Nat :=
  nativeResponseCount (nativeOwner event) (nativeBeforeResponse event)

/-- `control` is the owner's decision at `event`'s service turn: the owner is
active, and its own count of earlier responses is the one scheduled before
that turn. This is the owner's own knowledge; no public announcement names the
event. -/
def NativeTurn (event : nativeGraph.EventId) (control : (serviceApp observation).Control) :
    Prop :=
  control.actor = some (nativeOwner event) ∧
    (control.execution.recall (nativeOwner event)).length = nativeTurnCount event

/-- The event, if any, whose service turn is the decision of `who` after
`count` earlier responses of its own; `none` at the ambient prelude responses.
Players read it from their own recall. -/
def nativeTurnEvent? (who : Player) (count : Nat) : Option nativeGraph.EventId :=
  (List.finRange nativeGraph.order.eventCount).find? fun event =>
    nativeOwner event = who ∧ nativeTurnCount event = count

theorem nativeTurnEvent?_spec {who : Player} {count : Nat} {event : nativeGraph.EventId}
    (selected : nativeTurnEvent? who count = some event) :
    nativeOwner event = who ∧ nativeTurnCount event = count := by
  have chosen := List.find?_some selected
  exact of_decide_eq_true chosen

theorem nativeTurnEvent?_turnCount (event : nativeGraph.EventId) :
    nativeTurnEvent? (nativeOwner event) (nativeTurnCount event) = some event := by
  fin_cases event <;> decide

theorem NativeTurn.of_turnEvent? {event : nativeGraph.EventId}
    {control : (serviceApp observation).Control} {who : Player}
    (active : control.actor = some who)
    (selected : nativeTurnEvent? who (control.execution.recall who).length = some event) :
    NativeTurn event control := by
  obtain ⟨owner, counted⟩ := nativeTurnEvent?_spec selected
  subst who
  exact ⟨active, counted.symm⟩

theorem NativeTurn.turnEvent? {event : nativeGraph.EventId}
    {control : (serviceApp observation).Control} (turn : NativeTurn event control) :
    nativeTurnEvent? (nativeOwner event) (control.execution.recall (nativeOwner event)).length =
      some event := by
  rw [turn.2]
  exact nativeTurnEvent?_turnCount event

theorem NativeTurn.turnEvent?_of_active {event : nativeGraph.EventId}
    {control : (serviceApp observation).Control} {who : Player} (turn : NativeTurn event control)
    (active : control.actor = some who) :
    nativeTurnEvent? who (control.execution.recall who).length = some event := by
  obtain rfl : who = nativeOwner event := Option.some.inj (active.symm.trans turn.1)
  exact turn.turnEvent?

/-- Among each owner's scheduled activations, its earlier-response count picks
out the service turn of each event it owns. -/
private theorem turn_positions : ∀ position : Fin nativePlan.length,
    ∀ event : nativeGraph.EventId,
      (nativePlan[position.val]?).bind nativeInstructionPlayer = some (nativeOwner event) →
      nativeResponseCount (nativeOwner event) (nativePlan.take position.val) =
        nativeTurnCount event →
      position.val = (nativeBeforeResponse event).length := by
  decide

/-- The owner's response count distinguishes all six later decision sites,
even when the same player owns several events. -/
theorem native_decision_cursor (event : nativeGraph.EventId) (control : (serviceApp
  observation).Control)
    (trace : (serviceArena observation).Trace (some control)) (who : Player)
    (active : control.actor = some who)
    (turn : NativeTurn event control) :
    who = nativeOwner event ∧ control.execution.environmentRecall.length =
      (nativeBeforeResponse event).length + 1 := by
  have owner : who = nativeOwner event := Option.some.inj (active.symm.trans turn.1)
  subst who
  obtain ⟨accounted, supported⟩ := (serviceMenu observation).roundSupported_uniform
    (PMF.pure nativeInitial) nativeHorizon (serviceScheduler observation) trace
  rw [active] at supported
  obtain ⟨count, prior, command, position, priorMem, commandMem, actor, observed⟩ := supported
  have cursor := (serviceApp observation).roundsFrom_recall (PMF.pure nativeInitial)
    (serviceScheduler observation)
    (serviceMenu observation).uniformResponses count prior priorMem
  have bounded : count < nativePlan.length := by
    change _ + _ = nativePlan.length at accounted
    omega
  have selected : (nativePlan[count]?).bind nativeInstructionPlayer =
      some (nativeOwner event) := by
    simp only [serviceScheduler, cursor] at commandMem
    cases found : nativePlan[count]? with
    | none =>
        simp only [found, PMF.mem_support_pure_iff _ _] at commandMem
        subst command
        cases actor
    | some instruction =>
        rw [found] at commandMem
        simp only [Option.bind_some]
        exact (native_instruction_actor instruction _ _ command commandMem).symm.trans actor
  have recalled := native_rounds_recall_count (serviceMenu observation).uniformResponses count
    bounded.le prior priorMem (nativeOwner event)
  rw [← (serviceApp observation).environmentStep_recall prior control.execution _ observed,
    turn.2] at recalled
  have located : count = (nativeBeforeResponse event).length :=
    turn_positions ⟨count, bounded⟩ event selected recalled.symm
  exact ⟨rfl, by omega⟩

/-- At the scheduled cursor of `event`'s turn, the active owner's response
count is the scheduled one. -/
theorem native_turn_of_decision_cursor (event : nativeGraph.EventId)
    (control : (serviceApp observation).Control) (trace : (serviceArena observation).Trace (some
      control))
    (active : control.actor = some (nativeOwner event))
    (position : control.execution.environmentRecall.length =
      (nativeBeforeResponse event).length + 1) :
    NativeTurn event control := by
  obtain ⟨_, prior, priorMem, activated⟩ :=
    native_decision_predecessor event control trace active position
  refine ⟨active, ?_⟩
  rw [(serviceApp observation).environmentStep_recall prior control.execution _ activated]
  simpa only [nativeTurnCount, nativeRoot, ReactiveApplication.Execution.initial, List.length_nil,
    Nat.zero_add] using native_plan_recall_count (serviceMenu observation).uniformResponses
      (nativeBeforeResponse event) nativeRoot prior (nativeOwner event) priorMem

end Vegas.Examples.SelectiveAssociation
