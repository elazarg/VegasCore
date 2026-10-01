/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRoster
import Vegas.Game.RevealServiceCalendarState
import Vegas.Pending.ReactiveAsyncContract
import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.EventSequentialTiming
import Interaction.ReactiveOwnerSelection
import Interaction.ReactiveRecallInvariant
import Interaction.ReactiveReceipts

/-! # The fixed roster calendar satisfies the asynchronous contract

Event `e` occupies one block of the roster plan: its roster activations, then
protected inclusion of its owner's latest packet (or public sampling), then
`e.val + 1` clock ticks and expiry. On the sequentialized graph `e` becomes
ready only when its predecessor completes inside the predecessor's block, at
the latest at that block's inclusion, so the owner is activated at most
`e.val` slots after `e` became ready. Every owner response that sees `e` ready
happens in `e`'s roster, before its inclusion, so the owner's sole packet is
included within the same slot. Expiry completes every owned event that is
still ready at the end of its block.

The proof is one invariant over every legal history of the raw protocol, for
arbitrary player responses, leak rules and network policies. It locates the
scheduler at a plan position and records the completed prefix, the clock,
activation times, the owner's recorded activation, the readiness and clock
seen by every recorded response, and the receipt of a protected packet.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-! ## Positions in the roster plan -/

theorem rosterPlan_getElem_block (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId)
    (offset : Nat) (inside : offset < (rosterBlock setup rosters event).length) :
    (rosterPlan setup rosters)[(rosterPlanPrefix setup rosters event.val).length + offset]? =
      (rosterBlock setup rosters event)[offset]? := by
  obtain ⟨suffix, split⟩ := rosterPlan_split setup rosters event
  rw [split, List.append_assoc, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_left inside]

theorem rosterPlan_length_block (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId) :
    (rosterPlanPrefix setup rosters event.val).length +
        (rosterBlock setup rosters event).length ≤ (rosterPlan setup rosters).length := by
  obtain ⟨suffix, split⟩ := rosterPlan_split setup rosters event
  rw [split]
  simp only [List.length_append]
  omega

theorem rosterPlanPrefix_eventCount (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) :
    rosterPlanPrefix setup rosters (graph setup).order.eventCount = rosterPlan setup rosters := by
  simp only [rosterPlanPrefix, rosterPlan]
  rw [List.take_of_length_le (by simp only [List.length_finRange]; omega)]

theorem rosterBlock_roster (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId)
    (offset : Nat) (inside : offset < (rosters event).length) :
    (rosterBlock setup rosters event)[offset]? =
      some (.player ((rosters event)[offset]'inside)) := by
  rw [rosterBlock_eq_ending,
    List.getElem?_append_left (by simpa only [List.length_map] using inside),
    List.getElem?_map, List.getElem?_eq_getElem inside]
  rfl

theorem rosterBlock_ending (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId)
    (offset : Nat) :
    (rosterBlock setup rosters event)[(rosters event).length + offset]? =
      (rosterPhaseEnding setup event)[offset]? := by
  rw [rosterBlock_eq_ending, List.getElem?_append_right (by simp only [List.length_map]; omega)]
  simp only [List.length_map, Nat.add_sub_cancel_left]

theorem rosterPhaseEnding_first (setup : Setup (Player := Player) (L := L))
    (event : (graph setup).EventId) :
    (rosterPhaseEnding setup event)[0]? = some (match (graph setup).actor? event with
      | none => .sample event
      | some owner => .includeLatest event owner) := by
  unfold rosterPhaseEnding
  cases (graph setup).actor? event <;> rfl

theorem rosterPhaseEnding_tick (setup : Setup (Player := Player) (L := L))
    (event : (graph setup).EventId) (index : Nat) (inside : index < event.val + 1) :
    (rosterPhaseEnding setup event)[index + 1]? = some .tick := by
  have shape : rosterPhaseEnding setup event =
      (match (graph setup).actor? event with
        | none => ServiceInstruction.sample event
        | some owner => .includeLatest event owner) ::
        (List.replicate (event.val + 1) .tick ++ [.expire event]) := by
    unfold rosterPhaseEnding
    cases (graph setup).actor? event <;> rfl
  rw [shape, List.getElem?_cons_succ,
    List.getElem?_append_left (by simpa only [List.length_replicate] using inside),
    List.getElem?_replicate_of_lt inside]

theorem rosterPhaseEnding_expire (setup : Setup (Player := Player) (L := L))
    (event : (graph setup).EventId) :
    (rosterPhaseEnding setup event)[event.val + 2]? = some (.expire event) := by
  have shape : rosterPhaseEnding setup event =
      (match (graph setup).actor? event with
        | none => ServiceInstruction.sample event
        | some owner => .includeLatest event owner) ::
        (List.replicate (event.val + 1) .tick ++ [.expire event]) := by
    unfold rosterPhaseEnding
    cases (graph setup).actor? event <;> rfl
  rw [shape, List.getElem?_cons_succ,
    List.getElem?_append_right (by simp only [List.length_replicate]; omega)]
  simp only [List.length_replicate, Nat.sub_self, List.getElem?_cons_zero]

/-! ## Event kinds and actors -/

omit [DecidableEq Player] in
theorem nodeView_bind_actor {graph : EventGraph Player L} {event : graph.EventId}
    {owner : Player} {payload : L.Ty}
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload) :
    graph.actor? event = some owner := by
  have castActor : (cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event)).actor = some owner := by
    rw [codeEq]
    rfl
  exact (EventGraph.EventCode.actor_cast outputEq (graph.nodes event)).symm.trans castActor

omit [DecidableEq Player] in
theorem nodeView_resolve_actor {graph : EventGraph Player L} {event : graph.EventId}
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef graph.layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck graph.layout payload)}
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks) :
    graph.actor? event = some owner := by
  have castActor : (cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event)).actor = some owner := by
    rw [codeEq]
    rfl
  exact (EventGraph.EventCode.actor_cast outputEq (graph.nodes event)).symm.trans castActor

omit [DecidableEq Player] in
theorem nodeView_sample_actor {graph : EventGraph Player L} {event : graph.EventId}
    {payload : L.Ty} {law : EventGraph.PublicDist graph.layout payload}
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law) :
    graph.actor? event = none := by
  have castActor : (cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event)).actor = none := by
    rw [codeEq]
    rfl
  exact (EventGraph.EventCode.actor_cast outputEq (graph.nodes event)).symm.trans castActor

/-! ## Selecting a sole authored packet -/

omit [DecidableEq Player] in
private theorem forall₂_exists_right {α β : Type} {R : α → β → Prop} :
    ∀ {left : List α} {right : List β}, List.Forall₂ R left right →
      ∀ item ∈ left, ∃ partner ∈ right, R item partner
  | _, _, .nil, _, member => by cases member
  | _, _, .cons head tail, item, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self .., head⟩
      · obtain ⟨partner, inside, related⟩ := forall₂_exists_right tail item later
        exact ⟨partner, List.mem_cons_of_mem _ inside, related⟩

omit [DecidableEq Player] in
/-- A published identifier has a receipt. -/
theorem receipt_of_published {app : ReactiveApplication Player} (execution : app.Execution)
    (sound : execution.ReceiptsSound app (fun _ => True)) (id : MessageId Player)
    (published : id ∈ execution.network.ledger.map Message.id) :
    ∃ accepted, (id, accepted) ∈ execution.receipts := by
  obtain ⟨message, member, rfl⟩ := List.mem_map.mp published
  obtain ⟨receipt, inside, same, _⟩ := forall₂_exists_right sound message member
  refine ⟨receipt.2, ?_⟩
  rw [← same]
  exact inside

section Selection

variable {graph : EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- An owner's sole authored packet for an event, when unpublished, is pending
and is exactly what `reactiveLatest` selects: every pending envelope by that
author addressed to the event is a copy of it, whatever replays occurred. -/
theorem reactiveLatest_sole
    (execution : (runtime.reactiveApplication leaks).Execution)
    (origins : execution.Provenance (runtime.reactiveApplication leaks))
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (retained : execution.network.PendingOrPublished)
    (event : graph.EventId) (owner : Player)
    (earlier later : List (runtime.reactiveApplication leaks).PlayerEntry)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket graph))
    (split : execution.recall owner = earlier ++ entry :: later)
    (emitted : entry.emitted = some message) (authored : message.sender = owner)
    (addressed : message.payload.call.event? graph = some event)
    (sole : ∀ other ∈ earlier ++ later, ¬ EmitsFor runtime leaks other event)
    (unpublished : message.id ∉ execution.network.ledger.map Message.id) :
    message ∈ execution.network.pending ∧
      runtime.reactiveLatest leaks event owner
        (execution.observeEnvironment (runtime.reactiveApplication leaks)) =
          .include message.id := by
  have output : message ∈ (runtime.reactiveApplication leaks).outputs (execution.recall owner) :=
    List.mem_filterMap.mpr ⟨entry, by rw [split]; simp, emitted⟩
  have pending := ((runtime.reactiveApplication leaks).pending_iff_recalled execution owner
    message authored unpublished origins recalled retained).mpr output
  refine ⟨pending, ?_⟩
  unfold reactiveLatest
  split
  · rename_i absent
    exact (List.find?_eq_none.mp absent message (List.mem_reverse.mpr pending)
      (decide_eq_true ⟨authored, addressed, unpublished⟩)).elim
  · rename_i selected found
    have good := List.find?_some found
    simp only [decide_eq_true_eq] at good
    obtain ⟨selectedAuthored, selectedAddressed, selectedUnpublished⟩ := good
    have selectedPending := List.mem_reverse.mp (List.mem_of_find?_eq_some found)
    have selectedOutput := ((runtime.reactiveApplication leaks).pending_iff_recalled execution
      owner selected selectedAuthored selectedUnpublished origins recalled retained).mp
        selectedPending
    obtain ⟨other, member, otherEmitted⟩ := List.mem_filterMap.mp selectedOutput
    rw [split] at member
    have same : other = entry := by
      by_contra different
      have outside : other ∈ earlier ++ later := by
        simp only [List.mem_append, List.mem_cons] at member ⊢
        tauto
      exact sole other outside ⟨selected, otherEmitted, selectedAddressed⟩
    subst other
    rw [emitted] at otherEmitted
    cases Option.some.inj otherEmitted
    rfl

/-- Including the identifier of a pending envelope records a receipt for it. -/
theorem includePending_receipt_of_pending
    (execution : (runtime.reactiveApplication leaks).Execution)
    (message : Message Player (WitnessedPacket graph))
    (pending : message ∈ execution.network.pending) :
    ∃ accepted, (message.id, accepted) ∈
      (execution.includePending (runtime.reactiveApplication leaks) message.id).receipts := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  cases found : execution.network.lookup message.id with
  | none =>
      exact (List.find?_eq_none.mp found message pending (decide_eq_true rfl)).elim
  | some selected =>
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _)⟩

end Selection

/-! ## Facts at every legal history -/

/-- Scheduler-independent facts at every legal roster-service history: the
runtime invariant, envelope provenance, input recall, retention of known
envelopes, and receipts for published envelopes. -/
theorem roster_trace_facts (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control)) :
    (∃ inputs, control.execution.application.Invariant inputs) ∧
      control.execution.Provenance (application setup leaks) ∧
      control.execution.InputRecall (application setup leaks) ∧
      control.execution.network.PendingOrPublished ∧
      control.execution.ReceiptsSound (application setup leaks) (fun _ => True) := by
  let preserved : (application setup leaks).Invariant
      (fun state : EventGraphRuntime.State (graph setup) => ∃ inputs, state.Invariant inputs) := {
    submit := by
      rintro state who material ⟨inputs, valid⟩
      exact ⟨inputs, ((runtime setup).reactiveStateInvariant leaks inputs).submit state who
        material valid⟩
    handle := by
      rintro state message next ⟨inputs, valid⟩ accepted
      exact ⟨inputs, ((runtime setup).reactiveStateInvariant leaks inputs).handle state message
        next valid accepted⟩
    environment := by
      rintro state command next ⟨inputs, valid⟩ reached
      exact ⟨inputs, ((runtime setup).reactiveStateInvariant leaks inputs).environment state
        command next valid reached⟩ }
  have receipts : (application setup leaks).ServiceInvariant scheduler
      (fun execution => execution.ReceiptsSound (application setup leaks) (fun _ => True)) :=
    { respond := fun execution who action valid =>
        (application setup leaks).receiptsSound_respond _ execution who action valid
      environment := fun execution next command valid _ reached =>
        (application setup leaks).receiptsSound_environmentStep _ execution next command valid
          (fun _ _ _ => trivial) reached }
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact preserved.history (initialLaw setup) horizon scheduler (by
      intro state supported
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨_, State.initial_invariant _⟩) trace
  · exact (application setup leaks).history_provenance (initialLaw setup) horizon scheduler trace
  · exact (application setup leaks).history_inputRecall (initialLaw setup) horizon scheduler trace
  · exact (application setup leaks).pendingOrPublished_history scheduler (initialLaw setup)
      horizon trace
  · exact receipts.history (initialLaw setup) horizon
      (fun state _ => (application setup leaks).receiptsSound_initial _ state) trace

/-! ## Graph steps of the application -/

section GraphStep

variable {graph : EventGraph Player L}

omit [DecidableEq Player] in
/-- Either the graph, clock and activation table are unchanged, or one graph
step completes a ready event and activation times are refreshed around it. -/
def GraphStep (before after : EventGraphRuntime.State graph) : Prop :=
  (after.config = before.config ∧ after.clock = before.clock ∧
      after.activatedAt = before.activatedAt) ∨
    ∃ event, ∃ (ready : before.config.cut.Ready event) (action : graph.Action event),
      after.config ∈ (before.config.step event ready action).support ∧
        after.clock = before.clock ∧
        after.activatedAt = State.refreshActivated after.config before.clock before.activatedAt

omit [DecidableEq Player] in
theorem GraphStep.refl (state : EventGraphRuntime.State graph) : GraphStep state state :=
  Or.inl ⟨rfl, rfl, rfl⟩

theorem graphStep_handle (runtime : EventGraphRuntime graph)
    (state next : EventGraphRuntime.State graph) (message : Message Player (Payload graph))
    (accepted : handle runtime state message = some next) : GraphStep state next := by
  obtain ⟨event, _, ready, action, member⟩ :=
    handle_config_mem_step runtime state next message accepted
  obtain ⟨clockEq, activatedEq⟩ := handle_clock_activated runtime state next message accepted
  exact Or.inr ⟨event, ready, action, member, clockEq, activatedEq⟩

theorem graphStep_includePending (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (id : MessageId Player) :
    GraphStep execution.application
      (execution.includePending (runtime.reactiveApplication leaks) id).application := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  cases found : execution.network.lookup id with
  | none => exact GraphStep.refl _
  | some message =>
      change GraphStep execution.application
        ((handle runtime execution.application ⟨message.id, message.payload.call⟩).getD
          execution.application)
      cases accepted : handle runtime execution.application ⟨message.id, message.payload.call⟩ with
      | none => exact GraphStep.refl _
      | some next => exact graphStep_handle runtime _ next _ accepted

omit [DecidableEq Player] in
theorem graphStep_executeSample (runtime : EventGraphRuntime graph)
    (state next : EventGraphRuntime.State graph) (event : graph.EventId)
    (member : next ∈ (environmentStep runtime state (.executeSample event)).support) :
    GraphStep state next := by
  obtain ⟨clockEq, effect⟩ :=
    environmentStep_executeSample_config_activated runtime state next event member
  rcases effect with ⟨configEq, activatedEq⟩ | ⟨ready, action, configMem, activatedEq⟩
  · exact Or.inl ⟨configEq, clockEq, activatedEq⟩
  · exact Or.inr ⟨event, ready, action, configMem, clockEq, activatedEq⟩

omit [DecidableEq Player] in
theorem graphStep_expire (runtime : EventGraphRuntime graph)
    (state next : EventGraphRuntime.State graph) (event : graph.EventId)
    (member : next ∈ (environmentStep runtime state (.expire event)).support) :
    GraphStep state next := by
  obtain ⟨clockEq, effect⟩ :=
    environmentStep_expire_config_activated runtime state next event member
  rcases effect with ⟨configEq, activatedEq⟩ | ⟨ready, action, configMem, activatedEq⟩
  · exact Or.inl ⟨configEq, clockEq, activatedEq⟩
  · exact Or.inr ⟨event, ready, action, configMem, clockEq, activatedEq⟩

end GraphStep

omit [DecidableEq Player] in
theorem isPrefix_succ_false {order : EventOrder} {cut : order.Cut}
    (event : Fin order.eventCount) (current : cut.IsPrefix event.val)
    (next : cut.IsPrefix (event.val + 1)) : False := by
  have completed := (next.2 event).mpr (Nat.lt_succ_self _)
  exact Nat.lt_irrefl _ ((current.2 event).mp completed)

/-- At a completed prefix, a graph step either stutters or completes exactly
the next event. -/
theorem GraphStep.prefix (setup : Setup (Player := Player) (L := L))
    {before after : EventGraphRuntime.State (graph setup)} (step : GraphStep before after)
    (event : (graph setup).EventId) (ordered : before.config.cut.IsPrefix event.val) :
    (after.config = before.config ∧ after.clock = before.clock ∧
        after.activatedAt = before.activatedAt) ∨
      (after.config.cut.IsPrefix (event.val + 1) ∧ after.clock = before.clock ∧
        after.activatedAt =
          State.refreshActivated after.config before.clock before.activatedAt) := by
  rcases step with unchanged | ⟨completed, ready, action, member, clockEq, activatedEq⟩
  · exact Or.inl unchanged
  · refine Or.inr ⟨?_, clockEq, activatedEq⟩
    have rank := (ready_iff_rank setup before.config event.val ordered completed).mp ready
    rw [before.config.step_cut completed ready action after.config member]
    exact ordered.complete_at completed ready rank

/-- Completing the current event starts its successor's clock now. -/
theorem refreshActivated_successor (setup : Setup (Player := Player) (L := L))
    {inputs : (graph setup).Inputs} {state : EventGraphRuntime.State (graph setup)}
    (invariant : state.Invariant inputs) (event : (graph setup).EventId)
    (ordered : state.config.cut.IsPrefix event.val) (config : (graph setup).Config)
    (next : (graph setup).EventId) (successor : next.val = event.val + 1) (entered : Nat)
    (activated : State.refreshActivated config state.clock state.activatedAt next = some entered) :
    entered = state.clock := by
  have ready := (ready_iff_rank setup state.config event.val ordered event).mpr rfl
  have absent := invariant.successor_not_activated event next ready successor
  unfold State.refreshActivated at activated
  split at activated
  · cases owned : (graph setup).actor? next with
    | none => simp [owned] at activated
    | some owner =>
        simp only [owned, absent, Option.orElse_none, Option.some.injEq] at activated
        exact activated.symm
  · simp at activated

/-! ## The calendar invariant -/

/-- The roster service at `offset` inside `event`'s block. Only the events
before `event` have completed, except that `event` itself may have completed
after its roster; the clock counts the block's ticks; the event's activation
time leaves at most `event.val` slots before this block; the owner's roster
activation is recorded; every recorded response saw only `event` ready, at the
block's starting clock; and a protected packet has a receipt after the
inclusion step. -/
structure RosterPhase (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (event : (graph setup).EventId) (offset : Nat)
    (control : (application setup leaks).Control) : Prop where
  position : control.execution.environmentRecall.length =
    (rosterPlanPrefix setup rosters event.val).length + offset
  inside : offset < (rosterBlock setup rosters event).length
  remaining : control.remaining + control.execution.environmentRecall.length =
    (rosterPlan setup rosters).length
  completed : control.execution.application.config.cut.IsPrefix event.val ∨
    ((rosters event).length < offset ∧
      control.execution.application.config.cut.IsPrefix (event.val + 1))
  sampled : (graph setup).actor? event = none → (rosters event).length < offset →
    control.execution.application.config.cut.IsPrefix (event.val + 1)
  clock : control.execution.application.clock =
    clockAt event.val + (offset - ((rosters event).length + 1))
  entered : control.execution.application.config.cut.IsPrefix event.val → ∀ entered,
    control.execution.application.activatedAt event = some entered →
      entered ≤ clockAt event.val ∧ clockAt event.val ≤ entered + event.val
  successor : ∀ next : (graph setup).EventId, next.val = event.val + 1 → ∀ entered,
    control.execution.application.activatedAt next = some entered → clockAt event.val ≤ entered
  opportunity : control.execution.application.config.cut.IsPrefix event.val → ∀ owner,
    (graph setup).actor? event = some owner → owner ∈ (rosters event).take offset → ∀ entered,
      control.execution.application.activatedAt event = some entered →
        OwnerActivatedSince (runtime setup) leaks control.execution.environmentRecall event
          owner entered
  responses : ∀ who, ∀ entry ∈ control.execution.recall who, ∀ ready : (graph setup).EventId,
    entry.beforeView.application.publicView.EventReady ready →
      ready.val < event.val ∨
        (ready = event ∧ entry.beforeView.application.publicView.clock = clockAt event.val)
  activation : ∀ who, control.actor = some who → 0 < offset ∧ offset ≤ (rosters event).length
  inclusion : (rosters event).length < offset →
    control.execution.application.config.cut.IsPrefix event.val → ∀ owner,
      (graph setup).actor? event = some owner →
      ∀ (earlier later : List (application setup leaks).PlayerEntry) entry message,
        control.execution.recall owner = earlier ++ entry :: later →
        entry.emitted = some message → message.sender = owner →
        message.payload.call.event? (graph setup) = some event →
        (∀ other ∈ earlier ++ later, ¬ EmitsFor (runtime setup) leaks other event) →
        ∃ accepted, (message.id, accepted) ∈ control.execution.receipts

/-- Every reachable protocol state is inside some block, or after the plan
with every event completed. -/
def RosterReach (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) :
    (application setup leaks).ProtocolState → Prop
  | none => True
  | some control => (∃ event offset, RosterPhase setup leaks rosters event offset control) ∨
      (control.remaining = 0 ∧ control.actor = none ∧
        control.execution.application.config.cut.IsPrefix (graph setup).order.eventCount)

theorem RosterPhase.ordered_of_le {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {event : (graph setup).EventId}
    {offset : Nat} {control : (application setup leaks).Control}
    (phase : RosterPhase setup leaks rosters event offset control)
    (early : offset ≤ (rosters event).length) :
    control.execution.application.config.cut.IsPrefix event.val := by
  rcases phase.completed with ordered | ⟨late, _⟩
  · exact ordered
  · omega

theorem rosterReach_initial (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (state : EventGraphRuntime.State (graph setup))
    (supported : state ∈ (initialLaw setup).support) :
    RosterReach setup leaks rosters
      (some ⟨(rosterPlan setup rosters).length, none,
        ReactiveApplication.Execution.initial (application setup leaks) state⟩) := by
  obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
  have invariant := State.initial_invariant (setup.eventInputs initial)
  have empty : (State.initial (setup.eventInputs initial)).config.cut.IsPrefix 0 :=
    EventOrder.Cut.empty_isPrefix _
  by_cases nonempty : 0 < (graph setup).order.eventCount
  · left
    refine ⟨⟨0, nonempty⟩, 0, ?_⟩
    have zeroClock : clockAt 0 = 0 := by simp [clockAt]
    exact {
      position := by simp [rosterPlanPrefix, ReactiveApplication.Execution.initial]
      inside := by rw [rosterBlock_length]; omega
      remaining := by simp [ReactiveApplication.Execution.initial]
      completed := Or.inl empty
      sampled := fun _ late => absurd late (Nat.not_lt_zero _)
      clock := by
        change 0 = clockAt 0 + _
        rw [zeroClock]
        omega
      entered := by
        intro _ entered activated
        have bound := invariant.activated_le _ entered activated
        change entered ≤ 0 at bound
        rw [zeroClock]
        omega
      successor := by
        intro _ _ entered _
        rw [zeroClock]
        exact Nat.zero_le _
      opportunity := by
        intro _ owner _ member
        simp at member
      responses := by
        intro who entry member
        simp [ReactiveApplication.Execution.initial] at member
      activation := by
        intro who active
        cases active
      inclusion := fun late => absurd late (Nat.not_lt_zero _) }
  · right
    have zero : (graph setup).order.eventCount = 0 := by omega
    refine ⟨?_, rfl, ?_⟩
    · change (rosterPlan setup rosters).length = 0
      have absent : List.finRange (graph setup).order.eventCount = [] :=
        List.eq_nil_of_length_eq_zero (by rw [List.length_finRange, zero])
      rw [rosterPlan, absent]
      rfl
    · refine ⟨le_rfl, fun event => ?_⟩
      exact absurd event.isLt (by omega)

/-- A player's response changes neither the graph, the clock, the activation
table nor the scheduler recall, and it is recorded with the current view. -/
theorem RosterPhase.respond {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {event : (graph setup).EventId}
    {offset : Nat} {control : (application setup leaks).Control}
    (phase : RosterPhase setup leaks rosters event offset control) (who : Player)
    (active : control.actor = some who) (action : (application setup leaks).Action) :
    RosterPhase setup leaks rosters event offset
      { control with
        actor := none
        execution := control.execution.respond (application setup leaks) who action } := by
  obtain ⟨configEq, publicEq⟩ :=
    (runtime setup).reactive_respond_application leaks control.execution who action
  have clockEq := congrArg PublicView.clock publicEq
  have activatedEq := congrArg PublicView.activatedAt publicEq
  dsimp only [State.publicView] at clockEq activatedEq
  have recallEq := (application setup leaks).respond_environmentRecall control.execution who action
  have receiptsEq := (application setup leaks).respond_receipts control.execution who action
  obtain ⟨_, early⟩ := phase.activation who active
  have ordered := phase.ordered_of_le early
  have startClock : control.execution.application.clock = clockAt event.val := by
    rw [phase.clock]
    omega
  exact {
    position := by
      change (control.execution.respond _ who action).environmentRecall.length = _
      rw [recallEq]
      exact phase.position
    inside := phase.inside
    remaining := by
      change control.remaining +
        (control.execution.respond _ who action).environmentRecall.length = _
      rw [recallEq]
      exact phase.remaining
    completed := by
      change (control.execution.respond _ who action).application.config.cut.IsPrefix _ ∨ _
      rw [configEq]
      exact phase.completed
    sampled := fun owned late => absurd late (by omega)
    clock := by
      change (control.execution.respond _ who action).application.clock = _
      rw [clockEq]
      exact phase.clock
    entered := by
      change (control.execution.respond _ who action).application.config.cut.IsPrefix _ → _
      rw [configEq, activatedEq]
      exact phase.entered
    successor := by
      change ∀ next : (graph setup).EventId, _ → ∀ entered,
        (control.execution.respond _ who action).application.activatedAt next = _ → _
      rw [activatedEq]
      exact phase.successor
    opportunity := by
      change (control.execution.respond _ who action).application.config.cut.IsPrefix _ → _
      rw [configEq, activatedEq, recallEq]
      exact phase.opportunity
    responses := by
      intro observer entry member ready seen
      rcases (application setup leaks).respond_entry_origin control.execution who observer
          action entry member with prior | ⟨_, fresh⟩
      · exact phase.responses observer entry prior ready seen
      · rw [fresh] at seen ⊢
        change control.execution.application.publicView.EventReady ready at seen
        have readyNow := (State.publicView_eventReady _ ready).mp seen
        have rank := (ready_iff_rank setup _ event.val ordered ready).mp readyNow
        exact Or.inr ⟨Fin.ext rank, startClock⟩
    activation := by
      intro _ none_active
      cases none_active
    inclusion := fun late => absurd late (by omega) }

/-! ## Scheduler steps -/

theorem environmentStep_recall_append {app : ReactiveApplication Player}
    (execution next : app.Execution) (command : app.Command)
    (reached : next ∈ (execution.environmentStep app command).support) :
    next.environmentRecall =
      execution.environmentRecall ++ [⟨execution.observeEnvironment app, command⟩] := by
  unfold ReactiveApplication.Execution.environmentStep at reached
  rw [PMF.support_map] at reached
  obtain ⟨updated, _, rfl⟩ := reached
  rfl

theorem ownerActivatedSince_append {graph : EventGraph Player L}
    {runtime : EventGraphRuntime graph}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
    {history : List (runtime.reactiveApplication leaks).EnvironmentEntry}
    {event : graph.EventId} {owner : Player} {entered : Nat}
    (witness : OwnerActivatedSince runtime leaks history event owner entered)
    (extra : List (runtime.reactiveApplication leaks).EnvironmentEntry) :
    OwnerActivatedSince runtime leaks (history ++ extra) event owner entered := by
  obtain ⟨entry, member, rest⟩ := witness
  exact ⟨entry, List.mem_append_left _ member, rest⟩

section Steps

variable {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {rosters : (graph setup).EventId → List Player} {event : (graph setup).EventId}
  {offset : Nat} {control : (application setup leaks).Control}

theorem RosterPhase.next_remaining
    (phase : RosterPhase setup leaks rosters event offset control) {remaining : Nat}
    (counted : control.remaining = remaining + 1) {next : (application setup leaks).Execution}
    (length : next.environmentRecall.length = control.execution.environmentRecall.length + 1) :
    remaining + next.environmentRecall.length = (rosterPlan setup rosters).length := by
  have total := phase.remaining
  rw [counted] at total
  omega

/-- A roster activation records the owner's opportunity while the event is
ready. -/
theorem RosterPhase.activate_step
    (phase : RosterPhase setup leaks rosters event offset control)
    (early : offset < (rosters event).length) (who : Player)
    (chosen : (rosters event)[offset]? = some who) (remaining : Nat)
    (counted : control.remaining = remaining + 1)
    (next : (application setup leaks).Execution)
    (reached : next ∈ (control.execution.environmentStep (application setup leaks)
      (.activate who)).support) :
    RosterPhase setup leaks rosters event (offset + 1) ⟨remaining, some who, next⟩ := by
  have appended := environmentStep_recall_append control.execution next _ reached
  have recallEq := (application setup leaks).environmentStep_recall control.execution next _ reached
  have applicationEq : next.application = control.execution.application := by
    obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
    obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
    rfl
  have ordered := phase.ordered_of_le early.le
  have length : next.environmentRecall.length =
      control.execution.environmentRecall.length + 1 := by
    rw [appended, List.length_append, List.length_singleton]
  have blockLength := rosterBlock_length setup rosters event
  exact {
    position := by
      change next.environmentRecall.length = _
      rw [length, phase.position]
      omega
    inside := by
      rw [blockLength]
      omega
    remaining := phase.next_remaining counted length
    completed := by
      change next.application.config.cut.IsPrefix _ ∨ _
      rw [applicationEq]
      exact Or.inl ordered
    sampled := fun _ late => absurd late (by omega)
    clock := by
      change next.application.clock = _
      rw [applicationEq, phase.clock]
      omega
    entered := by
      change next.application.config.cut.IsPrefix _ → ∀ entered,
        next.application.activatedAt event = _ → _
      rw [applicationEq]
      exact phase.entered
    successor := by
      change ∀ later : (graph setup).EventId, _ → ∀ entered,
        next.application.activatedAt later = _ → _
      rw [applicationEq]
      exact phase.successor
    opportunity := by
      intro _ owner owned member entered activated
      change next.application.activatedAt event = some entered at activated
      rw [applicationEq] at activated
      change OwnerActivatedSince (runtime setup) leaks next.environmentRecall event owner entered
      rw [appended]
      rw [List.take_add_one, chosen] at member
      rcases List.mem_append.mp member with prior | current
      · exact ownerActivatedSince_append
          (phase.opportunity ordered owner owned prior entered activated) _
      · have same : owner = who := by simpa using current
        subst owner
        refine ⟨⟨control.execution.observeEnvironment _, .activate who⟩,
          List.mem_append_right _ (List.mem_singleton_self _), rfl, activated, ?_⟩
        exact (State.publicView_eventReady _ event).mpr
          ((ready_iff_rank setup _ event.val ordered event).mpr rfl)
    responses := by
      change ∀ observer, ∀ entry ∈ next.recall observer, _
      rw [recallEq]
      exact phase.responses
    activation := fun _ _ => ⟨Nat.succ_pos _, early⟩
    inclusion := fun late => absurd late (by omega) }

/-- Protected inclusion at the end of the roster. Whatever packet is included,
only the ready event can complete; an owner's sole authored packet for it gets
a receipt. -/
theorem RosterPhase.include_step
    (phase : RosterPhase setup leaks rosters event offset control)
    (atInclusion : offset = (rosters event).length) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    {inputs : (graph setup).Inputs} (invariant : control.execution.application.Invariant inputs)
    (origins : control.execution.Provenance (application setup leaks))
    (recalled : control.execution.InputRecall (application setup leaks))
    (retained : control.execution.network.PendingOrPublished)
    (sound : control.execution.ReceiptsSound (application setup leaks) (fun _ => True))
    (remaining : Nat) (counted : control.remaining = remaining + 1)
    (command : (application setup leaks).Command)
    (selected : command = (runtime setup).reactiveLatest leaks event owner
      (control.execution.observeEnvironment (application setup leaks)))
    (next : (application setup leaks).Execution)
    (reached : next ∈ (control.execution.environmentStep (application setup leaks)
      command).support) :
    RosterPhase setup leaks rosters event (offset + 1)
      ⟨remaining, command.actor? (application setup leaks), next⟩ := by
  have appended := environmentStep_recall_append control.execution next _ reached
  have recallEq := (application setup leaks).environmentStep_recall control.execution next _ reached
  have receiptsPrefix := (application setup leaks).environmentStep_receipts_prefix
    control.execution next _ reached
  have commandCases : command = .wait ∨ ∃ id, command = .include id := by
    rw [selected]
    unfold reactiveLatest
    split
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  have actorNone : command.actor? (application setup leaks) = none := by
    rcases commandCases with rfl | ⟨id, rfl⟩ <;> rfl
  have step : GraphStep control.execution.application next.application := by
    rcases commandCases with rfl | ⟨id, rfl⟩
    · simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact GraphStep.refl _
    · simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact graphStep_includePending (runtime setup) leaks control.execution id
  have ordered := phase.ordered_of_le atInclusion.le
  have outcome := step.prefix setup event ordered
  have length : next.environmentRecall.length =
      control.execution.environmentRecall.length + 1 := by
    rw [appended, List.length_append, List.length_singleton]
  have blockLength := rosterBlock_length setup rosters event
  have clockEq : next.application.clock = control.execution.application.clock := by
    rcases outcome with ⟨_, same, _⟩ | ⟨_, same, _⟩ <;> exact same
  exact {
    position := by
      change next.environmentRecall.length = _
      rw [length, phase.position]
      omega
    inside := by
      rw [blockLength]
      omega
    remaining := phase.next_remaining counted length
    completed := by
      change next.application.config.cut.IsPrefix _ ∨ _
      rcases outcome with ⟨configEq, _, _⟩ | ⟨completed, _, _⟩
      · rw [configEq]
        exact Or.inl ordered
      · exact Or.inr ⟨by omega, completed⟩
    sampled := fun absent => by rw [owned] at absent; cases absent
    clock := by
      change next.application.clock = _
      rw [clockEq, phase.clock]
      omega
    entered := by
      intro current entered activated
      change next.application.config.cut.IsPrefix _ at current
      change next.application.activatedAt event = some entered at activated
      rcases outcome with ⟨_, _, activatedEq⟩ | ⟨completed, _, _⟩
      · rw [activatedEq] at activated
        exact phase.entered ordered entered activated
      · exact (isPrefix_succ_false event current completed).elim
    successor := by
      intro later rank entered activated
      change next.application.activatedAt later = some entered at activated
      rcases outcome with ⟨_, _, activatedEq⟩ | ⟨_, _, activatedEq⟩
      · rw [activatedEq] at activated
        exact phase.successor later rank entered activated
      · rw [activatedEq] at activated
        have now := refreshActivated_successor setup invariant event ordered _ later rank
          entered activated
        rw [now, phase.clock]
        omega
    opportunity := by
      intro current someone owns member entered activated
      change next.application.config.cut.IsPrefix _ at current
      change next.application.activatedAt event = some entered at activated
      change OwnerActivatedSince (runtime setup) leaks next.environmentRecall event someone entered
      rcases outcome with ⟨_, _, activatedEq⟩ | ⟨completed, _, _⟩
      · rw [activatedEq] at activated
        rw [appended]
        have full : (rosters event).take (offset + 1) = (rosters event).take offset := by
          rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
        rw [full] at member
        exact ownerActivatedSince_append
          (phase.opportunity ordered someone owns member entered activated) _
      · exact (isPrefix_succ_false event current completed).elim
    responses := by
      change ∀ observer, ∀ entry ∈ next.recall observer, _
      rw [recallEq]
      exact phase.responses
    activation := by
      intro who active
      change command.actor? (application setup leaks) = some who at active
      rw [actorNone] at active
      cases active
    inclusion := by
      intro _ _ someone owns earlier later entry message split emitted authored addressed sole
      have same : someone = owner := Option.some.inj (owns.symm.trans owned)
      rw [same] at split authored
      change next.recall owner = _ at split
      rw [recallEq] at split
      change ∃ accepted, (message.id, accepted) ∈ next.receipts
      by_cases published : message.id ∈ control.execution.network.ledger.map Message.id
      · obtain ⟨accepted, member⟩ := receipt_of_published control.execution sound _ published
        exact ⟨accepted, receiptsPrefix.subset member⟩
      · obtain ⟨pending, latest⟩ := reactiveLatest_sole (runtime setup) leaks control.execution
          origins recalled retained event owner earlier later entry message split emitted
          authored addressed sole published
        have included : command = .include message.id := selected.trans latest
        rw [included] at reached
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact includePending_receipt_of_pending (runtime setup) leaks control.execution message
          pending }

end Steps

/-! ## Sampling and expiry complete the event -/

omit [DecidableEq Player] in
/-- Sampling a ready actorless event performs its graph step. -/
theorem executeSample_completes {graph : EventGraph Player L} (runtime : EventGraphRuntime graph)
    (state next : EventGraphRuntime.State graph) (event : graph.EventId)
    (actorless : graph.actor? event = none) (ready : state.config.cut.Ready event)
    (member : next ∈ (environmentStep runtime state (.executeSample event)).support) :
    next.config.cut = state.config.cut.complete event ready ∧ next.clock = state.clock ∧
      next.activatedAt = State.refreshActivated next.config state.clock state.activatedAt := by
  cases view : nodeView graph event with
  | bind owner payload outputEq codeEq =>
      rw [nodeView_bind_actor outputEq codeEq] at actorless
      cases actorless
  | resolve owner payload binding checks outputEq codeEq =>
      rw [nodeView_resolve_actor outputEq codeEq] at actorless
      cases actorless
  | sample payload law outputEq codeEq =>
      rw [environmentStep_executeSample_eq runtime state event ready payload law outputEq codeEq
        view, PMF.support_map] at member
      obtain ⟨config, configMem, rfl⟩ := member
      exact ⟨state.config.step_cut event ready _ config configMem, rfl, rfl⟩

omit [DecidableEq Player] in
/-- Expiring a ready owned event once its deadline is due completes it. -/
theorem expire_completes {graph : EventGraph Player L} (runtime : EventGraphRuntime graph)
    (state next : EventGraphRuntime.State graph) (event : graph.EventId) (owner : Player)
    (owned : graph.actor? event = some owner) (ready : state.config.cut.Ready event)
    (entered : Nat) (activated : state.activatedAt event = some entered)
    (due : runtime.deadline event ≤ state.clock - entered)
    (member : next ∈ (environmentStep runtime state (.expire event)).support) :
    next.config.cut = state.config.cut.complete event ready ∧ next.clock = state.clock ∧
      next.activatedAt = State.refreshActivated next.config state.clock state.activatedAt := by
  cases view : nodeView graph event with
  | sample payload law outputEq codeEq =>
      rw [nodeView_sample_actor outputEq codeEq] at owned
      cases owned
  | bind actor payload outputEq codeEq =>
      rw [environmentStep_expire_bind_eq runtime state event ready entered activated due actor
        payload outputEq codeEq view, PMF.mem_support_pure_iff] at member
      subst next
      exact ⟨rfl, rfl, rfl⟩
  | resolve actor payload binding checks outputEq codeEq =>
      rw [environmentStep_expire_resolve_eq runtime state event ready entered activated due actor
        payload binding checks outputEq codeEq view, PMF.mem_support_pure_iff] at member
      subst next
      exact ⟨rfl, rfl, rfl⟩

theorem applicationStep_facts {graph : EventGraph Player L} {runtime : EventGraphRuntime graph}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : EnvironmentCommand graph)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      (.application command)).support) :
    next.application ∈ (environmentStep runtime execution.application command).support ∧
      next.receipts = execution.receipts := by
  obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
  obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
  exact ⟨changed, rfl⟩

section Completion

variable {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {rosters : (graph setup).EventId → List Player} {event : (graph setup).EventId}
  {offset : Nat} {control : (application setup leaks).Control}

/-- Sampling at the end of an actorless event's roster completes it. -/
theorem RosterPhase.sample_step
    (phase : RosterPhase setup leaks rosters event offset control)
    (atInclusion : offset = (rosters event).length)
    (actorless : (graph setup).actor? event = none)
    {inputs : (graph setup).Inputs} (invariant : control.execution.application.Invariant inputs)
    (remaining : Nat) (counted : control.remaining = remaining + 1)
    (next : (application setup leaks).Execution)
    (reached : next ∈ (control.execution.environmentStep (application setup leaks)
      (.application (.executeSample event))).support) :
    RosterPhase setup leaks rosters event (offset + 1) ⟨remaining, none, next⟩ := by
  have appended := environmentStep_recall_append control.execution next _ reached
  have recallEq := (application setup leaks).environmentStep_recall control.execution next _ reached
  obtain ⟨member, receiptsEq⟩ := applicationStep_facts control.execution next _ reached
  have ordered := phase.ordered_of_le atInclusion.le
  have ready := (ready_iff_rank setup _ event.val ordered event).mpr rfl
  obtain ⟨cutEq, clockEq, activatedEq⟩ := executeSample_completes (runtime setup)
    control.execution.application next.application event actorless ready member
  have completed : next.application.config.cut.IsPrefix (event.val + 1) := by
    rw [cutEq]
    exact ordered.complete_at event ready rfl
  have length : next.environmentRecall.length =
      control.execution.environmentRecall.length + 1 := by
    rw [appended, List.length_append, List.length_singleton]
  have blockLength := rosterBlock_length setup rosters event
  exact {
    position := by
      change next.environmentRecall.length = _
      rw [length, phase.position]
      omega
    inside := by
      rw [blockLength]
      omega
    remaining := phase.next_remaining counted length
    completed := Or.inr ⟨by omega, completed⟩
    sampled := fun _ _ => completed
    clock := by
      change next.application.clock = _
      rw [clockEq, phase.clock]
      omega
    entered := fun current => (isPrefix_succ_false event current completed).elim
    successor := by
      intro later rank entered activated
      change next.application.activatedAt later = some entered at activated
      rw [activatedEq] at activated
      have now := refreshActivated_successor setup invariant event ordered _ later rank
        entered activated
      rw [now, phase.clock]
      omega
    opportunity := fun current => (isPrefix_succ_false event current completed).elim
    responses := by
      change ∀ observer, ∀ entry ∈ next.recall observer, _
      rw [recallEq]
      exact phase.responses
    activation := fun _ active => by cases active
    inclusion := fun _ _ owner owned => by rw [actorless] at owned; cases owned }

/-- A clock tick after the inclusion step. -/
theorem RosterPhase.tick_step
    (phase : RosterPhase setup leaks rosters event offset control)
    (late : (rosters event).length < offset)
    (ticking : offset < (rosters event).length + event.val + 2)
    (remaining : Nat) (counted : control.remaining = remaining + 1)
    (next : (application setup leaks).Execution)
    (reached : next ∈ (control.execution.environmentStep (application setup leaks)
      (.application .advanceClock)).support) :
    RosterPhase setup leaks rosters event (offset + 1) ⟨remaining, none, next⟩ := by
  have appended := environmentStep_recall_append control.execution next _ reached
  have recallEq := (application setup leaks).environmentStep_recall control.execution next _ reached
  obtain ⟨member, receiptsEq⟩ := applicationStep_facts control.execution next _ reached
  simp only [environmentStep, PMF.mem_support_pure_iff] at member
  have length : next.environmentRecall.length =
      control.execution.environmentRecall.length + 1 := by
    rw [appended, List.length_append, List.length_singleton]
  have blockLength := rosterBlock_length setup rosters event
  have full : (rosters event).take (offset + 1) = (rosters event).take offset := by
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  exact {
    position := by
      change next.environmentRecall.length = _
      rw [length, phase.position]
      omega
    inside := by
      rw [blockLength]
      omega
    remaining := phase.next_remaining counted length
    completed := by
      change next.application.config.cut.IsPrefix _ ∨ _
      rw [member]
      rcases phase.completed with ordered | ⟨_, completed⟩
      · exact Or.inl ordered
      · exact Or.inr ⟨by omega, completed⟩
    sampled := by
      intro actorless _
      change next.application.config.cut.IsPrefix _
      rw [member]
      exact phase.sampled actorless late
    clock := by
      change next.application.clock = _
      rw [member]
      change control.execution.application.clock + 1 = _
      rw [phase.clock]
      omega
    entered := by
      change next.application.config.cut.IsPrefix _ → ∀ entered,
        next.application.activatedAt event = _ → _
      rw [member]
      exact phase.entered
    successor := by
      change ∀ later : (graph setup).EventId, _ → ∀ entered,
        next.application.activatedAt later = _ → _
      rw [member]
      exact phase.successor
    opportunity := by
      change next.application.config.cut.IsPrefix _ → ∀ owner, _ → owner ∈ _ → ∀ entered,
        next.application.activatedAt event = _ →
          OwnerActivatedSince (runtime setup) leaks next.environmentRecall event owner entered
      rw [member, appended, full]
      intro ordered owner owned inside entered activated
      exact ownerActivatedSince_append
        (phase.opportunity ordered owner owned inside entered activated) _
    responses := by
      change ∀ observer, ∀ entry ∈ next.recall observer, _
      rw [recallEq]
      exact phase.responses
    activation := fun _ active => by cases active
    inclusion := by
      intro _ current owner owned earlier later entry message split
      change next.application.config.cut.IsPrefix _ at current
      change next.recall owner = _ at split
      rw [member] at current
      rw [recallEq] at split
      change _ → _ → _ → _ → ∃ accepted, (message.id, accepted) ∈ next.receipts
      rw [receiptsEq]
      exact phase.inclusion late current owner owned earlier later entry message split }

/-- Expiry ends the block. Every owned event still ready is due and completes,
so the next block starts with exactly the earlier events completed. -/
theorem RosterPhase.expire_step
    (phase : RosterPhase setup leaks rosters event offset control)
    (atExpiry : offset = (rosters event).length + event.val + 2)
    {inputs : (graph setup).Inputs} (invariant : control.execution.application.Invariant inputs)
    (remaining : Nat) (counted : control.remaining = remaining + 1)
    (next : (application setup leaks).Execution)
    (reached : next ∈ (control.execution.environmentStep (application setup leaks)
      (.application (.expire event))).support) :
    RosterReach setup leaks rosters (some ⟨remaining, none, next⟩) := by
  have appended := environmentStep_recall_append control.execution next _ reached
  have recallEq := (application setup leaks).environmentStep_recall control.execution next _ reached
  obtain ⟨member, _⟩ := applicationStep_facts control.execution next _ reached
  have nextInvariant := environmentStep_invariant (runtime setup) _ _ _ invariant member
  have length : next.environmentRecall.length =
      control.execution.environmentRecall.length + 1 := by
    rw [appended, List.length_append, List.length_singleton]
  have blockLength := rosterBlock_length setup rosters event
  have endClock : control.execution.application.clock = clockAt event.val + (event.val + 1) := by
    rw [phase.clock]
    omega
  -- After expiry the event has completed, the clock is unchanged, and the
  -- successor's activation time is no earlier than the block's start.
  obtain ⟨completed, clockEq, successor⟩ :
      next.application.config.cut.IsPrefix (event.val + 1) ∧
        next.application.clock = control.execution.application.clock ∧
        ∀ later : (graph setup).EventId, later.val = event.val + 1 → ∀ entered,
          next.application.activatedAt later = some entered → clockAt event.val ≤ entered := by
    rcases phase.completed with ordered | ⟨_, done⟩
    · cases owned : (graph setup).actor? event with
      | none => exact (isPrefix_succ_false event ordered (phase.sampled owned (by omega))).elim
      | some owner =>
          have ready := (ready_iff_rank setup _ event.val ordered event).mpr rfl
          obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor event ready
            (by rw [owned]; rfl)
          have bounds := phase.entered ordered entered activated
          have due : (runtime setup).deadline event ≤
              control.execution.application.clock - entered := by
            change event.val + 1 ≤ _
            omega
          obtain ⟨cutEq, clockEq, activatedEq⟩ := expire_completes (runtime setup)
            control.execution.application next.application event owner owned ready entered
            activated due member
          refine ⟨?_, clockEq, ?_⟩
          · rw [cutEq]
            exact ordered.complete_at event ready rfl
          · intro later rank laterEntered laterActivated
            rw [activatedEq] at laterActivated
            have now := refreshActivated_successor setup invariant event ordered _ later rank
              laterEntered laterActivated
            rw [now, endClock]
            omega
    · have unready : ¬ control.execution.application.config.cut.Ready event := fun ready =>
        ready.1 ((done.2 event).mpr (Nat.lt_succ_self _))
      rw [environmentStep_expire_of_not_ready (runtime setup) _ event unready,
        PMF.mem_support_pure_iff] at member
      rw [member]
      exact ⟨done, rfl, phase.successor⟩
  have position : next.environmentRecall.length =
      (rosterPlanPrefix setup rosters (event.val + 1)).length := by
    rw [length, phase.position, rosterPlanPrefix_succ, List.length_append, blockLength]
    omega
  have total : remaining + next.environmentRecall.length = (rosterPlan setup rosters).length :=
    phase.next_remaining counted length
  by_cases more : event.val + 1 < (graph setup).order.eventCount
  · left
    let following : (graph setup).EventId := ⟨event.val + 1, more⟩
    have startClock : next.application.clock = clockAt following.val := by
      rw [clockEq, endClock]
      exact (clockAt_succ event.val).symm
    refine ⟨following, 0, ?_⟩
    exact {
      position := by
        change next.environmentRecall.length = _
        rw [position]
        rfl
      inside := by
        rw [rosterBlock_length]
        omega
      remaining := total
      completed := Or.inl completed
      sampled := fun _ late => absurd late (Nat.not_lt_zero _)
      clock := by
        change next.application.clock = _
        rw [startClock]
        omega
      entered := by
        intro _ entered activated
        change next.application.activatedAt following = some entered at activated
        have lower := successor following rfl entered activated
        have upper := nextInvariant.activated_le following entered activated
        rw [startClock] at upper
        refine ⟨upper, ?_⟩
        change clockAt (event.val + 1) ≤ entered + (event.val + 1)
        rw [clockAt_succ]
        omega
      successor := by
        intro later rank entered activated
        change next.application.activatedAt later = some entered at activated
        have laterReady := ((nextInvariant.activated_iff later).mp
          (by rw [activated]; rfl)).1
        have laterRank := (ready_iff_rank setup _ (event.val + 1) completed later).mp laterReady
        change later.val = event.val + 1 + 1 at rank
        omega
      opportunity := by
        intro _ owner _ inside
        simp at inside
      responses := by
        intro observer entry inside ready seen
        change entry ∈ next.recall observer at inside
        rw [recallEq] at inside
        rcases phase.responses observer entry inside ready seen with before | ⟨same, _⟩
        · exact Or.inl (by change ready.val < event.val + 1; omega)
        · exact Or.inl (by rw [same]; change event.val < event.val + 1; omega)
      activation := fun _ active => by cases active
      inclusion := fun late => absurd late (Nat.not_lt_zero _) }
  · right
    have last : event.val + 1 = (graph setup).order.eventCount := by
      have := event.isLt
      omega
    refine ⟨?_, rfl, ?_⟩
    · change remaining = 0
      have whole : rosterPlanPrefix setup rosters (event.val + 1) = rosterPlan setup rosters := by
        rw [last]
        exact rosterPlanPrefix_eventCount setup rosters
      rw [position, whole] at total
      omega
    · refine ⟨le_rfl, fun query => ?_⟩
      rw [completed.2 query]
      have := query.isLt
      omega

/-- Every scheduler command of the roster plan preserves the calendar invariant,
for arbitrary network policies. -/
theorem RosterPhase.environment
    (network : (runtime setup).NetworkPolicy leaks)
    (phase : RosterPhase setup leaks rosters event offset control)
    {inputs : (graph setup).Inputs} (invariant : control.execution.application.Invariant inputs)
    (origins : control.execution.Provenance (application setup leaks))
    (recalled : control.execution.InputRecall (application setup leaks))
    (retained : control.execution.network.PendingOrPublished)
    (sound : control.execution.ReceiptsSound (application setup leaks) (fun _ => True))
    (remaining : Nat) (counted : control.remaining = remaining + 1)
    (command : (application setup leaks).Command)
    (selected : command ∈ (rosterScheduler setup leaks rosters network
      control.execution.environmentRecall
        (control.execution.observeEnvironment (application setup leaks))).support)
    (next : (application setup leaks).Execution)
    (reached : next ∈ (control.execution.environmentStep (application setup leaks)
      command).support) :
    RosterReach setup leaks rosters
      (some ⟨remaining, command.actor? (application setup leaks), next⟩) := by
  have found : (rosterPlan setup rosters)[control.execution.environmentRecall.length]? =
      (rosterBlock setup rosters event)[offset]? := by
    rw [phase.position]
    exact rosterPlan_getElem_block setup rosters event offset phase.inside
  unfold rosterScheduler at selected
  rw [found] at selected
  have blockLength := rosterBlock_length setup rosters event
  have inside := phase.inside
  rw [blockLength] at inside
  rcases (by omega : offset < (rosters event).length ∨ offset = (rosters event).length ∨
      ((rosters event).length < offset ∧ offset < (rosters event).length + event.val + 2) ∨
      offset = (rosters event).length + event.val + 2) with
    early | atInclusion | ⟨late, ticking⟩ | atExpiry
  · rw [rosterBlock_roster setup rosters event offset early] at selected
    simp only [interactionInstruction, PMF.mem_support_pure_iff] at selected
    subst command
    exact Or.inl ⟨event, offset + 1, phase.activate_step early _
      (List.getElem?_eq_getElem early) remaining counted next reached⟩
  · have atEnd := rosterBlock_ending setup rosters event 0
    rw [rosterPhaseEnding_first, Nat.add_zero, ← atInclusion] at atEnd
    rw [atEnd] at selected
    cases owned : (graph setup).actor? event with
    | none =>
        rw [owned] at selected
        simp only [interactionInstruction, PMF.mem_support_pure_iff] at selected
        subst command
        exact Or.inl ⟨event, offset + 1, phase.sample_step atInclusion owned invariant remaining
          counted next reached⟩
    | some owner =>
        rw [owned] at selected
        simp only [interactionInstruction, PMF.mem_support_pure_iff] at selected
        exact Or.inl ⟨event, offset + 1, phase.include_step atInclusion owner owned invariant
          origins recalled retained sound remaining counted command selected next reached⟩
  · have atTick := rosterBlock_ending setup rosters event (offset - (rosters event).length - 1 + 1)
    rw [rosterPhaseEnding_tick setup event _ (by omega),
      show (rosters event).length + (offset - (rosters event).length - 1 + 1) = offset by omega]
      at atTick
    rw [atTick] at selected
    simp only [interactionInstruction, PMF.mem_support_pure_iff] at selected
    subst command
    exact Or.inl ⟨event, offset + 1, phase.tick_step late ticking remaining counted next reached⟩
  · have atEnd := rosterBlock_ending setup rosters event (event.val + 2)
    rw [rosterPhaseEnding_expire,
      show (rosters event).length + (event.val + 2) = offset by omega] at atEnd
    rw [atEnd] at selected
    simp only [interactionInstruction, PMF.mem_support_pure_iff] at selected
    subst command
    exact phase.expire_step atExpiry invariant remaining counted next reached

end Completion

/-! ## Every legal history -/

theorem rosterReach_transition (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (before after : (application setup leaks).ProtocolState)
    (prior : ((application setup leaks).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        before)
    (valid : RosterReach setup leaks rosters before)
    (joint : Player → Option (application setup leaks).Action)
    (reached : after ∈ ((application setup leaks).transition (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) before
        joint).support) :
    RosterReach setup leaks rosters after := by
  cases before with
  | none =>
      obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
      exact rosterReach_initial setup leaks rosters state supported
  | some control =>
      obtain ⟨⟨inputs, invariant⟩, origins, recalled, retained, sound⟩ :=
        roster_trace_facts setup leaks _ _ prior
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          rcases valid with ⟨event, offset, phase⟩ | ⟨_, idle, _⟩
          · exact Or.inl ⟨event, offset, phase.respond who rfl _⟩
          · cases idle
      | none =>
          cases remaining with
          | zero =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact valid
          | succ remaining =>
              obtain ⟨command, selected, moved⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
              rcases valid with ⟨event, offset, phase⟩ | ⟨done, _, _⟩
              · exact phase.environment network invariant origins recalled retained sound
                  remaining rfl command selected next supported
              · cases done

/-- The calendar invariant holds at every legal history of the roster
service, including histories where players deviate arbitrarily. -/
theorem rosterReach_history (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks) :
    ∀ {state} (_trace : ((application setup leaks).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        state), RosterReach setup leaks rosters state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      rosterReach_transition setup leaks rosters network _ _ prior
        (rosterReach_history setup leaks rosters network prior) joint reached

/-! ## The asynchronous contract -/

/-- **The fixed roster calendar is an asynchronous service.** An owner is
activated within `event.val` slots of its event becoming ready, its sole
authored packet is included in the slot it was sent, and the plan completes
every event. The roster must give each event's actor an activation. -/
theorem rosterScheduler_asyncContract (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (opportunities : ActorOpportunities setup rosters) :
    AsyncContract (runtime setup) leaks (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) (fun event => event.val) (fun _ => 0) where
  opportunity := by
    intro control trace event owner entered owned readyView activated late
    dsimp only at late
    have ready := (State.publicView_eventReady _ event).mp readyView
    rcases rosterReach_history setup leaks rosters network trace with
      ⟨current, offset, phase⟩ | ⟨_, _, done⟩
    · have blockLength := rosterBlock_length setup rosters current
      have inside := phase.inside
      rw [blockLength] at inside
      rcases phase.completed with ordered | ⟨_, completed⟩
      · have same : event = current :=
          Fin.ext ((ready_iff_rank setup _ current.val ordered event).mp ready)
        subst same
        by_cases early : offset ≤ (rosters event).length
        · have bounds := phase.entered ordered entered activated
          have clockEq := phase.clock
          omega
        · have member : owner ∈ (rosters event).take offset := by
            rw [List.take_of_length_le (by omega)]
            exact opportunities event owner owned
          exact phase.opportunity ordered owner owned member entered activated
      · have rank := (ready_iff_rank setup _ (current.val + 1) completed event).mp ready
        have lower := phase.successor event rank entered activated
        have clockEq := phase.clock
        have tickBound : offset - ((rosters current).length + 1) ≤ current.val + 1 := by omega
        omega
    · exact (ready.1 ((done.2 event).mpr event.isLt)).elim
  inclusion := by
    intro control trace event owner owned earlier later entry message split emitted authored
      addressed seen sole unfinished late
    dsimp only at late
    rcases rosterReach_history setup leaks rosters network trace with
      ⟨current, offset, phase⟩ | ⟨_, _, done⟩
    · have member : entry ∈ control.execution.recall owner := by
        rw [split]
        simp
      have finishedBefore : ∀ query : (graph setup).EventId, query.val < current.val →
          query ∈ control.execution.application.config.cut.completed := by
        intro query before
        rcases phase.completed with ordered | ⟨_, completed⟩
        · exact (ordered.2 query).mpr before
        · exact (completed.2 query).mpr (by omega)
      rcases phase.responses owner entry member event seen with before | ⟨same, sent⟩
      · exact (unfinished (finishedBefore event before)).elim
      · subst same
        by_cases early : offset ≤ (rosters event).length
        · have clockEq := phase.clock
          omega
        · rcases phase.completed with ordered | ⟨_, completed⟩
          · exact phase.inclusion (by omega) ordered owner owned earlier later entry message
              split emitted authored addressed sole
          · exact (unfinished ((completed.2 event).mpr (Nat.lt_succ_self _))).elim
    · exact (unfinished ((done.2 event).mpr event.isLt)).elim
  completes := by
    intro control trace terminal
    obtain ⟨finished, _⟩ := terminal
    rcases rosterReach_history setup leaks rosters network trace with
      ⟨current, offset, phase⟩ | ⟨_, _, done⟩
    · have total := phase.remaining
      have bound := rosterPlan_length_block setup rosters current
      have inside := phase.inside
      rw [phase.position, finished] at total
      omega
    · exact done.terminal

/-- The roster calendar's bounds fit every deadline: `event.val + 0` slots
before inclusion, against a deadline of `event.val + 1`. -/
theorem rosterScheduler_asyncTimely (setup : Setup (Player := Player) (L := L)) :
    AsyncTimely (runtime setup) (fun event => event.val) (fun _ => 0) := by
  intro event _
  change event.val + 0 < event.val + 1
  omega

end Vegas
