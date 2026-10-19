/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochBindingCoupling
import Vegas.Pending.EventValueSwap
import Vegas.Pending.ReactiveEventStability

/-! # Native owner frames for matching opaque commitment batches -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

section

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

structure BindingFrame (owner : Player) (left right : State graph) : Prop where
  inputs : left.config.inputs = right.config.inputs
  publicOutputs : ∀ event, ((graph).outputLayout event).IsPublic →
    left.config.outputs event = right.config.outputs event
  ownerOutputs : ∀ event payload, (graph).outputLayout event = .binding owner payload →
    left.config.outputs event = right.config.outputs event
  ownHistory : (graph).ownCompletions owner left.config.history =
    (graph).ownCompletions owner right.config.history
  accepted : ∀ event payload, (graph).outputLayout event = .binding owner payload →
    left.accepted (.inr event) = right.accepted (.inr event)
  candidates : ∀ slot, left.candidates.lookup (owner, slot) = right.candidates.lookup (owner, slot)
  unused : ∀ candidate, candidate.1 = owner →
    (left.HandleUnused candidate ↔ right.HandleUnused candidate)
  activated : ∀ event payload, (graph).outputLayout event = .binding owner payload →
    left.activatedAt event = right.activatedAt event
  clock : left.clock = right.clock

end

namespace BindingFrame

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  {program : SourceProgram Player L Γ O} {owner : Player}

local notation "ownerGraph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

theorem refl (owner : Player) (state : State ownerGraph) :
    BindingFrame program owner state state where
  inputs := rfl
  publicOutputs := fun _ _ => rfl
  ownerOutputs := fun _ _ _ => rfl
  ownHistory := rfl
  accepted := fun _ _ _ => rfl
  candidates := fun _ => rfl
  unused := fun _ _ => Iff.rfl
  activated := fun _ _ _ => rfl
  clock := rfl

theorem symm {left right : State ownerGraph} (frame : BindingFrame program owner left right) :
    BindingFrame program owner right left where
  inputs := frame.inputs.symm
  publicOutputs := fun event visible => (frame.publicOutputs event visible).symm
  ownerOutputs := fun event payload binding => (frame.ownerOutputs event payload binding).symm
  ownHistory := frame.ownHistory.symm
  accepted := fun event payload binding => (frame.accepted event payload binding).symm
  candidates := fun slot => (frame.candidates slot).symm
  unused := fun candidate owned => (frame.unused candidate owned).symm
  activated := fun event payload binding => (frame.activated event payload binding).symm
  clock := frame.clock.symm

theorem trans {left right last : State ownerGraph} (first : BindingFrame program owner left right)
    (second : BindingFrame program owner right last) : BindingFrame program owner left last where
  inputs := first.inputs.trans second.inputs
  publicOutputs := fun event visible =>
    (first.publicOutputs event visible).trans (second.publicOutputs event visible)
  ownerOutputs := fun event payload binding =>
    (first.ownerOutputs event payload binding).trans (second.ownerOutputs event payload binding)
  ownHistory := first.ownHistory.trans second.ownHistory
  accepted := fun event payload binding =>
    (first.accepted event payload binding).trans (second.accepted event payload binding)
  candidates := fun slot => (first.candidates slot).trans (second.candidates slot)
  unused := fun candidate owned =>
    (first.unused candidate owned).trans (second.unused candidate owned)
  activated := fun event payload binding =>
    (first.activated event payload binding).trans (second.activated event payload binding)
  clock := first.clock.trans second.clock

theorem completed {left right : State ownerGraph} (frame : BindingFrame program owner left right)
    (payload : L.Ty)
    (event : (ownerGraph).EventId)
    (cone : ((ownerGraph).outputLayout event).IsPublic ∨
      ((ownerGraph).outputLayout event).SameBindingOwner (.binding owner payload)) :
    event ∈ left.config.cut.completed ↔ event ∈ right.config.cut.completed := by
  have outputs : left.config.outputs event = right.config.outputs event := by
    rcases cone with visible | owned
    · exact frame.publicOutputs event visible
    · have typed : ∃ sort, (ownerGraph).outputLayout event = .binding owner sort := by
        cases kind : (ownerGraph).outputLayout event with
        | binding who sort =>
            have same : who = owner := by
              simpa only [kind, EventField.SameBindingOwner] using owned
            subst who
            exact ⟨sort, rfl⟩
        | publicData | publication | privateInput =>
            simp only [kind, EventField.SameBindingOwner] at owned
      obtain ⟨sort, typed⟩ := typed
      exact frame.ownerOutputs event sort typed
  rw [← left.config.output_available event, ← right.config.output_available event, outputs]

theorem ready {left right : State ownerGraph} (frame : BindingFrame program owner left right)
    (event : (ownerGraph).EventId)
    (payload : L.Ty) (binding : (ownerGraph).outputLayout event = .binding owner payload) :
    left.config.cut.Ready event ↔ right.config.cut.Ready event :=
  binding_ready_congr program left.config.cut right.config.cut event owner payload binding
    (fun prior cone => frame.completed payload prior cone)

theorem withinDeadline {left right : State ownerGraph}
    (frame : BindingFrame program owner left right)
    (runtime : EventGraphRuntime ownerGraph) (event : (ownerGraph).EventId) (payload : L.Ty)
    (binding : (ownerGraph).outputLayout event = .binding owner payload) :
    left.WithinDeadline runtime event ↔ right.WithinDeadline runtime event := by
  unfold State.WithinDeadline
  rw [frame.clock, frame.activated event payload binding]

end BindingFrame

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

local notation "graph" =>
  EventGraph.withMode (toEventGraph program) EventGraph.ExecutionMode.concurrentReveals

theorem foreign_binding_frame (runtime : EventGraphRuntime graph)
    (left right : State graph) (inputs : (graph).Inputs) (valid : left.Invariant inputs)
    (id : MessageId Player) (event : (graph).EventId) (candidate : Handle graph)
    (owner foreign : Player) (different : foreign ≠ owner)
    (sender : id.1 = foreign)
    (handled : handle runtime left ⟨id, .commitment event candidate⟩ = some right) :
    BindingFrame program owner left right := by
  obtain ⟨ready, timely, actor, payload, binding, code, node, authored, owned, vacant, unused⟩ :=
    handle_commitment_conditions runtime left right id event candidate handled
  have same : actor = foreign := authored.symm.trans sender
  simp only [same] at binding owned
  obtain ⟨address, named, stepReady, action, member⟩ :=
    handle_config_mem_step runtime left right ⟨id, .commitment event candidate⟩ handled
  have addressEq : event = address := Option.some.inj named
  subst address
  have history := Config.step_history left.config event stepReady action right.config member
  rw [Config.step, PMF.support_map] at member
  obtain ⟨output, _, config⟩ := member
  have tables := handle_commitment_tables runtime left right id event candidate handled
  have fields : ∀ query : (graph).EventId,
      (((graph).outputLayout query).IsPublic ∨
        ∃ sort, (graph).outputLayout query = .binding owner sort) → query ≠ event := by
    intro query visible sameQuery
    subst query
    rw [binding] at visible
    rcases visible with impossible | ⟨sort, owners⟩
    · exact impossible
    · exact different (EventField.binding.inj owners).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, (handle_clock_activated runtime left right
    ⟨id, .commitment event candidate⟩ handled).1.symm⟩
  · rw [← config]
    rfl
  · intro query visible
    rw [← config]
    exact (Config.complete_output_of_ne _ _ _ _ _ _
      (fields query (Or.inl visible))).symm
  · intro query sort outputEq
    rw [← config]
    exact (Config.complete_output_of_ne _ _ _ _ _ _
      (fields query (Or.inr ⟨sort, outputEq⟩))).symm
  · have acting := (graph).actor?_of_outputLayout_binding binding
    have other : (graph).actor? event ≠ some owner :=
      fun same => different (Option.some.inj (acting.symm.trans same))
    simp only [history, ownCompletions, List.filter_append, List.filter_cons, List.filter_nil,
      other, decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  · intro query sort outputEq
    have distinct : (.inr query : (graph).Field) ≠ .inr event :=
      fun sameField => fields query (Or.inr ⟨sort, outputEq⟩) (Sum.inr.inj sameField)
    rw [tables.2.1, Function.update_of_ne distinct]
  · intro slot
    rw [tables.1, CommitmentCandidates.lookup_freeze_other]
    intro sameHandle
    have ownerEq : owner = foreign := (congrArg Prod.fst sameHandle).trans owned
    exact different ownerEq.symm
  · intro queried queriedOwner
    have distinct : queried ≠ candidate := by
      intro sameHandle
      exact different (owned.symm.trans ((congrArg Prod.fst sameHandle).symm.trans queriedOwner))
    constructor
    · intro before field after
      rw [tables.2.1] at after
      by_cases selected : field = .inr event
      · subst field
        have sameHandle : candidate = queried := Option.some.inj (by
          simpa only [Function.update_self] using after)
        exact distinct sameHandle.symm
      · exact before field (by simpa only [Function.update_of_ne selected] using after)
    · intro after field before
      by_cases selected : field = .inr event
      · subst field
        rw [vacant] at before
        cases before
      · apply after field
        rw [tables.2.1, Function.update_of_ne selected]
        exact before
  · intro query sort outputEq
    exact (accepted_binding_foreign_stamp program runtime left right inputs valid id event query
      candidate owner foreign sort payload outputEq binding different handled).symm

private theorem unused_after_binding (runtime : EventGraphRuntime graph)
    (left right : State graph) (id : MessageId Player) (event : (graph).EventId)
    (candidate queried : Handle graph)
    (handled : handle runtime left ⟨id, .commitment event candidate⟩ = some right) :
    right.HandleUnused queried ↔ queried ≠ candidate ∧ left.HandleUnused queried := by
  have table := (handle_commitment_tables runtime left right id event candidate handled).2.1
  obtain ⟨_, _, _, _, _, _, _, _, _, vacant, _⟩ :=
    handle_commitment_conditions runtime left right id event candidate handled
  constructor
  · intro unused
    refine ⟨?_, ?_⟩
    · intro same
      apply unused (.inr event)
      rw [table, Function.update_self, same]
    · intro field present
      by_cases selected : field = .inr event
      · subst field
        rw [vacant] at present
        cases present
      · apply unused field
        rw [table, Function.update_of_ne selected]
        exact present
  · rintro ⟨different, unused⟩ field present
    rw [table] at present
    by_cases selected : field = .inr event
    · subst field
      have same : candidate = queried := Option.some.inj (by
        simpa only [Function.update_self] using present)
      exact different same.symm
    · exact unused field (by simpa only [Function.update_of_ne selected] using present)

theorem BindingFrame.handle_binding {owner : Player} {left right : State graph}
    (frame : BindingFrame program owner left right) (runtime : EventGraphRuntime graph)
    (nextLeft : State graph) (id : MessageId Player) (event : (graph).EventId)
    (candidate : Handle graph) (sender : id.1 = owner)
    (handled : handle runtime left ⟨id, .commitment event candidate⟩ = some nextLeft) :
    ∃ nextRight : State graph,
      handle runtime right ⟨id, .commitment event candidate⟩ = some nextRight ∧
        BindingFrame program owner nextLeft nextRight := by
  obtain ⟨ready, timely, actor, payload, binding, code, node, authored, owned, vacant, unused⟩ :=
    handle_commitment_conditions runtime left nextLeft id event candidate handled
  have actorEq : actor = owner := authored.symm.trans sender
  simp only [actorEq] at binding owned
  have codeOwner : cast (congrArg (EventCode (graph).layout) binding) ((graph).nodes event) =
      .bind owner payload := by
    generalize cast (congrArg (EventCode (graph).layout) binding) ((graph).nodes event) = body
    cases body
    rfl
  have nodeOwner := nodeView_eq_bind binding codeOwner
  have rightReady := (frame.ready event payload binding).mp ready
  have rightTimely := (frame.withinDeadline runtime event payload binding).mp timely
  have rightVacant := (frame.accepted event payload binding).symm.trans vacant
  have rightUnused := (frame.unused candidate owned).mp unused
  have rightLaw := handle_commitment_eq runtime right id event candidate owner payload binding
    codeOwner
    nodeOwner rightReady rightTimely sender owned rightVacant rightUnused
  let nextRight :=
    { right.complete event rightReady
        (cast (congrArg EventField.Action binding.symm) (right.bindingResult candidate payload))
        (cast (congrArg EventField.Value binding.symm) (right.bindingResult candidate payload)) with
      accepted := Function.update right.accepted (.inr event) (some candidate)
      candidates := right.candidates.freeze candidate }
  change handle runtime right ⟨id, .commitment event candidate⟩ = some nextRight at rightLaw
  have catalogue : left.candidates.lookup candidate = right.candidates.lookup candidate := by
    have handleEq : candidate = (owner, candidate.2) := Prod.ext owned rfl
    rw [handleEq]
    exact frame.candidates _
  have result : left.bindingResult candidate payload = right.bindingResult candidate payload := by
    unfold State.bindingResult
    rw [catalogue]
  have leftLaw := handle_commitment_eq runtime left id event candidate owner payload binding
    codeOwner
    nodeOwner ready timely sender owned vacant unused
  have actualLeft := Option.some.inj (handled.symm.trans leftLaw)
  have leftTables := handle_commitment_tables runtime left nextLeft id event candidate handled
  have rightTables := handle_commitment_tables runtime right nextRight id event candidate rightLaw
  have timers (query : (graph).EventId) (sort : L.Ty)
      (outputEq : (graph).outputLayout query = .binding owner sort) :=
    accepted_binding_successor_timer program runtime left right nextLeft nextRight id id event query
      candidate candidate owner sort outputEq
      (fun prior cone => frame.completed sort prior cone) frame.clock
      (frame.activated query sort outputEq) handled rightLaw
  refine ⟨nextRight, rightLaw, ?_⟩
  constructor
  · rw [actualLeft]
    exact frame.inputs
  · intro query visible
    have different : query ≠ event := by
      intro same
      subst query
      rw [binding] at visible
      exact visible
    rw [actualLeft]
    change (left.config.complete event ready _ _).outputs query =
      (right.config.complete event rightReady _ _).outputs query
    rw [Config.complete_output_of_ne _ _ _ _ _ _ different,
      Config.complete_output_of_ne _ _ _ _ _ _ different]
    exact frame.publicOutputs query visible
  · intro query sort outputEq
    rw [actualLeft]
    change (left.config.complete event ready _ _).outputs query =
      (right.config.complete event rightReady _ _).outputs query
    by_cases same : query = event
    · subst query
      simp only [Config.complete_output_same, result]
    · rw [Config.complete_output_of_ne _ _ _ _ _ _ same,
        Config.complete_output_of_ne _ _ _ _ _ _ same]
      exact frame.ownerOutputs query sort outputEq
  · rw [actualLeft]
    have own := frame.ownHistory
    change left.config.history.filter _ = right.config.history.filter _ at own
    simp only [nextRight, State.complete, Config.complete, ownCompletions, List.filter_append,
      result, own]
  · intro query sort outputEq
    rw [leftTables.2.1, rightTables.2.1]
    by_cases same : (.inr query : (graph).Field) = .inr event
    · rw [same, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne same, Function.update_of_ne same]
      exact frame.accepted query sort outputEq
  · intro slot
    rw [leftTables.1, rightTables.1]
    by_cases same : (owner, slot) = candidate
    · rw [same, CommitmentCandidates.lookup_freeze_self, CommitmentCandidates.lookup_freeze_self,
        catalogue]
    · rw [CommitmentCandidates.lookup_freeze_other _ _ _ same,
        CommitmentCandidates.lookup_freeze_other _ _ _ same]
      exact frame.candidates slot
  · intro queried queriedOwner
    rw [unused_after_binding program runtime left nextLeft id event candidate queried handled,
      unused_after_binding program runtime right nextRight id event candidate queried rightLaw]
    exact and_congr Iff.rfl (frame.unused queried queriedOwner)
  · intro query sort outputEq
    exact (timers query sort outputEq).2.1
  · exact (timers event payload binding).2.2

theorem BindingFrame.handle_binding_getD {owner : Player} {left right : State graph}
    (frame : BindingFrame program owner left right) (runtime : EventGraphRuntime graph)
    (id : MessageId Player) (event : (graph).EventId) (candidate : Handle graph)
    (sender : id.1 = owner) :
    (handle runtime left ⟨id, .commitment event candidate⟩).isSome =
        (handle runtime right ⟨id, .commitment event candidate⟩).isSome ∧
      BindingFrame program owner
        ((handle runtime left ⟨id, .commitment event candidate⟩).getD left)
        ((handle runtime right ⟨id, .commitment event candidate⟩).getD right) := by
  cases handled : handle runtime left ⟨id, .commitment event candidate⟩ with
  | some next =>
      obtain ⟨other, counterpart, retained⟩ :=
        BindingFrame.handle_binding program frame runtime next id event candidate sender handled
      rw [counterpart]
      exact ⟨rfl, retained⟩
  | none =>
      cases counterpart : handle runtime right ⟨id, .commitment event candidate⟩ with
      | none =>
          exact ⟨rfl, frame⟩
      | some other =>
          obtain ⟨next, impossible, _⟩ :=
            BindingFrame.handle_binding program frame.symm runtime other id event candidate sender
              counterpart
          rw [handled] at impossible
          cases impossible

private theorem binding_getD_invariant (runtime : EventGraphRuntime graph)
    (state : State graph) (inputs : (graph).Inputs) (valid : state.Invariant inputs)
    (message : Message Player (Payload graph)) :
    ((handle runtime state message).getD state).Invariant inputs := by
  cases handled : handle runtime state message with
  | none => exact valid
  | some next => exact handle_invariant runtime state next message valid handled

theorem binding_fold_owner_projection (runtime : EventGraphRuntime graph) (owner : Player)
    (messages : List (Message Player (Payload graph))) (left right : State graph)
    (inputs : (graph).Inputs) (leftValid : left.Invariant inputs)
    (rightValid : right.Invariant inputs)
    (frame : BindingFrame program owner left right)
    (bindings : ∀ message ∈ messages, ∃ event candidate,
      message.payload = .commitment event candidate) :
    BindingFrame program owner
      (messages.foldl (fun state message => (handle runtime state message).getD state) left)
      ((messages.filter fun message => message.sender == owner).foldl
        (fun state message => (handle runtime state message).getD state) right) := by
  induction messages generalizing left right with
  | nil => exact frame
  | cons message rest ih =>
      obtain ⟨event, candidate, payload⟩ := bindings message (List.mem_cons_self ..)
      have tail : ∀ packet ∈ rest, ∃ event candidate,
          packet.payload = .commitment event candidate :=
        fun packet member => bindings packet (List.mem_cons_of_mem _ member)
      have leftNext := binding_getD_invariant program runtime left inputs leftValid message
      by_cases sender : message.sender = owner
      · have rightNext := binding_getD_invariant program runtime right inputs rightValid message
        have nextFrame : BindingFrame program owner
            ((handle runtime left message).getD left)
            ((handle runtime right message).getD right) := by
          rcases message with ⟨id, actual⟩
          change actual = _ at payload
          subst actual
          exact (BindingFrame.handle_binding_getD program frame runtime id event candidate sender).2
        simpa only [List.foldl_cons, List.filter_cons, sender, beq_self_eq_true, ↓reduceIte] using
          ih _ _ leftNext rightNext nextFrame tail
      · have localFrame : BindingFrame program owner left
            ((handle runtime left message).getD left) := by
          cases handled : handle runtime left message with
          | none => exact BindingFrame.refl owner left
          | some next =>
              rcases message with ⟨id, actual⟩
              change actual = _ at payload
              subst actual
              exact foreign_binding_frame program runtime left next inputs leftValid id event
                candidate owner id.1 sender rfl handled
        have nextFrame := localFrame.symm.trans frame
        have notOwner : (message.sender == owner) = false := by
          simp [sender]
        simpa only [List.foldl_cons, List.filter_cons, notOwner, Bool.false_eq_true,
          ↓reduceIte] using ih _ _ leftNext rightValid nextFrame tail

theorem binding_batches_owner_frame (runtime : EventGraphRuntime graph) (owner : Player)
    (leftPackets rightPackets : List (Message Player (Payload graph))) (left right : State graph)
    (inputs : (graph).Inputs) (leftValid : left.Invariant inputs)
    (rightValid : right.Invariant inputs)
    (frame : BindingFrame program owner left right)
    (leftBindings : ∀ message ∈ leftPackets, ∃ event candidate,
      message.payload = .commitment event candidate)
    (rightBindings : ∀ message ∈ rightPackets, ∃ event candidate,
      message.payload = .commitment event candidate)
    (ownPackets : leftPackets.filter (fun message => message.sender == owner) =
      rightPackets.filter (fun message => message.sender == owner)) :
    BindingFrame program owner
      (leftPackets.foldl (fun state message => (handle runtime state message).getD state) left)
      (rightPackets.foldl
        (fun state message => (handle runtime state message).getD state) right) := by
  have paired := binding_fold_owner_projection program runtime owner leftPackets left right inputs
    leftValid rightValid frame leftBindings
  rw [ownPackets] at paired
  have erased := binding_fold_owner_projection program runtime owner rightPackets right right
    inputs rightValid rightValid (BindingFrame.refl owner right) rightBindings
  exact paired.trans erased.symm

end Vegas.EventGraphRuntime.ReservedEpoch
