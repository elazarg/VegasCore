/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochBindingReadiness
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

private theorem binding_getD_invariant (runtime : EventGraphRuntime graph)
    (state : State graph) (inputs : (graph).Inputs) (valid : state.Invariant inputs)
    (message : Message Player (Payload graph)) :
    ((handle runtime state message).getD state).Invariant inputs := by
  cases handled : handle runtime state message with
  | none => exact valid
  | some next => exact handle_invariant runtime state next message valid handled

end Vegas.EventGraphRuntime.ReservedEpoch
