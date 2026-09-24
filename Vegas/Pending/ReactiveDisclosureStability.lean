/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDisclosure
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.Pending.ReactiveObservedState

/-! # Stable inputs of a submitted disclosure

Submission and inclusion preserve the application cache and every completed
read field. Accepted associations at those fields are immutable as well. Thus
later unrelated traffic cannot change either the selected disclosure packet or
its deferred-guard result.
-/

noncomputable section

namespace Vegas.EventGraphRuntime
open GameTheory.Math.Probability Interaction EventGraph
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem handle_accepted_of_present (runtime : EventGraphRuntime graph)
    (state next : State graph) (field : graph.Field)
    (present : (state.config.store field).isSome = true)
    (message : Message Player (Payload graph))
    (handled : handle runtime state message = some next) :
    next.accepted field = state.accepted field := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at handled
  | opening event chosen raw | withhold event =>
      rw [(handle_resolution_tables runtime state next _ (by intros; simp) handled).1]
  | commitment event chosen =>
      have tables := (handle_commitment_tables runtime state next id event chosen handled).2.1
      have different : field ≠ .inr event := by
        intro same
        subst field
        have completed := (state.config.output_available event).mp present
        obtain ⟨actual, addressed, ready, action, supported⟩ := handle_config_mem_step runtime
          state next ⟨id, .commitment event chosen⟩ handled
        have equal : actual = event := by simpa only [Payload.event?, Option.some.injEq]
          using addressed.symm
        subst actual
        exact ready.1 completed
      rw [tables, Function.update_of_ne different]

theorem reactiveReadFrameInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (original : State graph) (fields : Finset graph.Field)
    (available : ∀ field ∈ fields, (original.config.store field).isSome = true) :
    (runtime.reactiveApplication leaks).Invariant (fun state => ∀ field ∈ fields,
      state.config.store field = original.config.store field ∧
        state.accepted field = original.accepted field) where
  submit state who material agrees := by
    have same := runtime.reactive_respond_application leaks
      (.initial (runtime.reactiveApplication leaks) state) who ⟨some (.submit material)⟩
    have associated := congrArg PublicView.accepted same.2
    intro field member
    exact ⟨(congrArg (fun config : graph.Config => config.store field) same.1).trans
      (agrees field member).1, (congrFun associated field).trans (agrees field member).2⟩
  handle state message next agrees handled := by
    intro field member
    obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp (available field member)
    have present : state.config.store field = some value := (agrees field member).1.trans stored
    refine ⟨(handle_store_of_some runtime state next ⟨message.id, message.payload.call⟩
      handled field value present).trans stored.symm, ?_⟩
    exact (handle_accepted_of_present runtime state next field (by simp only [present]; rfl)
      ⟨message.id, message.payload.call⟩ handled).trans (agrees field member).2
  environment state command next agrees reached := by
    intro field member
    obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp (available field member)
    refine ⟨(environmentStep_store_of_some runtime state next command reached field value
      ((agrees field member).1.trans stored)).trans stored.symm, ?_⟩
    rw [(environmentStep_tables runtime state next command reached).1]
    exact (agrees field member).2

theorem reactiveResolutionPacket_eq_of_binding {owner : Player}
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (left right : ReactivePlayerView graph)
    (bound : binding.get? left.observation.store = binding.get? right.observation.store)
    (associated : left.publicView.accepted binding.field =
      right.publicView.accepted binding.field) :
    reactiveResolutionPacket who event payload binding outputEq action left =
      reactiveResolutionPacket who event payload binding outputEq action right := by
  unfold reactiveResolutionPacket
  rw [bound, associated]

omit [DecidableEq Player] in
theorem resolution_readFields (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks) :
    (graph.nodes event).readFields = insert binding.field (GuardCheck.listReadFields checks) := by
  calc
    (graph.nodes event).readFields =
        (cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event)).readFields :=
      (EventCode.readFields_cast outputEq (graph.nodes event)).symm
    _ = (EventCode.resolve owner payload binding checks).readFields :=
      congrArg EventCode.readFields codeEq
    _ = _ := rfl

end Vegas.EventGraphRuntime
