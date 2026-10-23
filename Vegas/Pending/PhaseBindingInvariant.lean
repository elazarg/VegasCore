/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseApplication
import Vegas.Pending.ReactiveAcceptedOutput

/-! # Immutable binding meanings through actual phase rollback -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace State

omit [DecidableEq Player] in
/-- Replacing only a catalogue by an extension of its fixed meanings preserves
all accepted associations and typed binding outputs at the saved frontier. -/
theorem BindingInvariant.copy_fixed {before after : State graph}
    (valid : before.BindingInvariant) (config : after.config = before.config)
    (accepted : after.accepted = before.accepted) (fixed : KeepsFixedCandidates before after) :
    after.BindingInvariant := by
  refine ⟨valid.toAssociationInvariant.transport accepted fixed (fun field value stored => by
    rw [config]; exact stored), ?_, ?_, ?_⟩
  · intro field candidate installed
    rw [accepted] at installed
    exact valid.accepted_typed field candidate installed
  · intro left right candidate atLeft atRight
    rw [accepted] at atLeft atRight
    exact valid.accepted_injective left right candidate atLeft atRight
  · intro owner payload ref value stored
    rw [config] at stored
    obtain ⟨candidate, installed, owned, opened⟩ := valid.success_provenance ref value stored
    refine ⟨candidate, by rw [accepted]; exact installed, owned, ?_⟩
    rw [fixed candidate (by rw [opened]; simp)]
    exact opened

omit [DecidableEq Player] in
/-- An automatic excluded-owner completion introduces no binding success. -/
theorem completeFailure_bindingInvariant {state : State graph}
    (valid : state.BindingInvariant) (event : graph.EventId)
    (ready : state.config.cut.Ready event) {owner : Player}
    (acting : graph.actor? event = some owner) :
    (state.completeFailure event ready).BindingInvariant := by
  cases view : nodeView graph event with
  | bind author payload outputEq codeEq =>
      simp only [State.completeFailure, view]
      apply BindingInvariant.complete_of_no_success valid event ready
        (cast (congrArg EventField.Action outputEq.symm) PublicationResult.failure)
        (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure)
      intro other ty otherEq value
      have same := outputEq.symm.trans otherEq
      cases same
      simp
  | resolve author payload binding checks outputEq codeEq =>
      simp only [State.completeFailure, view]
      apply BindingInvariant.complete_nonbinding valid event ready
        (cast (congrArg EventField.Action outputEq.symm) false)
        (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure)
      intro other ty otherEq
      cases outputEq.symm.trans otherEq
  | sample payload law outputEq codeEq =>
      have actorNone : graph.actor? event = none :=
        (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
          (congrArg EventCode.actor codeEq)
      rw [actorNone] at acting
      cases acting

end State

namespace RuntimePhase

/-- Local excluded service preserves the accepted meaning of every binding. -/
theorem drainFuel_bindingInvariant (phase : RuntimePhase graph) (fuel : Nat)
    (state : RecoveryState graph) (valid : state.native.BindingInvariant) :
    (phase.drainFuel fuel state).native.BindingInvariant := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
      unfold drainFuel
      split
      · rename_i pending
        obtain ⟨owner, acting, _excluded⟩ := (Classical.choose_spec pending).2.owned
        exact ih _ (State.completeFailure_bindingInvariant valid _
          (Classical.choose_spec pending).2.1 acting)
      · exact valid

theorem drain_bindingInvariant (phase : RuntimePhase graph) (state : RecoveryState graph)
    (valid : state.native.BindingInvariant) : (phase.drain state).native.BindingInvariant :=
  phase.drainFuel_bindingInvariant _ _ valid

end RuntimePhase

namespace PhaseRuntimeState

/-- Both the semantic checkpoint and current attempt retain exact accepted
binding provenance, and later preparation never changes a saved fixed meaning. -/
structure BindingRecord (state : PhaseRuntimeState graph) : Prop where
  saved : state.entry.native.BindingInvariant
  active : state.current.native.BindingInvariant
  fixed : KeepsFixedCandidates state.entry.native state.current.native

omit [DecidableEq Player] in
/-- Restoring semantic fields keeps the latest immutable candidate meanings. -/
theorem restore_bindingInvariant (entry current : RecoveryState graph)
    (saved : entry.native.BindingInvariant) (fixed : KeepsFixedCandidates entry.native
      current.native) : (restore entry current).native.BindingInvariant :=
  saved.copy_fixed rfl rfl fixed

/-- Closing any number of automatic phases preserves the original physical
candidate catalogue and the accepted semantics of the newly saved frontier. -/
theorem settle_bindingRecord (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (saved : entry.native.BindingInvariant) (active : current.native.BindingInvariant)
    (fixed : KeepsFixedCandidates entry.native current.native) :
    (settle phases generation entry current retired).BindingRecord := by
  induction phases generalizing generation entry current retired with
  | nil => exact ⟨saved, active, fixed⟩
  | cons phase rest ih =>
      have drained := phase.drain_bindingInvariant current active
      have drainedFixed : KeepsFixedCandidates entry.native (phase.drain current).native := by
        intro candidate wasFixed
        rw [(phase.drain_tables current).2.1]
        exact fixed candidate wasFixed
      have restored := restore_bindingInvariant entry (phase.drain current) saved drainedFixed
      have rebuilt := phase.drain_bindingInvariant (restore entry (phase.drain current)) restored
      simp only [settle]
      split
      · split
        · split
          · refine ⟨restored, rebuilt, ?_⟩
            intro candidate _wasFixed
            rw [(phase.drain_tables _).2.1]
          · exact ih _ _ _ _ rebuilt rebuilt (fun _ _ => rfl)
        · exact ih _ _ _ _ drained drained (fun _ _ => rfl)
      · exact ⟨saved, drained, drainedFixed⟩

/-- The actual compiled initial law starts with valid accepted binding tables. -/
theorem initial_bindingRecord (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (initial plan inputs).BindingRecord :=
  settle_bindingRecord _ _ _ _ _ (State.initial_bindingInvariant inputs)
    (State.initial_bindingInvariant inputs) (fun _ _ => rfl)

end PhaseRuntimeState

/-- Actual application operations, including phase retirement and rollback,
preserve binding provenance without a source-attempt premise. -/
theorem phaseApplication_bindingInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant PhaseRuntimeState.BindingRecord where
  submit state who material valid := by
    have registered : (material.call.register state.current.native who).BindingInvariant := by
      rw [material.call.register_eq]
      cases command : material.call.registrationCommand who with
      | none => exact valid.active
      | some privateCommand => exact privateStep_bindingInvariant _ valid.active who privateCommand
    refine ⟨valid.saved, submitStep_bindingInvariant _ registered who material.call.packet, ?_⟩
    intro candidate savedFixed
    change state.entry.native.candidates.lookup candidate ≠ .fresh at savedFixed
    change (submitStep (material.call.register state.current.native who) who
      material.call.packet).candidates.lookup candidate =
        state.entry.native.candidates.lookup candidate
    have activeFixed : state.current.native.candidates.lookup candidate ≠ .fresh := by
      rw [valid.fixed candidate savedFixed]
      exact savedFixed
    have prepared := material.call.register_lookup_of_not_fresh state.current.native who
      candidate activeFixed
    rw [submitStep_lookup_of_not_fresh _ _ _ candidate (by rwa [prepared]), prepared]
    exact valid.fixed candidate savedFixed
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      apply PhaseRuntimeState.settle_bindingRecord _ _ _ _ _ valid.saved
        (handle_bindingInvariant runtime _ native _ valid.active handled)
      intro candidate savedFixed
      have activeFixed : state.current.native.candidates.lookup candidate ≠ .fresh := by
        rw [valid.fixed candidate savedFixed]
        exact savedFixed
      exact (handle_lookup_of_not_fresh runtime _ native _ candidate activeFixed handled).trans
        (valid.fixed candidate savedFixed)
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, supported, rfl⟩ := reached
      apply PhaseRuntimeState.settle_bindingRecord _ _ _ _ _ valid.saved
        (environmentStep_bindingInvariant runtime _ native command valid.active supported)
      intro candidate savedFixed
      change native.candidates.lookup candidate = state.entry.native.candidates.lookup candidate
      rw [(environmentStep_tables runtime _ native command supported).2]
      exact valid.fixed candidate savedFixed
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- Every actual initialized phase-runtime history has the accepted binding
semantics used by the compiler's source-attempt decoder. -/
theorem phaseBindingRecord_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    control.execution.application.BindingRecord :=
  (phaseApplication_bindingInvariant runtime leaks).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact PhaseRuntimeState.initial_bindingRecord plan draw) trace

end Vegas.EventGraphRuntime
