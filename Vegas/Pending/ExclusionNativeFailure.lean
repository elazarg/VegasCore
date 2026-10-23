/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionPublicRecord

/-! # Native public failure persistence -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

omit [DecidableEq Player] in
/-- Completing a different ready event preserves every previous public failure. -/
theorem State.PublicFailure.of_completionStep {before after : State graph}
    (step : CompletionStep before after) {event : graph.EventId}
    (failed : before.PublicFailure event) : after.PublicFailure event := by
  rcases step with ⟨same, accepted, _⟩ | ⟨next, ready, action, reached, _, acceptedOnly⟩
  · exact (State.PublicFailure.congr event (by rw [same]) (by rw [same])
      (congrFun accepted _)).mpr failed
  · have different : event ≠ next := fun same => ready.1 (same ▸ failed.completed)
    exact (State.PublicFailure.of_step_of_ne reached (fun field changed =>
      (acceptedOnly field changed).2) different).mpr failed

/-- Every native operation either preserves the completion footprint or
completes one ready event. Private preparation changes no public footprint. -/
theorem reactiveApplication_completionStep :
    (runtime.reactiveApplication leaks).StepRelation CompletionStep where
  refl := CompletionStep.refl
  submit := by
    intro state who submission
    have publicEq := reactiveApplication_submit_publicView runtime leaks state who submission
    refine Or.inl ⟨?_, congrArg PublicView.accepted publicEq,
      congrArg PublicView.activatedAt publicEq⟩
    change (submitStep (submission.call.register state who) who _).config = _
    rw [submitStep_config, (submission.call.register_facts who state).1]
  handle := fun state message next accepted =>
    completionStep_handle runtime state next _ (reactiveHandle_call accepted)
  environment := fun state command next reached =>
    completionStep_environmentStep runtime state next command reached

/-- No future native operation can erase the public evidence of exclusion. -/
theorem reactiveApplication_publicFailure_monotone :
    (runtime.reactiveApplication leaks).StepRelation
      (fun before after => ∀ event, before.PublicFailure event → after.PublicFailure event) where
  refl := fun _ _ failed => failed
  submit := fun state who submission _event failed => failed.of_completionStep
    ((reactiveApplication_completionStep runtime leaks).submit state who submission)
  handle := fun state message next accepted _event failed => failed.of_completionStep
    ((reactiveApplication_completionStep runtime leaks).handle state message next accepted)
  environment := fun state command next reached _event failed => failed.of_completionStep
    ((reactiveApplication_completionStep runtime leaks).environment state command next reached)

/-- Accepted handles retain completed-event provenance along every native history. -/
theorem native_receiptsComplete_history (initial : PMF (State graph))
    (initialized : ∀ native ∈ initial.support, ∃ inputs, native = State.initial inputs)
    (horizon : Nat) (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {state : (runtime.reactiveApplication leaks).ProtocolState}
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace state) :
    ReactiveApplication.stateInvariant State.ReceiptsComplete state := by
  let step := reactiveApplication_completionStep runtime leaks
  have preserved : (runtime.reactiveApplication leaks).Invariant State.ReceiptsComplete :=
    { submit := fun state who submission valid => valid.step (step.submit state who submission)
      handle := fun state message next valid accepted =>
        valid.step (step.handle state message next accepted)
      environment := fun state command next valid reached =>
        valid.step (step.environment state command next reached) }
  apply preserved.history initial horizon scheduler ?_ trace
  intro native supported
  obtain ⟨inputs, rfl⟩ := initialized native supported
  exact State.ReceiptsComplete.initial inputs

/-- If a native transition ends with no public exclusion evidence, its actual
predecessor also has none. The accepted-handle invariant is supplied by the
actual predecessor history. -/
theorem native_clear_before_transition (initial : PMF (State graph))
    (initialized : ∀ native ∈ initial.support, ∃ inputs, native = State.initial inputs)
    (horizon : Nat) (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {before after : (runtime.reactiveApplication leaks).ProtocolState}
    (prior : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace before)
    (joint : Player → Option (runtime.reactiveApplication leaks).Action)
    (realized : after ∈ ((runtime.reactiveApplication leaks).transition initial horizon scheduler
      before joint).support)
    (clear : ∀ current, after = some current →
      PublicExclusionRecord (⟨current.execution.application, ∅⟩ : RecoveryState graph)) :
    ∀ current, before = some current →
      PublicExclusionRecord (⟨current.execution.application, ∅⟩ : RecoveryState graph) := by
  cases before with
  | none => intro current impossible; cases impossible
  | some current =>
    intro found same
    cases Option.some.inj same
    obtain ⟨next, nextEq, _recall⟩ :=
      (runtime.reactiveApplication leaks).transition_recall_prefix initial horizon scheduler
        current after joint realized
    have persists := (reactiveApplication_publicFailure_monotone runtime leaks).transition initial
      horizon scheduler current next joint (nextEq ▸ realized)
    refine ⟨native_receiptsComplete_history runtime leaks initial initialized horizon scheduler
      prior, fun owner => ⟨?_, ?_⟩⟩
    · intro member
      exact (Finset.notMem_empty owner member).elim
    · rintro ⟨event, acting, failed⟩
      exact (clear next nextEq).excluded owner |>.mpr ⟨event, acting, persists event failed⟩

end Vegas.EventGraphRuntime
