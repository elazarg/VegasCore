/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PublicFailureEvidence
import Interaction.ReactiveHistory

/-! # Native failure persistence and receipt provenance -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Completing a different ready event preserves every previous public failure. -/
theorem State.PublicFailure.of_completionStep {before after : State graph}
    (step : CompletionStep before after) {event : graph.EventId}
    (failed : before.PublicFailure event) : after.PublicFailure event :=
  (step.publicFailure_iff_of_completed failed.completed).mpr failed

/-- No application operation can erase public failure evidence. -/
theorem reactiveApplication_publicFailure_monotone :
    (runtime.reactiveApplication leaks).StepRelation
      (fun before after => ∀ event, before.PublicFailure event → after.PublicFailure event) where
  refl := fun _ _ failed => failed
  submit := fun state who submission _event failed => failed.of_completionPath
    ((reactiveApplication_completionPath runtime leaks).submit state who submission)
  handle := fun state message next accepted _event failed => failed.of_completionPath
    ((reactiveApplication_completionPath runtime leaks).handle state message next accepted)
  environment := fun state command next reached _event failed => failed.of_completionPath
    ((reactiveApplication_completionPath runtime leaks).environment state command next reached)

/-- Every application operation preserves prior public default membership. -/
theorem reactiveApplication_defaulted_monotone :
    (runtime.reactiveApplication leaks).StepRelation
      (fun before after => before.config.defaulted ⊆ after.config.defaulted) where
  refl := fun _ => Finset.Subset.refl _
  submit := fun state who submission => CompletionStep.defaulted_mono_path
    ((reactiveApplication_completionPath runtime leaks).submit state who submission)
  handle := fun state message next accepted => CompletionStep.defaulted_mono_path
    ((reactiveApplication_completionPath runtime leaks).handle state message next accepted)
  environment := fun state command next reached => CompletionStep.defaulted_mono_path
    ((reactiveApplication_completionPath runtime leaks).environment state command next reached)

/-- Accepted handles retain completed-event provenance along every initialized history. -/
theorem native_receiptsComplete_history (initial : PMF (State graph))
    (initialized : ∀ native ∈ initial.support, ∃ inputs, native = State.initial inputs)
    (horizon : Nat) (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {state : (runtime.reactiveApplication leaks).ProtocolState}
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace state) :
    ReactiveApplication.stateInvariant State.ReceiptsComplete state := by
  let step := reactiveApplication_completionPath runtime leaks
  have preserved : (runtime.reactiveApplication leaks).Invariant State.ReceiptsComplete :=
    { submit := fun state who submission valid => valid.path (step.submit state who submission)
      handle := fun state message next valid accepted =>
        valid.path (step.handle state message next accepted)
      environment := fun state command next valid reached =>
        valid.path (step.environment state command next reached) }
  apply preserved.history initial horizon scheduler ?_ trace
  intro native supported
  obtain ⟨inputs, rfl⟩ := initialized native supported
  exact State.ReceiptsComplete.initial inputs

/-- If a native transition ends without defaults, its predecessor also has none.
No initialization or receipt assumption is needed for this monotonicity fact. -/
theorem native_clear_before_transition (initial : PMF (State graph))
    (horizon : Nat) (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {before after : (runtime.reactiveApplication leaks).ProtocolState}
    (joint : Player → Option (runtime.reactiveApplication leaks).Action)
    (realized : after ∈ ((runtime.reactiveApplication leaks).transition initial horizon scheduler
      before joint).support)
    (clear : ∀ current, after = some current →
      current.execution.application.config.defaulted = ∅) :
    ∀ current, before = some current → current.execution.application.config.defaulted = ∅ := by
  cases before with
  | none => intro current impossible; cases impossible
  | some current =>
    intro found same
    cases Option.some.inj same
    obtain ⟨next, nextEq, _recall⟩ :=
      (runtime.reactiveApplication leaks).transition_recall_prefix initial horizon scheduler
        current after joint realized
    have persists := (reactiveApplication_defaulted_monotone runtime leaks).transition initial
      horizon scheduler current next joint (nextEq ▸ realized)
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro who member
    have remaining := persists member
    rw [clear next nextEq] at remaining
    exact Finset.notMem_empty _ remaining

end Vegas.EventGraphRuntime
