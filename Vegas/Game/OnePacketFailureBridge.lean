/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSureFailure
import Vegas.Game.OnePacketActorRecord
import Vegas.Game.ServiceBlockView

/-! # A failed binding output is an owed failure

**The failed-binding record.** At every legal history of the supplied runtime,
under arbitrary responses and every scheduler, the configuration decodes at a
prefix, and every completed binding event whose output is a failure makes its
owner owe a failure at the decoded point (`Vegas.FailedBindingRecord`,
`Vegas.failedBindingRecord_history`): a binding output is the action that
completed the event, so a failed output is a failing decoded completion, and
owing a failure is closed under later steps.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

omit [DecidableEq Player] in
/-- A failure stored in an event's output is a failure read through any
reference to that output. -/
theorem storeEventFailed_get? {graph : EventGraph Player L}
    {store : EventGraph.Store graph.layout} {event : graph.EventId}
    (failed : StoreEventFailed store event) {kind : EventGraph.EventField Player L}
    (ref : EventGraph.FieldRef graph.layout kind) (field : ref.field = .inr event) :
    ∃ value, ref.get? store = some value ∧ kind.IsFailure value := by
  rcases ref with ⟨refField, layoutEq⟩
  change refField = .inr event at field
  subst field
  subst layoutEq
  exact failed

section Record

variable (profile : BehavioralProfile setup.program)

/-- **The failed-binding record.** The configuration decodes at a prefix, and
every completed binding event whose output is a failure makes its owner owe a
failure at the decoded point. -/
def FailedBindingRecord (execution : (application setup runtime leaks).Execution) : Prop :=
  ∃ rank, Nonempty (SourceResidual setup profile rank execution.application.config) ∧
    ∀ event ∈ execution.application.config.cut.completed, ∀ owner payload
      (outputEq : (graph setup).outputLayout event = .binding owner payload),
      (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
        (.binding owner payload)).get? execution.application.config.store = some .failure →
        DecodedHolds (ProtocolState.OwesFailure owner setup.program) rank
          execution.application.config

/-- The failed-binding record holds at every legal history of the default
runtime, under arbitrary responses and every scheduler. -/
theorem failedBindingRecord_serviceInvariant (scheduler : (application setup runtime
  leaks).Scheduler) :
    (application setup runtime leaks).ServiceInvariant scheduler (FailedBindingRecord (runtime :=
      runtime) profile) where
  respond execution who action valid := by
    have configEq := (runtime.reactive_respond_application leaks execution who action).1
    unfold FailedBindingRecord at valid ⊢
    rw [configEq]
    exact valid
  environment execution next command valid _ reached := by
    obtain ⟨rank, ⟨residual⟩, record⟩ := valid
    rcases environmentStep_configStep setup leaks execution next command reached with
      same | ⟨completed, ready, action, member⟩
    · refine ⟨rank, ?_, fun other done owner payload outputEq failed => ?_⟩
      · rw [same]
        exact ⟨residual⟩
      · rw [same] at done failed ⊢
        exact record other done owner payload outputEq failed
    · have rankEq : completed.val = rank :=
        (ready_iff_rank setup _ rank residual.checkpoint.ordered completed).mp ready
      obtain ⟨successor, reachedPoint⟩ := residual.step completed ready action _ member
      have advanced : next.application.config.cut.IsPrefix (rank + 1) := by
        rw [execution.application.config.step_cut completed ready action _ member]
        exact residual.checkpoint.ordered.complete_at completed ready rankEq
      refine ⟨rank + 1, ⟨successor⟩, fun other done owner payload outputEq failed => ?_⟩
      rw [execution.application.config.step_cut completed ready action _ member,
        EventOrder.Cut.mem_complete] at done
      rcases done with rfl | earlier
      · cases view : nodeView (graph setup) other with
        | sample _ _ sampleEq _ =>
            rw [outputEq] at sampleEq
            cases sampleEq
        | resolve _ _ _ _ resolveEq _ =>
            rw [outputEq] at resolveEq
            cases resolveEq
        | bind bindOwner bindPayload bindEq codeEq =>
            obtain ⟨ownerEq, payloadEq⟩ :=
              EventGraph.EventField.binding.inj (bindEq.symm.trans outputEq)
            subst bindOwner
            subst bindPayload
            have output := step_binding_output (outputEq := outputEq)
              (codeEq := by
                have same : bindEq = outputEq := rfl
                exact same ▸ codeEq) member
            have read : (⟨.inr other, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
                (.binding owner payload)).get? next.application.config.store =
                some (cast (congrArg EventGraph.EventField.Action outputEq) action) := by
              simp only [EventGraph.FieldRef.get?]
              change cast _ (next.application.config.outputs other) = _
              rw [output]
              have castSome {A B : Type} (same : A = B) (value : A) :
                  cast (congrArg Option same) (some value) = some (cast same value) := by
                cases same
                rfl
              rw [castSome (congrArg EventGraph.EventField.Value outputEq)]
              have castInverse {A B : Type} (same : A = B) (value : B) :
                  cast same (cast same.symm value) = value := by
                cases same
                rfl
              rw [castInverse]
            rw [read] at failed
            have failedResult := Option.some.inj failed
            have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
                (PublicationResult.failure : PublicationResult (L.Val payload)) := by
              rw [← failedResult, cast_cast, cast_eq]
            have failing := decodeEventAction_failing_binding setup.program other.val other.isLt
              outputEq
            rw [← actionEq] at failing
            intro state decoded
            rw [successor.decode] at decoded
            obtain rfl := Option.some.inj decoded
            have decodedBefore := residual.decode
            generalize residual.lift (ProtocolState.entry residual.program residual.source) =
              point at decodedBefore reachedPoint
            rw [← rankEq] at decodedBefore
            have owned : eventOwner? setup.program ⟨other.val, other.isLt⟩ = some owner := by
              rw [eventOwner?_eq_actor]
              exact nodeView_bind_actor outputEq (by
                have same : bindEq = outputEq := rfl
                exact same ▸ codeEq)
            exact ProtocolState.owesFailure_of_decode_failing setup.program setup.namesNodup
              other.val _ _ _ _ _ _ point other.isLt owner _ _ decodedBefore owned failing
              reachedPoint
      · have different : other ≠ completed := fun same => ready.1 (same ▸ earlier)
        have kept : (⟨.inr other, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
            (.binding owner payload)).get? execution.application.config.store = some .failure := by
          rw [← failed]
          apply EventGraph.FieldRef.get?_congr
          change execution.application.config.outputs other = next.application.config.outputs other
          obtain ⟨value, valueEq⟩ := step_complete_of_mem member
          rw [valueEq, EventGraph.Config.complete_output_of_ne _ _ _ _ _ _ different]
        exact residual.decodedHolds_configStep (fun state joint target owing reached =>
          ProtocolState.owesFailure_step owner setup.program state joint target owing reached)
          (record other earlier owner payload outputEq kept)
          (Or.inr ⟨completed, ready, action, member⟩) advanced

/-- The failed-binding record holds at every legal history of the default
runtime from its initial law. -/
theorem failedBindingRecord_history (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler)
    {control : (application setup runtime leaks).Control}
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control)) :
    FailedBindingRecord (runtime := runtime) profile control.execution :=
  (failedBindingRecord_serviceInvariant (runtime := runtime) profile scheduler).history
    (initialLaw setup) horizon
    (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      let residual := SourceResidual.initial setup profile initial
      refine ⟨0, ⟨residual⟩, fun event completed => ?_⟩
      have below := (residual.checkpoint.ordered.2 event).mp completed
      exact absurd below (Nat.not_lt_zero _)) trace

end Record

end Vegas
