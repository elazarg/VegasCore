/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketFailureBridge
import Vegas.Game.OnePacketDisclosureResolves

/-! # Source debt recorded by failed compiled event outputs -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {profile : BehavioralProfile setup.program}

/-- A source residual together with the debt recorded by every completed
owned event whose output is a failure. -/
def SourceFailureRecord (profile : BehavioralProfile setup.program)
    (config : (graph setup).Config) : Prop :=
  ∃ rank, Nonempty (SourceResidual setup profile rank config) ∧
    ∀ event ∈ config.cut.completed, ∀ owner, (graph setup).actor? event = some owner →
      StoreEventFailed config.store event →
        DecodedHolds (ProtocolState.OwesFailure owner setup.program) rank config

namespace SourceFailureRecord

/-- Initial compiled configurations have no completed event outputs. -/
theorem initial (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) (initial : State L setup.context) :
    SourceFailureRecord profile
      (EventGraphRuntime.State.initial (graph := graph setup)
        (setup.eventInputs initial)).config := by
  let residual := SourceResidual.initial setup profile initial
  refine ⟨0, ⟨residual⟩, fun event completed => ?_⟩
  have below := (residual.checkpoint.ordered.2 event).mp completed
  exact absurd below (Nat.not_lt_zero _)

/-- Any supported compiled graph completion preserves the failed-output record. -/
theorem step {before after : (graph setup).Config}
    (valid : SourceFailureRecord profile before) (step : ConfigStep setup before after) :
    SourceFailureRecord profile after := by
  obtain ⟨rank, ⟨residual⟩, record⟩ := valid
  rcases step with same | ⟨completed, ready, action, member⟩
  · subst same
    exact ⟨rank, ⟨residual⟩, record⟩
  · have rankEq : completed.val = rank :=
      (ready_iff_rank setup _ rank residual.checkpoint.ordered completed).mp ready
    obtain ⟨successor, reachedPoint⟩ := residual.step completed ready action _ member
    have advanced : after.cut.IsPrefix (rank + 1) := by
      rw [before.step_cut completed ready action _ member]
      exact residual.checkpoint.ordered.complete_at completed ready rankEq
    refine ⟨rank + 1, ⟨successor⟩, fun other done owner acting failed => ?_⟩
    rw [before.step_cut completed ready action _ member, EventOrder.Cut.mem_complete] at done
    rcases done with rfl | earlier
    · cases view : nodeView (graph setup) other with
      | sample payload law outputEq codeEq =>
          rw [nodeView_sample_actor outputEq codeEq] at acting
          cases acting
      | resolve resolveOwner payload binding checks outputEq codeEq =>
          have ownerEq : resolveOwner = owner :=
            Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans acting)
          subst resolveOwner
          obtain ⟨value, read, isFailure⟩ := storeEventFailed_get? failed
            (⟨.inr other, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
              (.publication payload)) rfl
          change value = .failure at isFailure
          subst isFailure
          intro state decoded
          have nextDecoded := decoded
          rw [← rankEq] at nextDecoded
          unfold sourceServicePrefix? serviceSourcePrefix? at nextDecoded
          have readOutput : (outputRef setup.program other).get? after.store =
              some (cast (congrArg EventGraph.EventField.Value outputEq.symm)
                (PublicationResult.failure : PublicationResult (L.Val payload))) := by
            change after.outputs other = _
            change cast (congrArg Option (congrArg EventGraph.EventField.Value outputEq))
              (after.outputs other) = some .failure at read
            have castSome {A B : Type} (same : A = B) (value : B) :
                cast (congrArg Option same) (some (cast same.symm value)) = some value := by
              cases same
              rfl
            rw [← castSome (congrArg EventGraph.EventField.Value outputEq) .failure] at read
            exact (cast_inj _).mp read
          exact Or.inl ((ProtocolState.revealFailed_of_decode_failure setup.program other.val
            (ContextRefs.initial setup.context (outputLayout setup.program)) []
            (Revelations.initial setup.context) (outputRef setup.program) _ _ _ other.isLt owner
            payload outputEq nextDecoded ((eventOwner?_eq_actor setup.program other).trans acting)
            readOutput).indebted _ _)
      | bind bindOwner payload outputEq codeEq =>
          have ownerEq : bindOwner = owner :=
            Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans acting)
          subst bindOwner
          obtain ⟨value, failedRead, isFailure⟩ := storeEventFailed_get? failed
            (⟨.inr other, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
              (.binding owner payload)) rfl
          change value = .failure at isFailure
          subst isFailure
          have output := step_binding_output (outputEq := outputEq) (codeEq := codeEq) member
          have read : (⟨.inr other, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
              (.binding owner payload)).get? after.store =
              some (cast (congrArg EventGraph.EventField.Action outputEq) action) := by
            simp only [EventGraph.FieldRef.get?]
            change cast _ (after.outputs other) = _
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
          rw [read] at failedRead
          have failedResult := Option.some.inj failedRead
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
            exact acting
          exact ProtocolState.owesFailure_of_decode_failing setup.program setup.namesNodup
            other.val _ _ _ _ _ _ point other.isLt owner _ _ decodedBefore owned failing
            reachedPoint
    · have different : other ≠ completed := fun same => ready.1 (same ▸ earlier)
      have kept : StoreEventFailed before.store other := by
        obtain ⟨value, read, failure⟩ := failed
        refine ⟨value, ?_, failure⟩
        change before.outputs other = _
        change after.outputs other = _ at read
        obtain ⟨value, valueEq⟩ := step_complete_of_mem member
        rw [valueEq, EventGraph.Config.complete_output_of_ne _ _ _ _ _ _ different] at read
        exact read
      exact residual.decodedHolds_configStep (fun state joint target owing reached =>
        ProtocolState.owesFailure_step owner setup.program state joint target owing reached)
        (record other earlier owner acting kept)
        (Or.inr ⟨completed, ready, action, member⟩) advanced

end SourceFailureRecord
end Vegas
