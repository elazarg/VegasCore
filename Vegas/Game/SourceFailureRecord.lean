/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourcePrefixPublications
import Vegas.Game.OnePacketEventFailure

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
    (valid : SourceFailureRecord profile before) (moved : EventGraph.Config.Step before after) :
    SourceFailureRecord profile after := by
  obtain ⟨completed, ready, action, member⟩ := moved
  obtain ⟨rank, ⟨residual⟩, record⟩ := valid
  have readyPrefix : before.cut.IsPrefix completed.val := by
    refine ⟨completed.isLt.le, ?_⟩
    intro other
    exact before.cut.mem_completed_iff_lt_of_ready ready
  have rankEq : completed.val = rank := readyPrefix.unique residual.checkpoint.ordered
  obtain ⟨successor, _reachedPoint⟩ := residual.step completed ready action _ member
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
          (Revelations.initial setup.context) (outputRef setup.program) _ _ _ _ other.isLt owner
          payload outputEq nextDecoded ((eventOwner?_eq_actor setup.program other).trans acting)
          readOutput).indebted _ _)
    | bind bindOwner payload outputEq codeEq =>
        have ownerEq : bindOwner = owner :=
          Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans acting)
        subst bindOwner
        obtain ⟨value, read, isFailure⟩ := storeEventFailed_get? failed
          (⟨.inr other, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
            (.binding owner payload)) rfl
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
        exact Or.inr (ProtocolState.failedBinding_of_decode_failure setup.program
          setup.namesNodup other.val
          (ContextRefs.initial setup.context (outputLayout setup.program)) []
          (Revelations.initial setup.context) (outputRef setup.program) _ _ _ _ other.isLt owner
          payload outputEq nextDecoded ((eventOwner?_eq_actor setup.program other).trans acting)
          readOutput)
  · have different : other ≠ completed := fun same => ready.1 (same ▸ earlier)
    have kept : StoreEventFailed before.store other := by
      obtain ⟨value, read, failure⟩ := failed
      refine ⟨value, ?_, failure⟩
      change before.outputs other = _
      change after.outputs other = _ at read
      have complete : ∃ output, after = before.complete completed ready action output := by
        unfold EventGraph.Config.step at member
        rw [PMF.support_map] at member
        obtain ⟨output, _, rfl⟩ := member
        exact ⟨output, rfl⟩
      obtain ⟨output, same⟩ := complete
      rw [same, EventGraph.Config.complete_output_of_ne _ _ _ _ _ _ different] at read
      exact read
    obtain ⟨_, retained⟩ := residual.decodedHolds_step (owesFailure_stepClosed owner)
      (record other earlier owner acting kept) completed ready action after member
    exact retained

/-- A finite graph path preserves failed-output debt at its actual endpoint. -/
theorem path {before after : (graph setup).Config}
    (valid : SourceFailureRecord profile before)
    (moved : Relation.ReflTransGen EventGraph.Config.Step before after) :
    SourceFailureRecord profile after := by
  induction moved using Relation.ReflTransGen.head_induction_on with
  | refl => exact valid
  | @head _ _ step _ ih => exact ih (valid.step step)

end SourceFailureRecord
end Vegas
