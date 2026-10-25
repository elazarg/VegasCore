/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourcePrefixPublications
import Vegas.Game.OnePacketForcedRegular
import Vegas.Pending.ExclusionEvidence

/-! # Clear public runtime evidence gives the source public record -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem cast_option_none {A B : Type} (same : A = B) :
    cast (congrArg Option same) (none : Option A) = none := by
  cases same
  rfl

private theorem cast_option_some {A B : Type} (same : A = B) (value : A) :
    cast (congrArg Option same) (some value) = some (cast same value) := by
  cases same
  rfl

private theorem publicationFailure_has_owner
    (native : EventGraphRuntime.State (graph setup)) (event : (graph setup).EventId)
    (payload : L.Ty) (outputEq : (graph setup).outputLayout event = .publication payload)
    (read : cast (congrArg (fun kind : EventGraph.EventField Player L => Option kind.Value)
      outputEq) (native.config.outputs event) = some .failure) :
    ∃ owner, (graph setup).actor? event = some owner ∧ native.PublicFailure event := by
  cases node : nodeView (graph setup) event with
  | sample other law layoutEq codeEq =>
      rw [layoutEq] at outputEq
      cases outputEq
  | bind owner other layoutEq codeEq =>
      rw [layoutEq] at outputEq
      cases outputEq
  | resolve owner other binding checks layoutEq codeEq =>
      have same : other = payload := EventGraph.EventField.publication.inj
        (layoutEq.symm.trans outputEq)
      subst other
      refine ⟨owner, nodeView_resolve_actor layoutEq codeEq, Or.inr ?_⟩
      cases output : native.config.outputs event with
      | none =>
          have transported : cast
              (congrArg (fun kind : EventGraph.EventField Player L => Option kind.Value) outputEq)
              (none : Option ((graph setup).outputLayout event).Value) = none :=
            cast_option_none (congrArg EventGraph.EventField.Value outputEq)
          rw [output, transported] at read
          cases read
      | some value =>
          have transported : cast
              (congrArg (fun kind : EventGraph.EventField Player L => Option kind.Value) outputEq)
              (some value) = some (cast (congrArg EventGraph.EventField.Value outputEq) value) :=
            cast_option_some (congrArg EventGraph.EventField.Value outputEq) value
          rw [output, transported] at read
          have failed := Option.some.inj read
          simp only [RecoveryState.publicationFailed, node, output]
          rw [failed]

/-- A clear public exclusion record excludes every failed source reveal at the
actual decoded prefix. No debt-freeness is inferred for hidden commitments. -/
theorem not_revealFailed_of_exclusionEvidence
    (native : EventGraphRuntime.State (graph setup))
    (clear : ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
    (rank : Nat) (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank native.config = some point) (who : Player) :
    ¬ ProtocolState.RevealFailed who setup.program point := by
  apply not_revealFailed_of_decodeSourcePrefix? rank setup.program _ _ _ _ native.config.store
    _ point decoded ?_ who
  intro event _earlier payload outputEq failed
  have read : cast
      (congrArg (fun kind : EventGraph.EventField Player L => Option kind.Value) outputEq)
      (native.config.outputs event) = some .failure := failed
  obtain ⟨owner, acting, evidence⟩ :=
    publicationFailure_has_owner native event payload outputEq read
  have excluded := (clear.excluded_zero owner).mpr ⟨event, acting, evidence⟩
  exact Finset.notMem_empty owner excluded

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- At an actual native one-packet prefix, clear permanent public evidence gives
accepted completed bindings and absence of source failed reveals. -/
theorem publicRecord_of_exclusionEvidence
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (who : Player) : PublicRecord setup who control := by
  refine ⟨?_, ?_⟩
  · intro event owner payload outputEq _other completed absent
    have missed := (control.execution.application.publicView_missedBinding event owner payload
      outputEq).mpr ⟨completed, absent⟩
    have evidence : control.execution.application.PublicFailure event := Or.inl missed
    have excluded := (clear.excluded_zero owner).mpr
      ⟨event, actor_of_binding outputEq, evidence⟩
    exact Finset.notMem_empty owner excluded
  · intro other _different point decoded
    obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
      (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler trace control rfl
    have same := Option.some.inj ((decodedPoint_eq residual).symm.trans decoded)
    subst point
    exact not_revealFailed_of_exclusionEvidence control.execution.application clear rank _
      residual.decode other

end Vegas
