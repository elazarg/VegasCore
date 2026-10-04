/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingAcceptedOpening
import Vegas.Pending.PacketNodeKind

/-! # A used mistyped candidate has no lawful opening continuation

Accepted-handle injectivity and typed field references force all associated
bindings to have the same payload. A mistyped candidate therefore cannot open
any resolution once its handle is accepted. Its certificate may remain authentic:
public association or typed guard checks, rather than certification, reject it.
These are operational facts, not a continuation utility comparison.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- Two typed binding references associated to the same actual handle have
identical actors and payloads. This uses the initialized binding invariant. -/
theorem State.BindingInvariant.shared_handle_binding_type
    {state : State graph} (valid : state.BindingInvariant)
    {owner actor : Player} {payload other : L.Ty}
    (original : FieldRef graph.layout (.binding owner payload))
    (later : FieldRef graph.layout (.binding actor other)) (candidate : Handle graph)
    (accepted : state.accepted original.field = some candidate)
    (associated : state.accepted later.field = some candidate) :
    actor = owner ∧ other = payload := by
  have fieldEq := valid.accepted_injective original.field later.field candidate accepted associated
  have originalLayout : graph.layout later.field = .binding owner payload :=
    fieldEq ▸ original.layout_eq
  have kindEq : EventField.binding owner payload = .binding actor other :=
    originalLayout.symm.trans later.layout_eq
  cases kindEq
  exact ⟨rfl, rfl⟩

/-- The actual handler rejects every opening claim on a used mistyped
candidate, including claims with an authentic certificate and different raw data. -/
theorem used_mistyped_candidate_opening_rejected (runtime : EventGraphRuntime graph)
    (state : State graph) (valid : state.BindingInvariant)
    {owner : Player} {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding owner payload)) (candidate : Handle graph)
    (accepted : state.accepted binding.field = some candidate)
    (raw : Raw L) (fixed : state.candidates.lookup candidate = .openable raw)
    (mistyped : raw.as? payload = none)
    (id : MessageId Player) (event : graph.EventId) (claimed : Raw L) :
    handle runtime state ⟨id, .opening event candidate claimed⟩ = none := by
  cases handled : handle runtime state ⟨id, .opening event candidate claimed⟩ with
  | none => rfl
  | some next =>
      have compatible := runtime.handle_matchesNode state next
        ⟨id, .opening event candidate claimed⟩ handled
      cases node : nodeView graph event with
      | bind actor kind outputEq codeEq | sample kind law outputEq codeEq =>
          simp only [Payload.MatchesNode, node] at compatible
      | resolve actor other later checks outputEq codeEq =>
          obtain ⟨_, _, _, _, associated, value, _, actual, _, _⟩ :=
            runtime.handle_opening_at_resolve_facts state next id event candidate claimed actor
              other later checks outputEq codeEq node handled
          have same := (valid.shared_handle_binding_type binding later candidate accepted
            associated).2
          subst other
          have rawEq : raw = ⟨payload, value⟩ :=
            CommitmentCandidate.openable.inj (fixed.symm.trans actual)
          rw [rawEq, Raw.as?_mk] at mistyped
          cases mistyped

omit [DecidableEq Player] in
/-- Opening the actual mistyped raw either fails the public typed guard check
or names a different public binding association. Matching certification is unrestricted. -/
theorem used_mistyped_opening_public_failure
    (state : State graph) (valid : state.BindingInvariant)
    {owner : Player} {payload : L.Ty}
    (original : FieldRef graph.layout (.binding owner payload)) (candidate : Handle graph)
    (accepted : state.accepted original.field = some candidate)
    (raw : Raw L) (mistyped : raw.as? payload = none)
    (event : graph.EventId) (actor : Player) (other : L.Ty)
    (binding : FieldRef graph.layout (.binding actor other))
    (checks : List (GuardCheck graph.layout other))
    (outputEq : graph.outputLayout event = .publication other)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor other binding checks)
    (node : nodeView graph event = .resolve actor other binding checks outputEq codeEq)
    (packet : WitnessedPacket graph) (opened : packet.call = .opening event candidate raw) :
    state.publicView.openingGuardsAccepted packet = false ∨
      state.publicView.accepted binding.field ≠ some candidate := by
  classical
  by_cases same : other = payload
  · left
    subst other
    simp only [PublicView.openingGuardsAccepted, opened, node, mistyped, Option.any_none]
  · right
    intro associated
    exact same (valid.shared_handle_binding_type original binding candidate accepted associated).2

end Vegas.EventGraphRuntime
