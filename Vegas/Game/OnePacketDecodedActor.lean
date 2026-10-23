/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketIntendedProjection

/-! # The actor at a decoded point

A source state decoded at a prefix of length `count` sits at the instruction of
rank `count`, so its source actor is the owner of that instruction
(`Vegas.decodeSourcePrefix?_actor`). Hence at a native configuration with a
ready event, the source actor at the decoded point is the graph actor of the
ready event (`Vegas.decodedPoint_actor`).
-/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **The actor at a decoded state** is the owner of the instruction of the
decoded rank. -/
theorem decodeSourcePrefix?_actor (who : Player) {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} : ∀ (count : Nat)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (refs : ContextRefs layout Γ) (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (store : EventGraph.Store layout) (history : History Player L) (state : ProtocolState program),
    decodeSourcePrefix? program refs registry revelations outputs count store history =
      some state →
    (inside : count < eventCount program) →
      ProtocolView.actor who program (ProtocolState.observe who program state) =
        eventOwner? program ⟨count, inside⟩
  | 0, _, _, program, refs, registry, revelations, outputs, store, history, state, decoded,
      inside => by
      cases program with
      | ret _ => simp [eventCount] at inside
      | sample _ _ _ next =>
          obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          rfl
      | commit _ _ _ _ next =>
          obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          rfl
      | reveal _ _ _ _ _ _ next =>
          obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          rfl
  | count + 1, _, _, program, refs, registry, revelations, outputs, store, history, state,
      decoded, inside => by
      cases program with
      | ret _ => cases decoded
      | sample _ _ _ next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_actor who count next _ _ _ _ store history rest restDecoded
            (by simpa [eventCount] using inside)
      | commit _ _ _ _ next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_actor who count next _ _ _ _ store history rest restDecoded
            (by simpa [eventCount] using inside)
      | reveal _ _ _ _ _ _ next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_actor who count next _ _ _ _ store history rest restDecoded
            (by simpa [eventCount] using inside)

/-- **The actor at a decoded point** of a native configuration with a ready
event is the graph actor of that event. -/
theorem decodedPoint_actor {setup : Setup (Player := Player) (L := L)} (who : Player)
    {config : (graph setup).Config} {event : (graph setup).EventId}
    (ready : config.cut.Ready event) {point : ProtocolState setup.program}
    (decoded : decodedPoint setup config = some point) :
    ProtocolView.actor who setup.program (ProtocolState.observe who setup.program point) =
      (graph setup).actor? event := by
  unfold decodedPoint at decoded
  split at decoded
  · rename_i ordered
    have rank := (ready_iff_rank setup config _ ordered.choose_spec event).mp ready
    have inside : ordered.choose < eventCount setup.program := rank ▸ event.isLt
    have actor := decodeSourcePrefix?_actor who ordered.choose setup.program _ _ _ _ _ _ point
      decoded inside
    rw [actor, eventOwner?_eq_actor]
    have same : event = ⟨ordered.choose, inside⟩ := Fin.ext rank
    subst same
    rfl
  · cases decoded

end Vegas
