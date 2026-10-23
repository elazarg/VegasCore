/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDisclosureResolves

/-! # Successful decoded publications have no failed source reveals -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Decoding a later source point preserves agreement for every cell of the
program's original context. -/
theorem decodeSourcePrefix?_base_agrees {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (point : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count store history =
        some point → refs.Agrees (ProtocolState.base program point) store
  | 0, _, _, program, refs, registry, revelations, outputs, store, history, point, decoded => by
      simp only [decodeSourcePrefix?] at decoded
      obtain ⟨cells, cellsDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
      rw [ProtocolState.base_entry]
      exact decodeState?_agrees refs store cells cellsDecoded
  | count + 1, _, _, program, refs, registry, revelations, outputs, store, history, point,
      decoded => by
      cases program with
      | ret _ => simp [decodeSourcePrefix?] at decoded
      | sample _ _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          intro source
          exact decodeSourcePrefix?_base_agrees count next _ _ _ _ store history rest
            restDecoded (.there source)
      | commit _ _ _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          intro source
          exact decodeSourcePrefix?_base_agrees count next _ _ _ _ store history rest
            restDecoded (.there source)
      | reveal _ _ _ _ _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          intro source
          exact decodeSourcePrefix?_base_agrees count next _ _ _ _ store history rest
            restDecoded (.there source)

/-- Every failed source reveal at a decoded point is reflected in an earlier
publication output. In particular, nonfailed earlier outputs rule it out. -/
theorem not_revealFailed_of_decodeSourcePrefix? {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (point : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count store history =
        some point →
      (∀ event : Fin (eventCount program), event.val < count → ∀ payload
        (outputEq : outputLayout program event = .publication payload),
        cast (congrArg (fun kind : EventGraph.EventField Player L => Option kind.Value) outputEq)
          ((outputs event).get? store) ≠ some .failure) →
      ∀ who, ¬ ProtocolState.RevealFailed who program point
  | 0, _, _, program, refs, registry, revelations, outputs, store, history, point, decoded,
      _clean, who => by
      simp only [decodeSourcePrefix?] at decoded
      obtain ⟨cells, _cellsDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact ProtocolState.not_revealFailed_entry who program _
  | count + 1, _, _, program, refs, registry, revelations, outputs, store, history, point,
      decoded, clean, who => by
      cases program with
      | ret _ => simp [decodeSourcePrefix?] at decoded
      | sample _ _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          apply not_revealFailed_of_decodeSourcePrefix? count next _ _ _ _ store history rest
            restDecoded ?_ who
          intro event earlier payload outputEq
          exact clean event.succ (by simpa using Nat.succ_lt_succ earlier) payload outputEq
      | commit _ _ _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          apply not_revealFailed_of_decodeSourcePrefix? count next _ _ _ _ store history rest
            restDecoded ?_ who
          intro event earlier payload outputEq
          exact clean event.succ (by simpa using Nat.succ_lt_succ earlier) payload outputEq
      | reveal published owner name fresh selected unresolved next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have later := not_revealFailed_of_decodeSourcePrefix? count next _ _ _ _ store history
            rest restDecoded (fun event earlier payload outputEq =>
              clean event.succ (by simpa using Nat.succ_lt_succ earlier) payload outputEq) who
          rintro (⟨_sameOwner, failed⟩ | failed)
          · have agrees := decodeSourcePrefix?_base_agrees count next _ _ _ _ store history rest
              restDecoded HasVar.here
            have noFailure := clean ⟨0, by simp [eventCount]⟩ (by simp) _ rfl
            apply noFailure
            simpa [ContextRefs.cons, cellValue, failed] using agrees
          · exact later failed

end Vegas.SourceProgram
