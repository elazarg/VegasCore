/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketForced

/-! # Failures in typed source prefix readouts

Typed decoding retains the public default history and records failed binding
and publication cells at their source positions. These properties concern the
stored result independently of the requested graph action.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- No reveal has failed at a program's entry. -/
theorem not_revealFailed_entry (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    ¬ RevealFailed who program (entry program config) := by
  cases program <;> exact fun failed => failed

end ProtocolState

/-- Decoding a later source point preserves agreement for every cell of the
program's original context. -/
theorem decodeSourcePrefix?_base_agrees {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (defaults : DefaultHistory Player)
      (point : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count
        store history defaults =
        some point → refs.Agrees (ProtocolState.base program point) store
  | 0, _, _, program, refs, registry, revelations, outputs, store, history, defaults, point,
      decoded => by
      simp only [decodeSourcePrefix?] at decoded
      obtain ⟨cells, cellsDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
      rw [ProtocolState.base_entry]
      exact decodeState?_agrees refs store cells cellsDecoded
  | count + 1, _, _, program, refs, registry, revelations, outputs, store, history, defaults, point,
      decoded => by
      cases program with
      | ret _ => simp [decodeSourcePrefix?] at decoded
      | sample _ _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          intro source
          exact decodeSourcePrefix?_base_agrees count next _ _ _ _ store history defaults rest
            restDecoded (.there source)
      | commit _ _ _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          intro source
          exact decodeSourcePrefix?_base_agrees count next _ _ _ _ store history defaults rest
            restDecoded (.there source)
      | reveal _ _ _ _ _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          intro source
          exact decodeSourcePrefix?_base_agrees count next _ _ _ _ store history defaults rest
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
      (defaults : DefaultHistory Player)
      (point : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count
        store history defaults =
        some point →
      (∀ event : Fin (eventCount program), event.val < count → ∀ payload
        (outputEq : outputLayout program event = .publication payload),
        cast (congrArg (fun kind : EventGraph.EventField Player L => Option kind.Value) outputEq)
          ((outputs event).get? store) ≠ some .failure) →
      ∀ who, ¬ ProtocolState.RevealFailed who program point
  | 0, _, _, program, refs, registry, revelations, outputs, store, history, defaults, point,
      decoded,
      _clean, who => by
      simp only [decodeSourcePrefix?] at decoded
      obtain ⟨cells, _cellsDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact ProtocolState.not_revealFailed_entry who program _
  | count + 1, _, _, program, refs, registry, revelations, outputs, store, history, defaults, point,
      decoded, clean, who => by
      cases program with
      | ret _ => simp [decodeSourcePrefix?] at decoded
      | sample _ _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          apply not_revealFailed_of_decodeSourcePrefix? count next _ _ _ _ store history defaults
            rest
            restDecoded ?_ who
          intro event earlier payload outputEq
          exact clean event.succ (by simpa using Nat.succ_lt_succ earlier) payload outputEq
      | commit _ _ _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          apply not_revealFailed_of_decodeSourcePrefix? count next _ _ _ _ store history defaults
            rest
            restDecoded ?_ who
          intro event earlier payload outputEq
          exact clean event.succ (by simpa using Nat.succ_lt_succ earlier) payload outputEq
      | reveal published owner name fresh selected unresolved next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have later := not_revealFailed_of_decodeSourcePrefix? count next _ _ _ _ store history
            defaults rest restDecoded (fun event earlier payload outputEq =>
              clean event.succ (by simpa using Nat.succ_lt_succ earlier) payload outputEq) who
          rintro (⟨_sameOwner, failed⟩ | failed)
          · have agrees := decodeSourcePrefix?_base_agrees count next _ _ _ _ store history
              defaults rest restDecoded HasVar.here
            have noFailure := clean ⟨0, by simp [eventCount]⟩ (by simp) _ rfl
            apply noFailure
            simpa [ContextRefs.cons, cellValue, failed] using agrees
          · exact later failed

namespace ProtocolState

/-- **A stored failed publication is a failed reveal.** A point decoded past a
reveal of `who` whose stored publication is a failure shows `who`'s reveal
failed. -/
theorem revealFailed_of_decode_failure {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (defaults : DefaultHistory Player)
      (state : ProtocolState program) (bound : count < eventCount program) (who : Player)
      (payload : L.Ty) (publication : outputLayout program ⟨count, bound⟩ = .publication payload),
      decodeSourcePrefix? program refs registry revelations outputs (count + 1)
        store history defaults =
          some state →
      eventOwner? program ⟨count, bound⟩ = some who →
      (outputs ⟨count, bound⟩).get? store = some (cast
        (congrArg EventGraph.EventField.Value publication.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload))) →
      RevealFailed who program state := by
  induction program with
  | ret _ =>
      intro count _ _ _ _ _ _ _ _ bound
      simp [eventCount] at bound
  | sample _ fresh _ next ih =>
      intro count refs registry revelations outputs store history defaults state bound who payload
        publication decoded owned read
      cases count with
      | zero => cases publication
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact ih count _ _ _ _ store history defaults rest (Nat.lt_of_succ_lt_succ bound) who
            payload publication restDecoded owned read
  | commit name owner fresh guard next ih =>
      intro count refs registry revelations outputs store history defaults state bound who payload
        publication decoded owned read
      cases count with
      | zero => cases publication
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact ih count _ _ _ _ store history defaults rest (Nat.lt_of_succ_lt_succ bound) who
            payload publication restDecoded owned read
  | reveal published owner name fresh source unresolved next ih =>
      intro count refs registry revelations outputs store history defaults state bound who payload
        publication decoded owned read
      cases count with
      | zero =>
          cases Option.some.inj owned
          cases publication
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          obtain ⟨cells, cellsDecoded, rfl⟩ := Option.map_eq_some_iff.mp restDecoded
          refine Or.inl ⟨rfl, ?_⟩
          rw [base_entry]
          unfold decodeState? at cellsDecoded
          erw [read] at cellsDecoded
          obtain ⟨head, headEq, rest⟩ := Option.bind_eq_some_iff.mp cellsDecoded
          obtain ⟨tail, _, cellsEq⟩ := Option.bind_eq_some_iff.mp rest
          cases Option.some.inj headEq
          cases Option.some.inj cellsEq
          rfl
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact Or.inr (ih count _ _ _ _ store history defaults rest
            (Nat.lt_of_succ_lt_succ bound) who payload publication restDecoded owned read)


/-- A failed binding cell at its completed source position is an unresolved
failed binding, independently of the requested graph action. -/
theorem failedBinding_of_decode_failure {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (_unique : (Γ.map Prod.fst).Nodup) (count : Nat) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (defaults : DefaultHistory Player)
      (state : ProtocolState program) (bound : count < eventCount program) (who : Player)
      (payload : L.Ty) (binding : outputLayout program ⟨count, bound⟩ = .binding who payload),
      decodeSourcePrefix? program refs registry revelations outputs (count + 1)
        store history defaults = some state →
      eventOwner? program ⟨count, bound⟩ = some who →
      (outputs ⟨count, bound⟩).get? store = some (cast
        (congrArg EventGraph.EventField.Value binding.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload))) →
      FailedBinding who program state := by
  induction program with
  | ret _ =>
      intro _ count _ _ _ _ _ _ _ _ bound
      simp [eventCount] at bound
  | sample name fresh law next ih =>
      intro unique count refs registry revelations outputs store history defaults state bound who
        payload binding decoded owned read
      cases count with
      | zero => cases binding
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact ih (List.nodup_cons.mpr ⟨fresh, unique⟩) count _ _ _ _ store history defaults rest
            (Nat.lt_of_succ_lt_succ bound) who payload binding restDecoded owned read
  | commit name owner fresh guard next ih =>
      intro unique count refs registry revelations outputs store history defaults state bound who
        payload binding decoded owned read
      cases count with
      | zero =>
          cases Option.some.inj owned
          cases binding
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          obtain ⟨cells, cellsDecoded, rfl⟩ := Option.map_eq_some_iff.mp restDecoded
          apply failedBinding_entry
          refine ⟨List.nodup_cons.mpr ⟨fresh, unique⟩,
            name, _, .here, Finset.mem_insert_self _ _, ?_⟩
          unfold decodeState? at cellsDecoded
          erw [read] at cellsDecoded
          obtain ⟨head, headEq, rest⟩ := Option.bind_eq_some_iff.mp cellsDecoded
          obtain ⟨tail, _, cellsEq⟩ := Option.bind_eq_some_iff.mp rest
          cases Option.some.inj headEq
          cases Option.some.inj cellsEq
          rfl
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact ih (List.nodup_cons.mpr ⟨fresh, unique⟩) count _ _ _ _ store history defaults rest
            (Nat.lt_of_succ_lt_succ bound) who payload binding restDecoded owned read
  | reveal published owner name fresh source unresolved next ih =>
      intro unique count refs registry revelations outputs store history defaults state bound who
        payload binding decoded owned read
      cases count with
      | zero => cases binding
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact Or.inr (ih (List.nodup_cons.mpr ⟨fresh, unique⟩) count _ _ _ _ store history
            defaults rest (Nat.lt_of_succ_lt_succ bound) who payload binding restDecoded owned read)

end ProtocolState

end Vegas.SourceProgram
