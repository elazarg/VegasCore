/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCounterpartGuard

/-! # Typed cells read through the native prefix decoder -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  [DecidableEq (CellTy Player L)]

/-- Every original context cell remains readable at a decoded source prefix. -/
theorem decodeSourcePrefix?_context_cell {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (point : ProtocolState program),
      (Γ.map Prod.fst).Nodup →
      decodeSourcePrefix? program refs registry revelations outputs count store history =
        some point →
      ∀ {name kind} (source : HasVar Γ name kind) (value : CellVal L kind),
        (refs.get source).get? store = some (cellValue value) →
        ProtocolState.cell? program point name kind = some value
  | 0, _, _, program, refs, registry, revelations, outputs, store, history, point,
      unique, decoded, name, kind, source, value, read => by
      simp only [decodeSourcePrefix?] at decoded
      obtain ⟨cells, decodedCells, rfl⟩ := Option.map_eq_some_iff.mp decoded
      rw [ProtocolState.cell?_entry, State.cell?_eq_of_hasVar source unique]
      have agree := decodeState?_agrees refs store cells decodedCells source
      rw [read] at agree
      have same : value = cells.get source := by
        cases kind <;> exact Option.some.inj agree
      exact congrArg some same.symm
  | count + 1, _, _, program, refs, registry, revelations, outputs, store, history,
      point, unique, decoded, name, kind, source, value, read => by
      cases program with
      | ret _ => simp [decodeSourcePrefix?] at decoded
      | sample _ fresh _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_context_cell count next _ _ _ _ store history rest
            (List.nodup_cons.mpr ⟨fresh, unique⟩) restDecoded (.there source) value read
      | commit _ _ fresh _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_context_cell count next _ _ _ _ store history rest
            (List.nodup_cons.mpr ⟨fresh, unique⟩) restDecoded (.there source) value read
      | reveal _ _ _ fresh _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_context_cell count next _ _ _ _ store history rest
            (List.nodup_cons.mpr ⟨fresh, unique⟩) restDecoded (.there source) value read

/-- Every output already passed by the decoder remains in its source cells. -/
theorem decodeSourcePrefix?_output_cell {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (point : ProtocolState program),
      (Γ.map Prod.fst).Nodup →
      decodeSourcePrefix? program refs registry revelations outputs count store history =
        some point →
      ∀ (event : Fin (eventCount program)), event.val < count →
      ∀ (value : CellVal L (eventCell program event).2),
        (outputs event).get? store = some (cast
          (congrArg EventGraph.EventField.Value (outputLayout_eventCell program event).symm)
          (cellValue value)) →
        ProtocolState.cell? program point (eventCell program event).1
          (eventCell program event).2 = some value
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, event, earlier, value, read => by omega
  | count + 1, _, _, program, refs, registry, revelations, outputs, store, history,
      point, unique, decoded, event, earlier, value, read => by
      cases program with
      | ret _ => exact Fin.elim0 event
      | sample _ fresh _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          cases event using Fin.cases with
          | zero =>
              exact decodeSourcePrefix?_context_cell count next _ _ _ _ store history rest
                (List.nodup_cons.mpr ⟨fresh, unique⟩) restDecoded .here value read
          | succ event =>
              exact decodeSourcePrefix?_output_cell count next _ _ _ _ store history rest
                (List.nodup_cons.mpr ⟨fresh, unique⟩) restDecoded event
                (by simpa using earlier) value read
      | commit _ _ fresh _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          cases event using Fin.cases with
          | zero =>
              exact decodeSourcePrefix?_context_cell count next _ _ _ _ store history rest
                (List.nodup_cons.mpr ⟨fresh, unique⟩) restDecoded .here value read
          | succ event =>
              exact decodeSourcePrefix?_output_cell count next _ _ _ _ store history rest
                (List.nodup_cons.mpr ⟨fresh, unique⟩) restDecoded event
                (by simpa using earlier) value read
      | reveal _ _ _ fresh _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          cases event using Fin.cases with
          | zero =>
              exact decodeSourcePrefix?_context_cell count next _ _ _ _ store history rest
                (List.nodup_cons.mpr ⟨fresh, unique⟩) restDecoded .here value read
          | succ event =>
              exact decodeSourcePrefix?_output_cell count next _ _ _ _ store history rest
                (List.nodup_cons.mpr ⟨fresh, unique⟩) restDecoded event
                (by simpa using earlier) value read

end Vegas.SourceProgram
