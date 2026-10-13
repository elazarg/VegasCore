/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePrefix
import Vegas.Source.CellSwap

/-! # Decoding commutes with corresponding swaps

A map of graph stores *corresponds* to a cell swap at a field reference of a
cell kind when reading the reference from a mapped store reads the swapped
value of the cell (`Vegas.SourceProgram.CellSwap.FieldCorr`). When every
context reference corresponds to the swap of its cell and every output
reference of the program corresponds to the swap of the cell its event binds,
decoding a mapped store with swapped action lists decodes to the swapped
program point (`Vegas.decodeSourcePrefix?_swap`).
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace CellSwap

variable (swap : CellSwap Player L)

/-- The swap of a cell, read as a value of the graph field of its kind. -/
def field (name : VarId) : (kind : CellTy Player L) → (cellField kind).Value →
    (cellField kind).Value
  | .publicData payload => swap.cell name (.publicData payload)
  | .privateInput owner payload => swap.cell name (.privateInput owner payload)
  | .commitment owner payload => swap.cell name (.commitment owner payload)
  | .publication payload => swap.cell name (.publication payload)

variable {Field : Type} [DecidableEq Field] {layout : Field → EventGraph.EventField Player L}

/-- A store map *corresponds* to the swap at a reference of a cell kind. -/
def FieldCorr (storeMap : EventGraph.Store layout → EventGraph.Store layout) (name : VarId)
    (kind : CellTy Player L) (ref : EventGraph.FieldRef layout (cellField kind)) : Prop :=
  ∀ store, ref.get? (storeMap store) = (ref.get? store).map (swap.field name kind)

/-- Every context reference corresponds to the swap of its cell. -/
def RefsCorr (storeMap : EventGraph.Store layout → EventGraph.Store layout)
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ) : Prop :=
  ∀ {name kind} (source : HasVar Γ name kind), swap.FieldCorr storeMap name kind (refs.get source)

/-- Every output reference corresponds to the swap of the cell its event binds. -/
def OutputsCorr (storeMap : EventGraph.Store layout → EventGraph.Store layout) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (∀ event, EventGraph.FieldRef layout (outputLayout program event)) → Prop
  | _, _, .ret _, _ => True
  | _, _, .sample (payload := payload) name _ _ next, outputs =>
      swap.FieldCorr storeMap name (.publicData payload) (outputs ⟨0, Nat.succ_pos _⟩) ∧
        OutputsCorr storeMap next (fun tail => outputs tail.succ)
  | _, _, .commit (payload := payload) name owner _ _ next, outputs =>
      swap.FieldCorr storeMap name (.commitment owner payload)
          (outputs ⟨0, Nat.succ_pos _⟩) ∧
        OutputsCorr storeMap next (fun tail => outputs tail.succ)
  | _, _, .reveal (payload := payload) published _ _ _ _ _ next, outputs =>
      swap.FieldCorr storeMap published (.publication payload)
          (outputs ⟨0, Nat.succ_pos _⟩) ∧
        OutputsCorr storeMap next (fun tail => outputs tail.succ)

omit [DecidableEq Player] [IExpr.ResultTypes L] [DecidableEq Field] in
theorem refsCorr_cons (storeMap : EventGraph.Store layout → EventGraph.Store layout)
    {Γ : SourceCtx Player L} {refs : ContextRefs layout Γ} {name : VarId}
    {kind : CellTy Player L} {head : EventGraph.FieldRef layout (cellField kind)}
    (headCorr : swap.FieldCorr storeMap name kind head) (tailCorr : swap.RefsCorr storeMap refs) :
    swap.RefsCorr storeMap (ContextRefs.cons (name := name) head refs) := by
  intro otherName otherKind source
  cases source with
  | here => exact headCorr
  | there source => exact tailCorr source

omit [DecidableEq Player] [IExpr.ResultTypes L] [DecidableEq Field] in
/-- **Reading a state commutes with corresponding swaps.** -/
theorem decodeState?_swap (storeMap : EventGraph.Store layout → EventGraph.Store layout) :
    ∀ {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ), swap.RefsCorr storeMap refs →
      ∀ store, decodeState? refs (storeMap store) = (decodeState? refs store).map swap.state
  | [], _, _, _ => by
      simp only [decodeState?, Option.map_some]
      congr 1
      funext name kind source
      nomatch source
  | (name, kind) :: Γ, refs, corr, store => by
      have tailCorr : swap.RefsCorr storeMap refs.tail := fun source => corr (.there source)
      have recursive := decodeState?_swap storeMap refs.tail tailCorr store
      have headEq := corr (.here : HasVar ((name, kind) :: Γ) name kind) store
      have consEq : ∀ (head : CellVal L kind) (tail : State L Γ),
          (Env.cons (swap.cell name kind head) (swap.state tail) : State L ((name, kind) :: Γ)) =
            swap.state (Env.cons head tail) := by
        intro head tail
        funext otherName otherKind source
        cases source <;> rfl
      cases kind with
      | publicData payload =>
          simp only [decodeState?]
          rw [headEq, recursive]
          cases (refs.get .here).get? store <;> cases decodeState? refs.tail store <;>
            simp [consEq, field]
      | publication payload =>
          simp only [decodeState?]
          rw [headEq, recursive]
          cases (refs.get .here).get? store <;> cases decodeState? refs.tail store <;>
            simp [consEq, field]
      | commitment owner payload =>
          simp only [decodeState?]
          rw [headEq, recursive]
          cases (refs.get .here).get? store <;> cases decodeState? refs.tail store <;>
            simp [consEq, field]
      | privateInput owner payload =>
          simp only [decodeState?]
          rw [headEq, recursive]
          cases (refs.get .here).get? store <;> cases decodeState? refs.tail store <;>
            simp [consEq, field]

end CellSwap

end Vegas.SourceProgram

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **Decoding commutes with corresponding swaps.** -/
theorem decodeSourcePrefix?_swap (swap : CellSwap Player L) {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L}
    (storeMap : EventGraph.Store layout → EventGraph.Store layout) :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event)),
      swap.RefsCorr storeMap refs → swap.OutputsCorr storeMap program outputs →
      ∀ store history,
      decodeSourcePrefix? program refs registry revelations outputs count (storeMap store)
          (swap.history history) =
        (decodeSourcePrefix? program refs registry revelations outputs count store
          history).map (swap.protocolState program)
  | 0, _, _, program, refs, registry, revelations, outputs, refsCorr, _, store, history => by
      simp only [decodeSourcePrefix?]
      rw [swap.decodeState?_swap storeMap refs refsCorr store]
      cases decodeState? refs store with
      | none => rfl
      | some state =>
          simp only [Option.map_some, CellSwap.protocolState_entry]
          rfl
  | count + 1, _, _, .ret _, _, _, _, _, _, _, _, _ => rfl
  | count + 1, _, _, .sample name fresh law next, refs, registry, revelations, outputs,
      refsCorr, outputsCorr, store, history => by
      rw [decodeSourcePrefix?_sample, decodeSourcePrefix?_sample,
        decodeSourcePrefix?_swap swap storeMap count next _ _ _ _
          (swap.refsCorr_cons storeMap outputsCorr.1 refsCorr) outputsCorr.2, Option.map_map,
        Option.map_map]
      rfl
  | count + 1, _, _, .commit name owner fresh guard next, refs, registry, revelations, outputs,
      refsCorr, outputsCorr, store, history => by
      rw [decodeSourcePrefix?_commit, decodeSourcePrefix?_commit,
        decodeSourcePrefix?_swap swap storeMap count next _ _ _ _
          (swap.refsCorr_cons storeMap outputsCorr.1 refsCorr) outputsCorr.2, Option.map_map,
        Option.map_map]
      rfl
  | count + 1, _, _, .reveal published owner name fresh selected unresolved next, refs,
      registry, revelations, outputs, refsCorr, outputsCorr, store, history => by
      rw [decodeSourcePrefix?_reveal, decodeSourcePrefix?_reveal,
        decodeSourcePrefix?_swap swap storeMap count next _ _ _ _
          (swap.refsCorr_cons storeMap outputsCorr.1 refsCorr) outputsCorr.2, Option.map_map,
        Option.map_map]
      rfl

end Vegas
