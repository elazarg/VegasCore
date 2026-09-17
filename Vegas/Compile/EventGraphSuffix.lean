/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphAssembly

/-! # Node-table agreement for compiled source suffixes

This module records the small dependent-transport fact needed when a proof
recurses through a source program while continuing to execute the one graph
compiled from the whole program.  It is deliberately only a node-table
certificate; it assumes no execution or distributional correspondence.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- A residual source program's generic lowering is exactly the corresponding
slice of one fixed compiled graph.  The cast is the unavoidable transport from
the whole graph's output layout to the residual program's output layout. -/
structure CompiledSuffix
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (refs : ContextRefs (graphLayout whole) Γ)
    (revelations : Revelations Γ)
    (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
    (refsBefore : ContextRefsBefore refs embedding)
    (offset : Nat) : Prop where
  countEq : offset + eventCount program = eventCount whole
  rankEq : ∀ index, (embedding.event index).val = offset + index.val
  nodeEq : ∀ index,
    cast (congrArg (Vegas.EventGraph.EventCode (graphLayout whole))
        (embedding.layout_eq index))
      ((toEventGraph whole).nodes (embedding.event index)) =
      (compileRankedNodes program refs revelations registry embedding
        refsBefore index).code

/-- The complete program is its own initial compiled suffix. -/
theorem CompiledSuffix.whole
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) :
    CompiledSuffix program program
      (ContextRefs.initial Γ (outputLayout program)) (Revelations.initial Γ) []
      (outputEmbedding program) (initialRefsBefore program) 0 := by
  constructor
  · simp
  · intro index
    simp [outputEmbedding]
  · intro index
    rfl

/-- Advance a compiled-suffix certificate across a sampling node.  The state
in the conclusion is definitionally the state used by `compileRankedNodes`'s
sampling branch. -/
theorem CompiledSuffix.sampleTail
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    {Γ : SourceCtx Player L} {_openNames nextOpen : Finset VarId}
    {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: Γ) nextOpen)
    (refs : ContextRefs (graphLayout whole) Γ)
    (revelations : Revelations Γ)
    (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.sample name fresh law next))
    (refsBefore : ContextRefsBefore refs embedding)
    (offset : Nat)
    (suffix : CompiledSuffix whole (.sample name fresh law next)
      refs revelations registry embedding refsBefore offset) :
    let headIndex : Fin (eventCount (.sample name fresh law next)) :=
      ⟨0, by simp [eventCount]⟩
    let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
    let tailRefs := refs.cons (embedding.ref headIndex)
    let tailRefsBefore : ContextRefsBefore tailRefs tailEmbedding := by
      intro readName cell source remaining
      cases source with
      | here =>
          change (embedding.event headIndex).val <
            (embedding.event (Fin.succ remaining)).val
          apply embedding.strictMono
          exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
      | there source => exact refsBefore source (Fin.succ remaining)
    CompiledSuffix whole next tailRefs
      revelations.weaken registry.weaken tailEmbedding tailRefsBefore (offset + 1) := by
  dsimp only
  constructor
  · simpa [eventCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      suffix.countEq
  · intro index
    change (embedding.event (Fin.succ index)).val = offset + 1 + index.val
    calc
      _ = offset + (Fin.succ index).val := suffix.rankEq (Fin.succ index)
      _ = offset + 1 + index.val := by
        simp [Fin.val_succ, Nat.add_comm, Nat.add_left_comm]
  · intro index
    simpa [OutputEmbedding.tail, compileRankedNodes, eventCount, outputLayout] using
      suffix.nodeEq (Fin.succ index)

/-- Advance a compiled-suffix certificate across a binding node. -/
theorem CompiledSuffix.commitTail
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .privateData owner payload) :: Γ)
      (insert name openNames))
    (refs : ContextRefs (graphLayout whole) Γ)
    (revelations : Revelations Γ)
    (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding)
    (offset : Nat)
    (suffix : CompiledSuffix whole (.commit name owner fresh guard next)
      refs revelations registry embedding refsBefore offset) :
    let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let obligation : Obligation _ :=
      { owner := owner, subject := name, payload := payload, source := .here,
        guard := guard.weaken }
    let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
    let tailRefs := refs.cons (embedding.ref headIndex)
    let tailRefsBefore : ContextRefsBefore tailRefs tailEmbedding := by
      intro readName cell source remaining
      cases source with
      | here =>
          change (embedding.event headIndex).val <
            (embedding.event (Fin.succ remaining)).val
          apply embedding.strictMono
          exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
      | there source => exact refsBefore source (Fin.succ remaining)
    CompiledSuffix whole next tailRefs
      revelations.weaken (obligation :: registry.weaken) tailEmbedding tailRefsBefore
      (offset + 1) := by
  dsimp only
  constructor
  · simpa [eventCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      suffix.countEq
  · intro index
    change (embedding.event (Fin.succ index)).val = offset + 1 + index.val
    calc
      _ = offset + (Fin.succ index).val := suffix.rankEq (Fin.succ index)
      _ = offset + 1 + index.val := by
        simp [Fin.val_succ, Nat.add_comm, Nat.add_left_comm]
  · intro index
    simpa [OutputEmbedding.tail, compileRankedNodes, eventCount, outputLayout] using
      suffix.nodeEq (Fin.succ index)

/-- Advance a compiled-suffix certificate across a resolution node. -/
theorem CompiledSuffix.revealTail
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.privateData owner payload))
    (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (refs : ContextRefs (graphLayout whole) Γ)
    (revelations : Revelations Γ)
    (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.reveal published owner name fresh selected unresolved next))
    (refsBefore : ContextRefsBefore refs embedding)
    (offset : Nat)
    (suffix : CompiledSuffix whole
      (.reveal published owner name fresh selected unresolved next)
      refs revelations registry embedding refsBefore offset) :
    let headIndex : Fin (eventCount
        (.reveal published owner name fresh selected unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let resultRef : Vegas.EventGraph.FieldRef (graphLayout whole)
        (.publication payload) := by
      simpa [headIndex, outputLayout, eventCount] using embedding.ref headIndex
    let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
    let tailRefs := refs.cons resultRef
    let tailRefsBefore : ContextRefsBefore tailRefs tailEmbedding := by
      intro readName cell source remaining
      cases source with
      | here =>
          change (embedding.event headIndex).val <
            (embedding.event (Fin.succ remaining)).val
          apply embedding.strictMono
          exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
      | there source => exact refsBefore source (Fin.succ remaining)
    CompiledSuffix whole next tailRefs
      (revelations.reveal (published := published) selected) registry.weaken tailEmbedding
      tailRefsBefore (offset + 1) := by
  dsimp only
  constructor
  · simpa [eventCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      suffix.countEq
  · intro index
    change (embedding.event (Fin.succ index)).val = offset + 1 + index.val
    calc
      _ = offset + (Fin.succ index).val := suffix.rankEq (Fin.succ index)
      _ = offset + 1 + index.val := by
        simp [Fin.val_succ, Nat.add_comm, Nat.add_left_comm]
  · intro index
    simpa [OutputEmbedding.tail, compileRankedNodes, eventCount, outputLayout] using
      suffix.nodeEq (Fin.succ index)

end Vegas.SourceProgram.EventLowering
