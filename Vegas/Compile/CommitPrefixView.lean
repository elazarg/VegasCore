/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.CommitPrefixCompletion
import Vegas.Compile.EventSourceView

/-! # Source protocol views at the end of a filled commitment initial segment -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO)

/-- The source syntax decoder at the first suffix event returns exactly the
view of the original protocol point after the earlier typed commitments. -/
theorem decodeEventView?_commitPrefix_entry
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (refs : ContextRefs (graphLayout whole) Γ)
    (store : Store (graphLayout whole)) (finished : SourceProgram.Config Player L Δ)
    (who : Player) (selected : Fin (eventCount (block.prepend suffix)))
    (atEnd : selected.val = block.length)
    (decoded : decodeObservation? who (commitBlockRefs whole block suffix embedding refs) store =
      some (sourceObserve who finished.state)) :
    decodeEventView? (block.prepend suffix) refs embedding.ref who selected store
      (finished.history who) = some (ProtocolState.observe who (block.prepend suffix)
        (block.liftPoint suffix (ProtocolState.entry suffix finished))) := by
  induction block with
  | nil =>
      change decodeEventView? suffix refs embedding.ref who selected store
        (finished.history who) =
          some (ProtocolState.observe who suffix (ProtocolState.entry suffix finished))
      change decodeObservation? who refs store = some (sourceObserve who finished.state) at decoded
      have zero : selected.val = 0 := atEnd
      cases suffix with
      | ret => exact Fin.elim0 selected
      | sample name fresh law next =>
          have same : selected = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext zero
          subst selected
          change (decodeObservation? who refs store).map (fun observation =>
            Sum.inl (observation, finished.history who)) = _
          rw [decoded]
          rfl
      | commit name owner fresh guard next =>
          have same : selected = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext zero
          subst selected
          change (decodeObservation? who refs store).map (fun observation =>
            Sum.inl (observation, finished.history who)) = _
          rw [decoded]
          rfl
      | reveal published owner name fresh source unresolved next =>
          have same : selected = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext zero
          subst selected
          change (decodeObservation? who refs store).map (fun observation =>
            Sum.inl (observation, finished.history who)) = _
          rw [decoded]
          rfl
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      refine Fin.cases ?_ ?_ selected atEnd
      · intro impossible
        simp only [Fin.val_zero, CommitPrefix.length] at impossible
        omega
      · intro index atEnd
        let zero : Fin (eventCount ((CommitPrefix.commit name owner fresh guard rest).prepend
            suffix)) := ⟨0, by simp only [CommitPrefix.prepend, eventCount]; omega⟩
        let later := embedding.tail (rest.prepend suffix) (by
          simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
        let field : FieldRef (graphLayout whole) (.binding owner payload) := by
          simpa only [zero, CommitPrefix.prepend, outputLayout, Fin.mk_zero, Fin.cases_zero] using
            embedding.ref zero
        have nextEnd : index.val = rest.length := by
          simp only [Fin.val_succ, CommitPrefix.length] at atEnd
          omega
        have result := ih suffix later
          (refs.cons (name := name) (cell := .commitment owner payload) field) finished index
          nextEnd decoded
        change (decodeEventView? (rest.prepend suffix)
          (refs.cons (name := name) (cell := .commitment owner payload) field) later.ref who
          index store (finished.history who)).map Sum.inr =
            some (Sum.inr (ProtocolState.observe who (rest.prepend suffix)
              (rest.liftPoint suffix (ProtocolState.entry suffix finished))))
        exact congrArg (Option.map Sum.inr) result

end Vegas
