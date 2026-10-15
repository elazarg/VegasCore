/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitPrefixSnoc
import Vegas.Compile.CommitPrefixCompletion

/-! # Exact physical completion at the final commitment of a telescope -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO)

/-- Casting source syntax preserves the physical event at every equal index. -/
theorem OutputEmbedding.event_cast {Γ : SourceCtx Player L} {O : Finset VarId}
    {first second : SourceProgram Player L Γ O} (same : first = second)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) first)
    (left : Fin (eventCount first)) (right : Fin (eventCount second))
    (coordinate : left.val = right.val) :
    embedding.event left = (cast (congrArg (fun program =>
      OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program) same) embedding).event
        right := by
  cases same
  have equal : left = right := Fin.ext coordinate
  subst right
  rfl

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem fieldRef_eq_of_field_eq {Field : Type}
    {layout : Field → EventField Player L} {kind : EventField Player L}
    (first second : FieldRef layout kind) (same : first.field = second.field) : first = second := by
  rcases first with ⟨left, leftLayout⟩
  rcases second with ⟨right, rightLayout⟩
  dsimp only at same
  subst right
  rfl

private theorem fill_snoc_of_events
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (name : VarId) (owner : Player) {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (full : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      ((block.snoc name owner fresh guard).prepend next))
    (prefixEmbedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend (.commit name owner fresh guard next)))
    (same : ∀ left right, left.val = right.val → full.event left = prefixEmbedding.event right)
    (store : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ)
    (field : FieldRef (graphLayout whole) (.binding owner payload))
    (selected : Fin (eventCount (block.prepend (.commit name owner fresh guard next))))
    (atEnd : selected.val = block.length)
    (named : field.field = .inr (prefixEmbedding.event selected)) :
    fillCommitPrefix whole (block.snoc name owner fresh guard) next full store entry =
      commitSuccessor name guard
        (fillCommitPrefix whole block (.commit name owner fresh guard next) prefixEmbedding
          store entry)
        ((field.get? store).getD .failure) := by
  induction block with
  | nil =>
      have zero : selected = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext atEnd
      rcases zero with rfl
      let firstIndex : Fin (eventCount ((CommitPrefix.nil.snoc name owner fresh guard).prepend
          next)) := ⟨0, Nat.zero_lt_succ _⟩
      let first : FieldRef (graphLayout whole) (.binding owner payload) :=
        ⟨.inr (full.event firstIndex), full.layout_eq _⟩
      have equal : first = field := by
        have coordinates : first.field = field.field :=
          (congrArg Sum.inr (same _ _ rfl)).trans named.symm
        exact fieldRef_eq_of_field_eq first field coordinates
      change commitSuccessor name guard entry ((first.get? store).getD .failure) = _
      rw [equal]
      rfl
  | @commit Γ O Δ P prior author value priorFresh priorGuard rest ih =>
      refine Fin.cases ?_ ?_ selected atEnd named
      · intro impossible _named
        change 0 = rest.length + 1 at impossible
        omega
      · intro index atEnd named
        let fullZero : Fin (eventCount
            (((CommitPrefix.commit prior author priorFresh priorGuard rest).snoc name owner
              fresh guard).prepend next)) := ⟨0, by
          simp only [CommitPrefix.snoc, CommitPrefix.prepend, eventCount]; omega⟩
        let partialZero : Fin (eventCount
            ((CommitPrefix.commit prior author priorFresh priorGuard rest).prepend
              (.commit name owner fresh guard next))) := ⟨0, by
          simp only [CommitPrefix.prepend, eventCount]; omega⟩
        let fullField : FieldRef (graphLayout whole) (.binding author value) :=
          ⟨.inr (full.event fullZero), full.layout_eq _⟩
        let partialField : FieldRef (graphLayout whole) (.binding author value) :=
          ⟨.inr (prefixEmbedding.event partialZero), prefixEmbedding.layout_eq _⟩
        have headEq : fullField = partialField := by
          have coordinates : fullField.field = partialField.field :=
            congrArg Sum.inr (same fullZero partialZero rfl)
          exact fieldRef_eq_of_field_eq fullField partialField coordinates
        let fullTail := full.tail ((rest.snoc name owner fresh guard).prepend next)
          (by simp only [CommitPrefix.snoc, CommitPrefix.prepend, eventCount]) (fun _ => rfl)
        let partialTail := prefixEmbedding.tail (rest.prepend (.commit name owner fresh guard next))
          (by simp only [CommitPrefix.prepend, eventCount]) (fun _ => rfl)
        have tailSame : ∀ left right, left.val = right.val →
            fullTail.event left = partialTail.event right := by
          intro left right equal
          exact same (Fin.succ left) (Fin.succ right) (congrArg Nat.succ equal)
        have nextEnd : index.val = rest.length := by
          change index.val + 1 = rest.length + 1 at atEnd
          omega
        change fillCommitPrefix whole (rest.snoc name owner fresh guard) next fullTail store
            (commitSuccessor prior priorGuard entry ((fullField.get? store).getD .failure)) =
          commitSuccessor name guard (fillCommitPrefix whole rest
            (.commit name owner fresh guard next) partialTail store
              (commitSuccessor prior priorGuard entry ((partialField.get? store).getD .failure)))
            ((field.get? store).getD .failure)
        rw [headEq]
        exact ih fresh guard next fullTail partialTail tailSame
          (commitSuccessor prior priorGuard entry ((partialField.get? store).getD .failure))
            index nextEnd named

/-- Filling an appended commitment is exactly the original source successor
of the filled earlier prefix and the actual final physical binding cell. The
whole Config, registry and complete own action words are retained. -/
theorem fillCommitPrefix_snoc
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (name : VarId) (owner : Player) {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Δ) (insert name P))
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      ((block.snoc name owner fresh guard).prepend next))
    (store : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ) :
    let prefixEmbedding := cast (congrArg (fun program =>
      OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
        (block.prepend_snoc name owner fresh guard next)) embedding
    ∀ (field : FieldRef (graphLayout whole) (.binding owner payload))
      (selected : Fin (eventCount (block.prepend (.commit name owner fresh guard next)))),
      selected.val = block.length → field.field = .inr (prefixEmbedding.event selected) →
      fillCommitPrefix whole (block.snoc name owner fresh guard) next embedding store entry =
        commitSuccessor name guard
          (fillCommitPrefix whole block (.commit name owner fresh guard next) prefixEmbedding
          store entry)
          ((field.get? store).getD .failure) := by
  intro prefixEmbedding field selected atEnd named
  exact fill_snoc_of_events whole block name owner fresh guard next embedding prefixEmbedding
    (fun left right same => OutputEmbedding.event_cast whole
      (block.prepend_snoc name owner fresh guard next) embedding left right same)
      store entry field selected atEnd named

end Vegas
