/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSwapInfo
import Vegas.Game.OnePacketSwapExchange

/-! # The swap between two views of one owner

Two views of a player `who` that agree on everything operational can differ only
in what `who` alone sees: the values of its private fields, its own private
inputs and bindings, and the values prepared at its own handles. The owner swap
between two such views (`Vegas.ownerSwap`) transposes, at each private field of
`who`, the two stored values when both are present, distinct and not failures,
and at each handle of `who`, the two prepared values when both are openable and
distinct.

The owner swap does not depend on the order of the two views
(`Vegas.ownerSwap_comm`), and it fixes every other player
(`Vegas.ownerSwap_fixes`): no other player sees a private field of `who`, acts
at an event of `who`, or owns a handle of `who`.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

/-- A field is private to `who`: `who` sees it and it is not public. -/
def PrivateTo (who : Player) (field : (graph setup).Field) : Prop :=
  (graph setup).fieldVisibleTo who field ∧ ¬ (graph setup).fieldPublic field

section Pairs

variable (who : Player) (first second : PlayerView (graph setup))

open Classical in
/-- The pair of two stored values at a field: both present, distinct and not
failures. -/
def ownerValuePair (field : (graph setup).Field) :
    Option (((graph setup).layout field).Value × ((graph setup).layout field).Value) :=
  if PrivateTo who field then
    match first.observation.store field, second.observation.store field with
    | some left, some right =>
        if left = right ∨ ((graph setup).layout field).IsFailure left ∨
            ((graph setup).layout field).IsFailure right then none
        else some (left, right)
    | _, _ => none
  else none

theorem ownerValuePair_public {field : (graph setup).Field}
    (isPublic : (graph setup).fieldPublic field) :
    ownerValuePair who first second field = none := by
  unfold ownerValuePair
  have notPrivate : ¬ PrivateTo who field := fun privateTo => privateTo.2 isPublic
  simp [notPrivate]

/-- **The owner pairs** between two views of `who`. -/
def ownerPairs : (graph setup).SwapPairs where
  pair := ownerValuePair who first second
  public_none _ isPublic := ownerValuePair_public who first second isPublic
  binding_success event owner payload outputEq left right paired := by
    unfold ownerValuePair at paired
    split_ifs at paired with privateTo
    split at paired
    · rename_i firstValue secondValue _ _
      split_ifs at paired with excluded
      cases paired
      have general : ∀ (kind : EventGraph.EventField Player L)
          (kindEq : kind = .binding owner payload),
          kind.IsFailure (cast (congrArg EventGraph.EventField.Value kindEq.symm) .failure) := by
        rintro _ rfl
        rfl
      have notFailure : ∀ value : ((graph setup).layout (.inr event)).Value,
          ¬ ((graph setup).layout (.inr event)).IsFailure value →
            value ≠ cast (congrArg EventGraph.EventField.Value outputEq.symm) .failure := by
        intro value notFailed same
        apply notFailed
        rw [same]
        exact general _ outputEq
      push Not at excluded
      exact ⟨notFailure _ excluded.2.1, notFailure _ excluded.2.2⟩
    · cases paired

open Classical in
/-- **The owner handle pairs**: at each handle of `who`, the two prepared values
when both are openable and distinct. -/
def ownerHandlePairs (handle : Handle (graph setup)) : Option (Raw L × Raw L) :=
  if handle.1 = who then
    match first.candidates handle.2, second.candidates handle.2 with
    | .openable left, .openable right => if left = right then none else some (left, right)
    | _, _ => none
  else none

/-- **The owner swap** between two views of `who`. -/
def ownerSwap : HiddenSwap (graph setup) :=
  HiddenSwap.ofPairs (ownerPairs who first second) (ownerHandlePairs who first second)


theorem pairSwap_ownerValuePair_comm (field : (graph setup).Field) :
    EventGraph.pairSwap (ownerValuePair who second first field) =
      EventGraph.pairSwap (ownerValuePair who first second field) := by
  unfold ownerValuePair
  split_ifs
  · rcases first.observation.store field with _ | left <;>
    rcases second.observation.store field with _ | right
    all_goals try rfl
    by_cases excluded : left = right ∨ ((graph setup).layout field).IsFailure left ∨
        ((graph setup).layout field).IsFailure right
    · have swapped : right = left ∨ ((graph setup).layout field).IsFailure right ∨
          ((graph setup).layout field).IsFailure left := by
        rcases excluded with same | failed | failed
        · exact Or.inl same.symm
        · exact Or.inr (Or.inr failed)
        · exact Or.inr (Or.inl failed)
      simp only [excluded, swapped, ↓reduceIte]
    · have swapped : ¬ (right = left ∨ ((graph setup).layout field).IsFailure right ∨
          ((graph setup).layout field).IsFailure left) := by
        intro bad
        apply excluded
        rcases bad with same | failed | failed
        · exact Or.inl same.symm
        · exact Or.inr (Or.inr failed)
        · exact Or.inr (Or.inl failed)
      simp only [excluded, swapped, ↓reduceIte]
      exact EventGraph.pairSwap_comm _ _
  · rfl

theorem pairSwap_ownerHandlePairs_comm (handle : Handle (graph setup)) :
    EventGraph.pairSwap (ownerHandlePairs who second first handle) =
      EventGraph.pairSwap (ownerHandlePairs who first second handle) := by
  unfold ownerHandlePairs
  split_ifs
  · rcases first.candidates handle.2 with _ | left | _ <;>
    rcases second.candidates handle.2 with _ | right | _
    all_goals try rfl
    by_cases same : left = right
    · subst same
      simp
    · have other : right ≠ left := fun equal => same equal.symm
      simp only [same, other, ↓reduceIte]
      exact EventGraph.pairSwap_comm _ _
  · rfl

/-- **The owner swap does not depend on the order of the two views.** -/
theorem ownerSwap_comm : ownerSwap who second first = ownerSwap who first second := by
  have values := EventGraph.ValueSwap.ofPairs_congr (first := ownerPairs who second first)
    (second := ownerPairs who first second) (pairSwap_ownerValuePair_comm who first second)
  have raws : (fun handle => EventGraph.pairSwap (ownerHandlePairs who second first handle)) =
      (fun handle => EventGraph.pairSwap (ownerHandlePairs who first second handle)) :=
    funext (pairSwap_ownerHandlePairs_comm who first second)
  unfold ownerSwap HiddenSwap.ofPairs
  congr 1

/-- A field private to `who` is visible to no other player. -/
theorem not_visible_of_privateTo {field : (graph setup).Field} {other : Player}
    (different : other ≠ who) (privateTo : PrivateTo who field) :
    ¬ (graph setup).fieldVisibleTo other field := by
  intro visible
  obtain ⟨own, notPublic⟩ := privateTo
  unfold EventGraph.fieldVisibleTo at visible own
  unfold EventGraph.fieldPublic at notPublic
  revert visible own notPublic
  cases (graph setup).layout field with
  | publicData | publication => intro _ _ notPublic; exact notPublic trivial
  | binding owner payload | privateInput owner payload =>
      intro visible own _
      exact different (visible.symm.trans own)

/-- **The owner swap fixes every other player.** -/
theorem ownerSwap_fixes {other : Player} (different : other ≠ who) :
    (ownerSwap who first second).Fixes other := by
  have pairNone : ∀ field, (graph setup).fieldVisibleTo other field →
      (ownerPairs who first second).pair field = none := fun field visible => by
    change ownerValuePair who first second field = none
    have notPrivate : ¬ PrivateTo who field := fun privateTo =>
      not_visible_of_privateTo who different privateTo visible
    unfold ownerValuePair
    simp [notPrivate]
  refine ⟨fun field visible => ?_, fun event acting => ?_, fun slot => ?_⟩
  · change EventGraph.pairSwap ((ownerPairs who first second).pair field) = id
    rw [pairNone field visible]
    rfl
  · change (ownerPairs who first second).action event = id
    unfold EventGraph.SwapPairs.action
    cases nodeView (graph setup) event with
    | resolve | sample => rfl
    | bind owner payload outputEq codeEq =>
        rw [nodeView_bind_actor outputEq codeEq] at acting
        cases Option.some.inj acting
        have visible : (graph setup).fieldVisibleTo other (.inr event) := by
          change ((graph setup).outputLayout event).VisibleTo other
          rw [outputEq]
          rfl
        rw [pairNone _ visible]
        funext original
        simp [EventGraph.pairSwap]
  · change EventGraph.pairSwap (ownerHandlePairs who first second (other, slot)) = id
    unfold ownerHandlePairs
    simp only [different, ↓reduceIte]
    rfl

end Pairs

end Vegas
