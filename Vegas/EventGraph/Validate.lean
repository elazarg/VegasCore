/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Basic

/-!
# Raw event-graph validation

Boolean validation is useful for hand-written examples and tests. Semantic
compilation uses `Graph.WF`, the proof-level invariant in `EventGraph.Basic`.
-/

namespace Vegas

namespace EventGraph

namespace Graph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Fold over a list with the current list index. -/
def allIndexedFrom {α : Type} (start : Nat) : List α → (Nat → α → Bool) → Bool
  | [], _ => true
  | value :: rest, p => p start value && allIndexedFrom (start + 1) rest p

/-- Boolean universal quantification over a finite set. -/
def allFields (fields : Finset Nat) (p : Nat → Bool) : Bool :=
  decide (∀ field, field ∈ fields → p field = true)

@[simp] theorem allFields_eq_true {fields : Finset Nat} {p : Nat → Bool} :
    allFields fields p = true ↔
      ∀ field, field ∈ fields → p field = true := by
  simp [allFields]

/-- Boolean universal quantification over a finite set of typed field
references. -/
def allFieldRefs (refs : Finset (FieldRef L)) (p : FieldRef L → Bool) :
    Bool :=
  decide (∀ ref, ref ∈ refs → p ref = true)

@[simp] theorem allFieldRefs_eq_true {refs : Finset (FieldRef L)}
    {p : FieldRef L → Bool} :
    allFieldRefs refs p = true ↔
      ∀ ref, ref ∈ refs → p ref = true := by
  simp [allFieldRefs]

/-- Boolean check that a typed field reference names a public graph field. -/
def validFieldRefPublic (G : Graph Player L) (ref : FieldRef L) : Bool :=
  match G.field? ref.field with
  | some spec => decide (spec.ty = ref.ty) && decide (spec.owner = none)
  | none => false

theorem validFieldRefPublic_eq_true_iff (G : Graph Player L)
    (ref : FieldRef L) :
    G.validFieldRefPublic ref = true ↔ G.fieldRefPublic ref := by
  unfold validFieldRefPublic fieldRefPublic
  cases G.field? ref.field <;> simp

/-- Boolean check that a typed field reference names a graph field visible to a
player. -/
def validFieldRefVisibleTo (G : Graph Player L) (who : Player)
    (ref : FieldRef L) : Bool :=
  match G.field? ref.field with
  | some spec =>
      decide (spec.ty = ref.ty) &&
        decide (spec.owner = none ∨ spec.owner = some who)
  | none => false

theorem validFieldRefVisibleTo_eq_true_iff (G : Graph Player L)
    (who : Player) (ref : FieldRef L) :
    G.validFieldRefVisibleTo who ref = true ↔
      G.fieldRefVisibleTo who ref := by
  unfold validFieldRefVisibleTo fieldRefVisibleTo
  cases G.field? ref.field <;> simp

/-- Boolean check corresponding to `Graph.nodeWFAt`. -/
def validNodeAt (G : Graph Player L) (node : Nat)
    (event : EventNode Player L) : Bool :=
  let readsAvailable :=
    allFields event.sem.reads (fun field =>
      G.fieldAvailableBefore node field)
  match event.sem with
  | .sample dist =>
      decide (event.ty = dist.ty) &&
        decide (event.owner = none) &&
          readsAvailable &&
            allFieldRefs dist.reads (G.validFieldRefPublic ·)
  | .commit who guard =>
      decide (event.ty = guard.ty) &&
        decide (event.owner = some who) &&
          readsAvailable &&
            allFieldRefs guard.choiceReads (G.validFieldRefVisibleTo who ·)
  | .reveal source =>
      match G.field? source with
      | some sourceSpec =>
          decide (sourceSpec.ty = event.ty) &&
            decide (sourceSpec.owner.isSome) &&
              decide (event.owner = none) &&
                readsAvailable
      | none => false

theorem validNodeAt_eq_true_iff (G : Graph Player L) (node : Nat)
    (event : EventNode Player L) :
    G.validNodeAt node event = true ↔ G.nodeWFAt node event := by
  cases event with
  | mk ty owner sem =>
      cases sem with
      | sample dist =>
          simp only [validNodeAt, nodeWFAt, Bool.and_eq_true,
            decide_eq_true_eq, allFields_eq_true, allFieldRefs_eq_true,
            validFieldRefPublic_eq_true_iff]
          constructor
          · rintro ⟨⟨⟨hty, howner⟩, hreads⟩, hrefs⟩
            exact ⟨hreads, hty, howner, hrefs⟩
          · rintro ⟨hreads, hty, howner, hrefs⟩
            exact ⟨⟨⟨hty, howner⟩, hreads⟩, hrefs⟩
      | commit who guard =>
          simp only [validNodeAt, nodeWFAt, Bool.and_eq_true,
            decide_eq_true_eq, allFields_eq_true, allFieldRefs_eq_true,
            validFieldRefVisibleTo_eq_true_iff]
          constructor
          · rintro ⟨⟨⟨hty, howner⟩, hreads⟩, hrefs⟩
            exact ⟨hreads, hty, howner, hrefs⟩
          · rintro ⟨hreads, hty, howner, hrefs⟩
            exact ⟨⟨⟨hty, howner⟩, hreads⟩, hrefs⟩
      | reveal source =>
          unfold validNodeAt nodeWFAt
          cases hsource : G.field? source with
          | none =>
              simp only [hsource, Bool.false_eq_true, false_iff]
              intro h
              rcases h with ⟨_hreads, _sourceSpec, hget, _rest⟩
              cases hget
          | some sourceSpec =>
              simp only [hsource, Bool.and_eq_true, decide_eq_true_eq,
                allFields_eq_true]
              constructor
              · rintro ⟨⟨⟨hty, hsealed⟩, howner⟩, hreads⟩
                exact ⟨hreads, sourceSpec, rfl, hty, hsealed, howner⟩
              · rintro ⟨hreads, _foundSpec, hget, hty, hsealed, howner⟩
                cases hget
                exact ⟨⟨⟨hty, hsealed⟩, howner⟩, hreads⟩

/-- Boolean graph well-formedness check for raw numeric ids. -/
def valid (G : Graph Player L) : Bool :=
  allIndexedFrom 0 G.nodes G.validNodeAt

theorem allIndexedFrom_eq_true_of_get? {α : Type} {xs : List α}
    {p : Nat → α → Bool} {start offset : Nat} {value : α}
    (hall : allIndexedFrom start xs p = true)
    (hget : xs[offset]? = some value) :
    p (start + offset) value = true := by
  induction xs generalizing start offset with
  | nil =>
      cases hget
  | cons head tail ih =>
      cases offset with
      | zero =>
          have hallParts :
              p start head = true ∧
                allIndexedFrom (start + 1) tail p = true := by
            simpa only [allIndexedFrom, Bool.and_eq_true] using hall
          have hvalue : head = value := by
            simpa only [List.getElem?_cons_zero, Option.some.injEq] using hget
          cases hvalue
          simpa only [Nat.add_zero] using hallParts.1
      | succ offset =>
          have hallParts :
              p start head = true ∧
                allIndexedFrom (start + 1) tail p = true := by
            simpa only [allIndexedFrom, Bool.and_eq_true] using hall
          have htailGet : tail[offset]? = some value := by
            simpa only [List.getElem?_cons_succ] using hget
          have htail : allIndexedFrom (start + 1) tail p = true := by
            exact hallParts.2
          have hp := ih (start := start + 1) (offset := offset) htail htailGet
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp

theorem WF_of_valid_eq_true (G : Graph Player L)
    (hvalid : G.valid = true) : G.WF := by
  intro node event hget
  have hnode :
      G.validNodeAt (0 + node) event = true :=
    allIndexedFrom_eq_true_of_get? (start := 0) (offset := node)
      (value := event) hvalid hget
  exact (G.validNodeAt_eq_true_iff node event).mp (by simpa using hnode)

end Graph

end EventGraph

end Vegas
