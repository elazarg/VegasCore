/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionPolicy

/-! # Local-store completion after sealed timeouts

Resolution adds values only at timed-out commitments owned by the observing
principal.  These fold laws expose the resulting lookup directly, without a
decoded source configuration or a post-timeout source/runtime invariant.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

private theorem fold_resolvedStoreStep_getAs_of_preserved
    (supported : SealedFragment G ty) (who : Player) (nullValue : L.Val ty)
    (history : List (supported.compile.messageApplication
      (Value := L.Val ty)).PlayerEntry) (store : Store L) (completed : List Nat)
    (field : Nat) (fieldTy : L.Ty)
    (hfield : ∀ index, index ∈ completed → ∀ guard,
      G.node? index = some (.commit who guard) → field ≠ G.nodeTarget index) :
    Store.getAs (completed.foldl
      (supported.resolvedPlayerStoreStep who nullValue history) store) field fieldTy =
      Store.getAs store field fieldTy := by
  induction completed generalizing store with
  | nil => rfl
  | cons index rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      · unfold resolvedPlayerStoreStep
        cases hnode : G.node? index with
        | none => rfl
        | some sem =>
            cases sem with
            | sample dist => rfl
            | reveal source => rfl
            | commit owner guard =>
                by_cases howner : owner = who
                · subst owner
                  simp only [↓reduceIte]
                  exact Store.getAs_set_ne store
                    (hfield index (List.mem_cons_self ..) guard hnode) _ fieldTy
                · simp only [howner, ↓reduceIte]
      · intro other hother guard hcommit
        exact hfield other (List.mem_cons_of_mem index hother) guard hcommit

private theorem fold_resolvedStoreStep_getAs_commit
    (supported : SealedFragment G ty) (who : Player) (nullValue : L.Val ty)
    (history : List (supported.compile.messageApplication
      (Value := L.Val ty)).PlayerEntry) (node : Fin G.nodeCount) (store : Store L)
    (hstore : Store.getAs store (G.nodeTarget node) ty = some
      (((supported.compile.registrationEncoding node.val).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) history).getD nullValue))
    (completed : List Nat) :
    Store.getAs (completed.foldl
      (supported.resolvedPlayerStoreStep who nullValue history) store)
        (G.nodeTarget node) ty = some
      (((supported.compile.registrationEncoding node.val).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) history).getD nullValue) := by
  induction completed generalizing store with
  | nil => exact hstore
  | cons index rest ih =>
      simp only [List.foldl_cons]
      apply ih
      unfold resolvedPlayerStoreStep
      cases hnode : G.node? index with
      | none => exact hstore
      | some sem =>
          cases sem with
          | sample dist => exact hstore
          | reveal source => exact hstore
          | commit owner otherGuard =>
              by_cases howner : owner = who
              · subst owner
                simp only [↓reduceIte]
                by_cases hindex : index = node.val
                · subst index
                  simp [Store.getAs, TypedValue.as?]
                · have htarget : G.nodeTarget node ≠ G.nodeTarget index := by
                    unfold Graph.nodeTarget
                    omega
                  exact (Store.getAs_set_ne store htarget _ ty).trans hstore
              · simp only [howner, ↓reduceIte]
                exact hstore

/-- A timed-out commitment owned by the observer is always readable from the
resolved local store.  A prior private registration wins over the null value;
an empty cache receives exactly the configured null. -/
theorem resolvedPlayerStore_getAs_timeout_commit
    (supported : SealedFragment G ty) (who : Player) (nullValue : L.Val ty)
    (completed : List Nat)
    (history : List (supported.compile.messageApplication
      (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (node : Fin G.nodeCount) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (htimeout : node.val ∈ completed) :
    Store.getAs (supported.resolvedPlayerStore who nullValue completed history view)
        (G.nodeTarget node) ty = some
      (((supported.compile.registrationEncoding node.val).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) history).getD nullValue) := by
  obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp htimeout
  unfold resolvedPlayerStore
  rw [List.foldl_append]
  simp only [List.foldl_cons]
  apply supported.fold_resolvedStoreStep_getAs_commit who nullValue history node
  unfold resolvedPlayerStoreStep
  rw [G.node?_nodeRow, hsem]
  simp [Store.getAs, TypedValue.as?]

/-- The resolution fold preserves any typed field which is not the target of
a timed-out commitment owned by this observer.  Timed-out reveals therefore
do not overwrite their public target in this local-store completion pass. -/
theorem resolvedPlayerStore_getAs_of_not_owned_timeout_target
    (supported : SealedFragment G ty) (who : Player) (nullValue : L.Val ty)
    (completed : List Nat)
    (history : List (supported.compile.messageApplication
      (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (field : Nat) (fieldTy : L.Ty)
    (hfield : ∀ index, index ∈ completed → ∀ guard,
      G.node? index = some (.commit who guard) → field ≠ G.nodeTarget index) :
    Store.getAs (supported.resolvedPlayerStore who nullValue completed history view)
        field fieldTy =
      Store.getAs (supported.playerStore who history view) field fieldTy := by
  unfold resolvedPlayerStore
  exact supported.fold_resolvedStoreStep_getAs_of_preserved who nullValue history _ _ _ _ hfield

private theorem fold_resolvedStoreStep_available
    (supported : SealedFragment G ty) (who : Player) (nullValue : L.Val ty)
    (history : List (supported.compile.messageApplication
      (Value := L.Val ty)).PlayerEntry) (store : Store L) (completed : List Nat)
    (field : Nat)
    (havailable : (Store.getAs store field ty).isSome = true) :
    (Store.getAs (completed.foldl
      (supported.resolvedPlayerStoreStep who nullValue history) store) field ty).isSome = true := by
  induction completed generalizing store with
  | nil => exact havailable
  | cons index rest ih =>
      simp only [List.foldl_cons]
      apply ih
      unfold resolvedPlayerStoreStep
      cases hnode : G.node? index with
      | none => exact havailable
      | some sem =>
          cases sem with
          | sample dist => exact havailable
          | reveal source => exact havailable
          | commit owner guard =>
              by_cases howner : owner = who
              · subst owner
                simp only [↓reduceIte]
                by_cases hfield : field = G.nodeTarget index
                · subst field
                  simp [Store.getAs, TypedValue.as?]
                · rw [Store.getAs_set_ne store hfield]
                  exact havailable
              · simp only [howner, ↓reduceIte]
                exact havailable

/-- Timeout completion cannot make an already available common-typed local
field unavailable. Every fold write has exactly the fragment's common type. -/
theorem resolvedPlayerStore_available
    (supported : SealedFragment G ty) (who : Player) (nullValue : L.Val ty)
    (completed : List Nat)
    (history : List (supported.compile.messageApplication
      (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (field : Nat)
    (havailable : (Store.getAs (supported.playerStore who history view) field ty).isSome = true) :
    (Store.getAs (supported.resolvedPlayerStore who nullValue completed history view)
      field ty).isSome = true := by
  unfold resolvedPlayerStore
  exact supported.fold_resolvedStoreStep_available who nullValue history _ _ field havailable

/-- A reveal target is preserved by timeout completion, including when that
reveal itself is in the timeout list: the fold writes only owned commitment
targets, and graph node targets are injective. -/
theorem resolvedPlayerStore_getAs_reveal_target
    (supported : SealedFragment G ty) (who : Player) (nullValue : L.Val ty)
    (completed : List Nat)
    (history : List (supported.compile.messageApplication
      (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (node : Fin G.nodeCount) (source : Nat)
    (hsem : (G.nodeRow node).sem = .reveal source) (fieldTy : L.Ty) :
    Store.getAs (supported.resolvedPlayerStore who nullValue completed history view)
        (G.nodeTarget node) fieldTy =
      Store.getAs (supported.playerStore who history view)
        (G.nodeTarget node) fieldTy := by
  apply supported.resolvedPlayerStore_getAs_of_not_owned_timeout_target
  intro index _ guard hcommit htarget
  have hindex : index = node.val := by
    unfold Graph.nodeTarget at htarget
    omega
  subst index
  rw [G.node?_nodeRow, hsem] at hcommit
  cases hcommit

end Vegas.EventGraph.SealedFragment
