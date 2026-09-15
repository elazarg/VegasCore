/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPublicStore
import Vegas.EventGraph.GuardValidation

/-! # Persistence of validated public reads

An event log with distinct node indices never overwrites an available public
value. Consequently a successful guard evaluation against an earlier public
prefix stays valid in the completed public store. No source syntax, candidate
catalog, homogeneous-graph certificate, or universally accepting guard is used.
-/

namespace Vegas.EventGraph.Graph

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}

private theorem initialPublicStore_nodeTarget (G : Graph Player L) (node : Nat) :
    G.initialPublicStore (G.nodeTarget node) = none := by
  have hlt : ¬ G.initialFields.length + node < G.initialFields.length := by omega
  simp only [initialPublicStore, Graph.field?, nodeTarget, hlt, ↓reduceDIte,
    Nat.add_sub_cancel_left]
  cases G.nodes[node]? with
  | none => rfl
  | some row =>
      dsimp only
      split <;> rfl

private theorem replayPublicOpenings_origin (G : Graph Player L) (ty : L.Ty)
    (events : List (SealedProgram.Event Player (L.Val ty))) (store : Store L)
    (field : Nat) (value : TypedValue L)
    (hvalue : G.replayPublicOpenings ty store events field = some value) :
    store field = some value ∨
      ∃ node opened, .opened node opened ∈ events ∧ field = G.nodeTarget node := by
  induction events generalizing store with
  | nil => exact Or.inl hvalue
  | cons event rest ih =>
      cases event with
      | accepted node handle =>
          rcases ih store hvalue with hstore | ⟨node, opened, hmem, hfield⟩
          · exact Or.inl hstore
          · exact Or.inr ⟨node, opened, List.mem_cons_of_mem _ hmem, hfield⟩
      | opened node opened =>
          rcases ih (store.set (G.nodeTarget node) ⟨ty, opened⟩) hvalue with
            hstore | ⟨other, otherValue, hmem, hfield⟩
          · by_cases hfield : field = G.nodeTarget node
            · exact Or.inr ⟨node, opened, List.mem_cons_self .., hfield⟩
            · exact Or.inl (by simpa only [Store.set_ne store hfield] using hstore)
          · exact Or.inr ⟨other, otherValue, List.mem_cons_of_mem _ hmem, hfield⟩

private theorem replayPublicOpenings_unchanged (G : Graph Player L) (ty : L.Ty)
    (events : List (SealedProgram.Event Player (L.Val ty))) (store : Store L)
    (field : Nat)
    (hnot : ∀ node value, .opened node value ∈ events → field ≠ G.nodeTarget node) :
    G.replayPublicOpenings ty store events field = store field := by
  induction events generalizing store with
  | nil => rfl
  | cons event rest ih =>
      have htail := fun node value hmem => hnot node value (List.mem_cons_of_mem event hmem)
      cases event with
      | accepted node handle => exact ih store htail
      | opened node value =>
          rw [replayPublicOpenings, ih _ htail,
            Store.set_ne store (hnot node value (List.mem_cons_self ..))]

theorem replayPublicOpenings_append (G : Graph Player L) (ty : L.Ty) (store : Store L)
    (beforeEvents afterEvents : List (SealedProgram.Event Player (L.Val ty))) :
    G.replayPublicOpenings ty store (beforeEvents ++ afterEvents) =
      G.replayPublicOpenings ty (G.replayPublicOpenings ty store beforeEvents) afterEvents := by
  induction beforeEvents generalizing store with
  | nil => rfl
  | cons event rest ih => cases event <;> exact ih _

/-- Extending a node-distinct event log preserves every already available
public value, including values read by a nontrivial opening validator. -/
theorem publicSealedStore_prefix (G : Graph Player L) (ty : L.Ty)
    (beforeEvents afterEvents : List (SealedProgram.Event Player (L.Val ty)))
    (hnodup : ((beforeEvents ++ afterEvents).map SealedProgram.Event.node).Nodup)
    (field : Nat) (value : TypedValue L)
    (hvalue : G.publicSealedStore ty beforeEvents field = some value) :
    G.publicSealedStore ty (beforeEvents ++ afterEvents) field = some value := by
  rw [publicSealedStore, G.replayPublicOpenings_append,
    G.replayPublicOpenings_unchanged ty afterEvents _ field ?_]
  · exact hvalue
  · intro node opened hmem hfield
    rcases G.replayPublicOpenings_origin ty beforeEvents G.initialPublicStore field value
        hvalue with hinitial | ⟨prior, priorValue, hprior, hpriorField⟩
    · rw [hfield, G.initialPublicStore_nodeTarget] at hinitial
      contradiction
    · have heq : prior = node := by
        have htargets := hpriorField.symm.trans hfield
        unfold nodeTarget at htargets
        omega
      subst prior
      rw [List.map_append, List.nodup_append] at hnodup
      exact hnodup.2.2 node (List.mem_map.mpr ⟨.opened node priorValue, hprior, rfl⟩)
        node (List.mem_map.mpr ⟨.opened node opened, hmem, rfl⟩) rfl

/-- Typed public reads are immutable along a node-distinct log extension. -/
theorem publicSealedStore_getAs_prefix (G : Graph Player L) (ty : L.Ty)
    (beforeEvents afterEvents : List (SealedProgram.Event Player (L.Val ty)))
    (hnodup : ((beforeEvents ++ afterEvents).map SealedProgram.Event.node).Nodup)
    (ref : FieldRef L) (value : L.Val ref.ty)
    (hvalue : Store.getAs (G.publicSealedStore ty beforeEvents) ref.field ref.ty = some value) :
    Store.getAs (G.publicSealedStore ty (beforeEvents ++ afterEvents)) ref.field ref.ty =
      some value := by
  cases hstored : G.publicSealedStore ty beforeEvents ref.field with
  | none => simp [Store.getAs, hstored] at hvalue
  | some stored =>
      have hafter := G.publicSealedStore_prefix ty beforeEvents afterEvents hnodup
        ref.field stored hstored
      simpa only [Store.getAs, hstored, hafter] using hvalue

/-- A guard evaluated against an earlier public prefix has the same Boolean
result against the completed store. Its dependencies were already available
and distinct event nodes cannot overwrite them. -/
theorem guard_validation_prefix (G : Graph Player L) (ty : L.Ty)
    (beforeEvents afterEvents : List (SealedProgram.Event Player (L.Val ty)))
    (hnodup : ((beforeEvents ++ afterEvents).map SealedProgram.Event.node).Nodup)
    (guard : EventGuard L) (value : L.Val guard.ty) {result : Bool}
    (hvalid : guard.evalValidationStore? value (G.publicSealedStore ty beforeEvents) =
      some result) :
    guard.evalValidationStore? value (G.publicSealedStore ty (beforeEvents ++ afterEvents)) =
      some result :=
  guard.evalValidationStore?_preserved value _ _ result hvalid
    (fun ref _ read hread =>
      G.publicSealedStore_getAs_prefix ty beforeEvents afterEvents hnodup ref read hread)

end Vegas.EventGraph.Graph

/-- info: 'Vegas.EventGraph.Graph.guard_validation_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.Graph.guard_validation_prefix
