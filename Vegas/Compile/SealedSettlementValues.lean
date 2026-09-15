/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPublicStore
import Vegas.EventGraph.Linearization

/-! # Graph values representing a public settlement

The assignment copies each public reveal from a supplied store and assigns
its producer the same value. Unrevealed commitments use the designated
default. These are store construction laws, not yet execution or policy laws:
semantic validity of the resulting values must be proved separately.
-/

noncomputable section

namespace Vegas.EventGraph.Graph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- A commitment's public settlement value, or the default when it has no
direct reveal. This assignment need not match a private runtime candidate. -/
def revealAssignment (G : Graph Player L) {ty : L.Ty}
    (fallback : L.Val ty) (store : Store L) : Fin G.nodeCount → L.Val ty := by
  classical
  exact fun producer =>
    if found : ∃ node, (G.nodeRow node).sem = .reveal (G.nodeTarget producer) then
      (Store.getAs store (G.nodeTarget (Classical.choose found).val) ty).getD fallback
    else fallback

theorem revealAssignment_reveal (G : Graph Player L) {ty : L.Ty}
    (hunique : G.UniqueReveals) (fallback : L.Val ty) (store : Store L)
    (node producer : Fin G.nodeCount)
    (hsem : (G.nodeRow node).sem = .reveal (G.nodeTarget producer)) :
    G.revealAssignment fallback store producer =
      (Store.getAs store (G.nodeTarget node) ty).getD fallback := by
  classical
  have found : ∃ node, (G.nodeRow node).sem = .reveal (G.nodeTarget producer) := ⟨node, hsem⟩
  rw [revealAssignment, dif_pos found]
  rw [hunique _ node _ (Classical.choose_spec found) hsem]

/-- Node values read from a public settlement, with private producers chosen
consistently with their disclosures. Sample validity is not supplied here. -/
def settlementValue (G : Graph Player L) {ty : L.Ty}
    (fallback : L.Val ty) (store : Store L) (node : Fin G.nodeCount) : L.Val ty :=
  match (G.nodeRow node).sem with
  | .commit _ _ => G.revealAssignment fallback store node
  | .reveal _ => (Store.getAs store (G.nodeTarget node) ty).getD fallback
  | .sample _ => fallback

/-- Assemble the chosen values in canonical graph order. Reachability is a
separate theorem, so this definition admits no unproved execution step. -/
def settlementConfig (G : Graph Player L) {ty : L.Ty}
    (fallback : L.Val ty) (store : Store L) : Config G :=
  Config.canonicalCompletion G (fun node => ⟨ty, G.settlementValue fallback store node⟩)

theorem settlementConfig_getAs (G : Graph Player L) {ty : L.Ty}
    (fallback : L.Val ty) (store : Store L) (node : Fin G.nodeCount) :
    Store.getAs (G.settlementConfig fallback store).store (G.nodeTarget node) ty =
      some (G.settlementValue fallback store node) := by
  unfold settlementConfig Config.canonicalCompletion Config.scheduleComplete
  rw [Config.completeNodes_getAs_of_mem _ _
    (by simpa [Function.comp_def] using G.nodeOrder_nodup)
    (List.mem_map.mpr ⟨node, G.mem_nodeOrder node, rfl⟩)]
  simp [TypedValue.as?]

theorem settlementConfig_getAs_initial (G : Graph Player L) {ty : L.Ty}
    (fallback : L.Val ty) (store : Store L)
    (field : Nat) (spec : FieldSpec Player L) (value : L.Val spec.ty)
    (hfield : G.field? field = some spec) (hsource : spec.source = .initial value) :
    Store.getAs (G.settlementConfig fallback store).store field spec.ty = some value := by
  unfold settlementConfig Config.canonicalCompletion Config.scheduleComplete
  rw [Config.completeNodes_getAs_of_not_targets _ _ ?_]
  · simp [Config.initial, Store.getAs, Graph.initialStore, hfield,
      FieldSpec.initialValue?, hsource, TypedValue.as?]
  · rintro step hstep
    obtain ⟨node, _, rfl⟩ := List.mem_map.mp hstep
    exact G.initial_field_ne_target field spec value hfield hsource node

/-- The assembled configuration has the supplied public store, without any
assumption that all guards accept or that the assignment is already reachable. -/
theorem settlementConfig_public_store (G : Graph Player L) {ty : L.Ty}
    (hwf : G.WF) (hrow : ∀ node, (G.nodeRow node).ty = ty)
    (hnoSamples : ∀ node dist, (G.nodeRow node).sem ≠ .sample dist)
    (hreveals : ∀ node source, (G.nodeRow node).sem = .reveal source →
      ∃ (producer : Fin G.nodeCount) (who : Player) (guard : EventGuard L),
        source = G.nodeTarget producer ∧ (G.nodeRow producer).sem = .commit who guard)
    (fallback : L.Val ty) (store : Store L)
    (havailable : ∀ ref, G.fieldRefPublic ref →
      ∃ value, Store.getAs store ref.field ref.ty = some value)
    (hinitial : ∀ field (spec : FieldSpec Player L) (value : L.Val spec.ty),
      G.field? field = some spec → spec.source = .initial value → spec.owner = none →
      Store.getAs store field spec.ty = some value)
    (ref : FieldRef L) (hpublic : G.fieldRefPublic ref) :
    Store.getAs (G.settlementConfig fallback store).store ref.field ref.ty =
      Store.getAs store ref.field ref.ty := by
  rcases G.publicField_origin hwf hrow hnoSamples hreveals ref hpublic with
    ⟨spec, value, hfield, hsource, hty, howner⟩ |
      ⟨node, producer, owner, guard, htarget, hrefty, hsem, _hcommit⟩
  · rw [← hty, G.settlementConfig_getAs_initial fallback store ref.field spec value hfield hsource,
      hinitial ref.field spec value hfield hsource howner]
  · obtain ⟨value, hvalue⟩ := havailable ref hpublic
    have hcast := Store.getAs_cast store ref.field hrefty hvalue
    rw [htarget] at hcast
    rw [htarget, hrefty, G.settlementConfig_getAs, settlementValue, hsem, hcast]
    rfl

end Vegas.EventGraph.Graph
