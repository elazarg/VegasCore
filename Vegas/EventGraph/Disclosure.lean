/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Basic

/-! # Direct disclosures and public-field origins

Each field has at most one direct reveal node. This is an additional graph
condition, independent of well-formedness and declared information. It lets a
defaulted public disclosure be represented by one changed commitment value
without contradicting another disclosure of the same field.
In a sample-free commit/reveal graph, public fields originate in public initial
data or a reveal, independently of whether commitment guards restrict values.
-/

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- A field is directly disclosed at most once in the graph. -/
def Graph.UniqueReveals (G : Graph Player L) : Prop :=
  ∀ (left right : Fin G.nodeCount) (field : Nat),
    (G.nodeRow left).sem = .reveal field →
    (G.nodeRow right).sem = .reveal field → left = right

/-- In a sample-free graph whose reveals disclose commitments, a public field
is initial public data or a reveal output. Guard truth is irrelevant to this
structural classification. -/
theorem Graph.publicField_origin (G : Graph Player L) {ty : L.Ty}
    (hwf : G.WF) (hrow : ∀ node, (G.nodeRow node).ty = ty)
    (hnoSamples : ∀ node dist, (G.nodeRow node).sem ≠ .sample dist)
    (hreveals : ∀ node source, (G.nodeRow node).sem = .reveal source →
      ∃ (producer : Fin G.nodeCount) (who : Player) (guard : EventGuard L),
        source = G.nodeTarget producer ∧ (G.nodeRow producer).sem = .commit who guard)
    (ref : FieldRef L) (hpublic : G.fieldRefPublic ref) :
    (∃ spec value, G.field? ref.field = some spec ∧
      spec.source = .initial value ∧ spec.ty = ref.ty ∧ spec.owner = none) ∨
    ∃ (node producer : Fin G.nodeCount) (owner : Player) (guard : EventGuard L),
      ref.field = G.nodeTarget node ∧ ref.ty = ty ∧
      (G.nodeRow node).sem = .reveal (G.nodeTarget producer) ∧
      (G.nodeRow producer).sem = .commit owner guard := by
  obtain ⟨spec, hfield, hty, howner⟩ := hpublic
  cases hsource : spec.source with
  | initial value => exact Or.inl ⟨spec, value, hfield, hsource, hty, howner⟩
  | event writer =>
      obtain ⟨_, hwriter⟩ := G.node_get_of_field_event_source hfield hsource
      have hlt : writer < G.nodeCount := (List.getElem?_eq_some_iff.mp hwriter).1
      let node : Fin G.nodeCount := ⟨writer, hlt⟩
      have htarget : ref.field = G.nodeTarget node :=
        G.field_eq_nodeTarget_of_event_source hfield hsource
      have hspec := G.field?_nodeTarget (G.nodes_get?_nodeRow node)
      rw [← htarget, hfield] at hspec
      have heq := Option.some.inj hspec
      have hrefty : ref.ty = ty := hty.symm.trans
        ((congrArg FieldSpec.ty heq).trans (hrow node))
      cases hsem : (G.nodeRow node).sem with
      | sample dist => exact (hnoSamples node dist hsem).elim
      | commit owner guard =>
          have hnodeWF := hwf node (G.nodeRow node) (G.nodes_get?_nodeRow node)
          unfold Graph.nodeWFAt at hnodeWF
          rw [hsem] at hnodeWF
          have hbad : spec.owner = some owner :=
            (congrArg FieldSpec.owner heq).trans hnodeWF.2.2.1
          rw [howner] at hbad
          contradiction
      | reveal source =>
          obtain ⟨producer, owner, guard, hproducer, hcommit⟩ :=
            hreveals node source hsem
          exact Or.inr ⟨node, producer, owner, guard, htarget, hrefty,
            hproducer ▸ hsem, hcommit⟩

end Vegas.EventGraph
