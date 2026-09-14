/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedMessages

/-! # Origins of declared reads in the sealed backend -/

namespace Vegas.EventGraph.SealedFragment

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty}

/-- Public fields in a sealed fragment are initial public data or the output
of a reveal of a compiled commitment. This classification uses graph typing,
not a runtime reachability or completion assumption. -/
theorem publicField_origin (supported : SealedFragment G ty)
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
        ((congrArg FieldSpec.ty heq).trans (supported.rowType node))
      cases hsem : (G.nodeRow node).sem with
      | sample dist => exact (supported.noSamples node dist hsem).elim
      | commit owner guard =>
          have hwf := supported.graphWF node (G.nodeRow node) (G.nodes_get?_nodeRow node)
          unfold Graph.nodeWFAt at hwf
          rw [hsem] at hwf
          have hbad : spec.owner = some owner :=
            (congrArg FieldSpec.owner heq).trans hwf.2.2.1
          rw [howner] at hbad
          contradiction
      | reveal source =>
          obtain ⟨producer, owner, guard, hproducer, hcommit⟩ :=
            supported.revealSource node source hsem
          exact Or.inr ⟨node, producer, owner, guard, htarget, hrefty,
            hproducer ▸ hsem, hcommit⟩

/-- A declared read of a compiled commitment is either an initially visible
field or the output of a completed earlier node. In the latter case the
producer is an own commitment or a public reveal; admitted sealed graphs have
no sample nodes. -/
theorem choiceRead_origin_of_prereqs_completed
    (supported : SealedFragment G ty) (completed : Fin G.nodeCount → Prop)
    (node : Fin G.nodeCount) (who : Player) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (hcompleted : ∀ prior, prior ∈ G.prereqs node → completed prior)
    (ref : FieldRef L) (href : ref ∈ guard.choiceReads) :
    (∃ spec value, G.field? ref.field = some spec ∧
      spec.source = .initial value ∧ spec.ty = ref.ty ∧
      (spec.owner = none ∨ spec.owner = some who)) ∨
    ∃ prior : Fin G.nodeCount,
      ref.field = G.nodeTarget prior ∧ ref.ty = ty ∧ completed prior ∧
      ((∃ priorGuard, (G.nodeRow prior).sem = .commit who priorGuard) ∨
        ∃ source, (G.nodeRow prior).sem = .reveal source ∧
          (G.nodeRow prior).owner = none) := by
  have hwf := supported.graphWF node (G.nodeRow node) (G.nodes_get?_nodeRow node)
  have hread : ref.field ∈ (G.nodeRow node).sem.reads := by
    rw [hsem]
    exact Finset.mem_image.mpr ⟨ref, href, rfl⟩
  have havailable := hwf.1 ref.field hread
  unfold Graph.nodeWFAt at hwf
  rw [hsem] at hwf
  obtain ⟨spec, hfield, hty, howner⟩ := hwf.2.2.2 ref href
  cases hsource : spec.source with
  | initial value =>
      exact Or.inl ⟨spec, value, hfield, hsource, hty, howner⟩
  | event writer =>
      obtain ⟨_, hwriter⟩ := G.node_get_of_field_event_source hfield hsource
      have hwriterLt : writer < G.nodeCount := by
        change writer < G.nodes.length
        exact (List.getElem?_eq_some_iff.mp hwriter).1
      let prior : Fin G.nodeCount := ⟨writer, hwriterLt⟩
      have htarget : ref.field = G.nodeTarget prior :=
        G.field_eq_nodeTarget_of_event_source hfield hsource
      have hlt : (prior : Nat) < (node : Nat) := by
        simpa [prior, Graph.fieldAvailableBefore, hfield, hsource] using havailable
      have hprereq : prior ∈ G.prereqs node :=
        G.nodeTarget_mem_prereqs_of_read (G.nodes_get?_nodeRow node)
          (G.nodes_get?_nodeRow prior) hlt (by simpa only [htarget] using hread)
      have hproducerWF := supported.graphWF prior (G.nodeRow prior)
        (G.nodes_get?_nodeRow prior)
      have hfieldTarget := G.field?_nodeTarget (G.nodes_get?_nodeRow prior)
      rw [← htarget, hfield] at hfieldTarget
      have hspec := Option.some.inj hfieldTarget
      have hrefty : ref.ty = ty := by
        calc
          ref.ty = spec.ty := hty.symm
          _ = (G.nodeRow prior).ty := by
            simpa using congrArg FieldSpec.ty hspec
          _ = ty := supported.rowType prior
      refine Or.inr ⟨prior, htarget, hrefty, hcompleted prior hprereq, ?_⟩
      cases hproducer : (G.nodeRow prior).sem with
      | sample dist => exact False.elim (supported.noSamples prior dist hproducer)
      | commit owner priorGuard =>
          have hownerEq : owner = who := by
            unfold Graph.nodeWFAt at hproducerWF
            rw [hproducer] at hproducerWF
            have : some owner = spec.owner := by
              rw [hspec]
              exact hproducerWF.2.2.1.symm
            rcases howner with hpublic | hwho
            · rw [hpublic] at this
              cases this
            · exact Option.some.inj (this.trans hwho)
          subst owner
          exact Or.inl ⟨priorGuard, rfl⟩
      | reveal source =>
          unfold Graph.nodeWFAt at hproducerWF
          rw [hproducer] at hproducerWF
          obtain ⟨sourceSpec, _, _, _, hpublic⟩ := hproducerWF.2
          exact Or.inr ⟨source, rfl, hpublic⟩

end Vegas.EventGraph.SealedFragment
