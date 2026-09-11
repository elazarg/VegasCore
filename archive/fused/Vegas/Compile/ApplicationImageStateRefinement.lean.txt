/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.BindingImageRefinement
import Vegas.EventGraph.Confluence

/-! # Binding provenance in public-application refinement

The graph configuration is proof-only. Each accepted handle refers to a
present sealed graph field owned by that principal. A recoverable frozen value
agrees with the graph value; absent or ill-typed frozen values impose no value
equation. This permits unopenable bindings without fabricating a native secret.
-/

namespace Vegas.ApplicationImage

open EventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr} {G : Graph P L}

/-- Opaque handles and public defaults each agree with a present private graph
field. Only opaque bindings constrain the private frozen snapshot. -/
structure State.BindingsRepresent (state : State P L) (cfg : Config G) : Prop where
  opaqueBinding : ∀ field handle, state.memory.accepted field = some (.opaque handle) →
    ∃ (spec : FieldSpec P L) (value : L.Val spec.ty),
      G.field? field = some spec ∧ spec.owner = some handle.1 ∧
      Store.getAs cfg.store field spec.ty = some value ∧
      ∀ recovered, (state.frozen field).bind (fun typed => typed.as? spec.ty) =
        some recovered → recovered = value
  publicDefault : ∀ field typed,
    state.memory.accepted field = some (.publicDefault typed) →
      ∃ spec : FieldSpec P L,
        G.field? field = some spec ∧ spec.owner.isSome = true ∧
          typed.ty = spec.ty ∧ cfg.store field = some typed

/-- An absent source value rules out either kind of accepted binding at that
field. -/
theorem State.BindingsRepresent.accepted_eq_none_of_store_eq_none
    {state : State P L} {cfg : Config G}
    (hbindings : state.BindingsRepresent cfg) (field : Nat)
    (hstore : cfg.store field = none) : state.memory.accepted field = none := by
  cases haccepted : state.memory.accepted field with
  | none => rfl
  | some disposition =>
      cases disposition with
      | publicDefault typed =>
          obtain ⟨_, _, _, _, hvalue⟩ :=
            hbindings.publicDefault field typed haccepted
          rw [hstore] at hvalue
          contradiction
      | «opaque» handle =>
          obtain ⟨spec, value, _, _, hvalue, _⟩ :=
            hbindings.opaqueBinding field handle haccepted
          simp [Store.getAs, hstore] at hvalue

/-- Completing a previously unfinished node cannot overwrite an earlier
represented binding: that binding already has a typed value in the graph. -/
theorem State.BindingsRepresent.completeNode
    {state : State P L} {cfg : Config G}
    (hbindings : state.BindingsRepresent cfg) (hreachable : Reachable G cfg)
    (node : Fin G.nodeCount) (hnode : node ∉ cfg.done) (written : TypedValue L) :
    state.BindingsRepresent (cfg.completeNode node written) := by
  constructor
  · intro field handle haccepted
    obtain ⟨spec, value, hfield, howner, hvalue, hfrozen⟩ :=
      hbindings.opaqueBinding field handle haccepted
    have hne : field ≠ G.nodeTarget node := by
      intro heq
      rw [heq, reachable_getAs_nodeTarget_eq_none hreachable node hnode spec.ty] at hvalue
      contradiction
    refine ⟨spec, value, hfield, howner, ?_, hfrozen⟩
    simpa [Config.completeNode, Store.getAs, Store.set, hne] using hvalue
  · intro field typed haccepted
    obtain ⟨spec, hfield, howner, htype, hvalue⟩ :=
      hbindings.publicDefault field typed haccepted
    have hne : field ≠ G.nodeTarget node := by
      intro heq
      have hpresent : Store.getAs cfg.store (G.nodeTarget node) typed.ty =
          some typed.value := by
        simp [heq ▸ hvalue, Store.getAs, TypedValue.as?]
      rw [reachable_getAs_nodeTarget_eq_none hreachable node hnode typed.ty] at hpresent
      contradiction
    refine ⟨spec, hfield, howner, htype, ?_⟩
    simpa [Config.completeNode, Store.set, hne] using hvalue

/-- A batch of fresh graph writes preserves every existing accepted binding.
The nodes need only be unfinished at the original checkpoint; no hidden source
context or intermediate runtime observation is required. -/
theorem State.BindingsRepresent.completeNodes
    {state : State P L} {cfg : Config G}
    (hbindings : state.BindingsRepresent cfg) (hreachable : Reachable G cfg)
    (steps : List (Fin G.nodeCount × TypedValue L))
    (hfresh : ∀ step ∈ steps, step.1 ∉ cfg.done) :
    state.BindingsRepresent (cfg.completeNodes steps) := by
  constructor
  · intro field handle haccepted
    obtain ⟨spec, value, hfield, howner, hvalue, hfrozen⟩ :=
      hbindings.opaqueBinding field handle haccepted
    refine ⟨spec, value, hfield, howner, ?_, hfrozen⟩
    rw [cfg.completeNodes_getAs_of_not_targets steps]
    · exact hvalue
    · intro step hstep heq
      rw [heq, reachable_getAs_nodeTarget_eq_none hreachable step.1
        (hfresh step hstep) spec.ty] at hvalue
      contradiction
  · intro field typed haccepted
    obtain ⟨spec, hfield, howner, htype, hvalue⟩ :=
      hbindings.publicDefault field typed haccepted
    have htargets : ∀ step ∈ steps, field ≠ G.nodeTarget step.1 := by
      intro step hstep heq
      have hpresent : Store.getAs cfg.store (G.nodeTarget step.1) typed.ty =
          some typed.value := by
        simp [heq ▸ hvalue, Store.getAs, TypedValue.as?]
      rw [reachable_getAs_nodeTarget_eq_none hreachable step.1
        (hfresh step hstep) typed.ty] at hpresent
      contradiction
    refine ⟨spec, hfield, howner, htype, ?_⟩
    have hget : Store.getAs (cfg.completeNodes steps).store field typed.ty =
        some typed.value := by
      rw [cfg.completeNodes_getAs_of_not_targets steps htargets]
      simp [hvalue, Store.getAs, TypedValue.as?]
    cases hfinal : (cfg.completeNodes steps).store field with
    | none => simp [Store.getAs, hfinal] at hget
    | some final =>
        have hdecode : final.as? typed.ty = some typed.value := by
          simpa only [Store.getAs, hfinal, Option.bind_some] using hget
        have htyped : final = typed := by
          have heq := TypedValue.eq_mk_of_as?_eq_some final typed.ty typed.value hdecode
          cases typed
          exact heq
        exact congrArg some htyped

/-- Completing a pair of fresh nodes changes no previously accepted binding. -/
theorem State.BindingsRepresent.completePair
    {state : State P L} {cfg : Config G}
    (hbindings : state.BindingsRepresent cfg) (hreachable : Reachable G cfg)
    (choice publication : Fin G.nodeCount) (written : TypedValue L)
    (hchoice : choice ∉ cfg.done) (hpublication : publication ∉ cfg.done) :
    state.BindingsRepresent
      ((cfg.completeNode choice written).completeNode publication written) := by
  apply hbindings.completeNodes hreachable [(choice, written), (publication, written)]
  intro step hstep
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hstep
  rcases hstep with rfl | rfl
  · exact hchoice
  · exact hpublication

/-- A typed accepted snapshot is recorded with the value written by its graph
commit. Unopenable snapshots impose no equation and remain permitted. -/
theorem State.BindingsRepresent.bind
    {state : State P L} {cfg : Config G}
    (hbindings : state.BindingsRepresent cfg) (hreachable : Reachable G cfg)
    (hwf : G.WF) (code : BindingCode P L) (node : Fin G.nodeCount)
    (hfieldTarget : code.sourceField = G.nodeTarget node)
    (handle : CommitmentHandle P Nat) (howner : handle.1 = code.owner)
    (written : TypedValue L)
    (hstep : CommitStep G cfg code.owner ⟨node, written⟩)
    (hsnapshot : ∀ recovered,
      (state.prepared.lookup handle).bind (fun typed => typed.as? written.ty) = some recovered →
        recovered = written.value) :
    (state.bind code handle).BindingsRepresent (cfg.completeNode node written) := by
  have hnodeWF := hwf node hstep.row hstep.row_get
  unfold Graph.nodeWFAt at hnodeWF
  rw [hstep.sem_eq] at hnodeWF
  have hty : hstep.row.ty = written.ty :=
    hnodeWF.2.1.trans (congrArg TypedValue.ty hstep.written_eq_action)
  let spec : FieldSpec P L :=
    { ty := written.ty, owner := some code.owner, source := .event node }
  have hfield : G.field? code.sourceField = some spec := by
    rw [hfieldTarget, G.field?_nodeTarget hstep.row_get, hty, hnodeWF.2.2.1]
  have hprior := hbindings.completeNode hreachable node hstep.ready.1 written
  constructor
  · intro field accepted haccepted
    by_cases heq : field = code.sourceField
    · subst field
      have heqHandle : handle = accepted := by
        simpa [State.bind] using haccepted
      subst accepted
      refine ⟨spec, written.value, hfield, ?_, ?_, ?_⟩
      · simpa only [spec] using congrArg some howner.symm
      · simp [spec, hfieldTarget, Config.completeNode, Store.getAs, TypedValue.as?]
      · simpa [State.bind, spec] using hsnapshot
    · have haccepted : state.memory.accepted field = some (.opaque accepted) := by
        simpa only [State.bind, if_neg heq] using haccepted
      simpa only [State.bind, if_neg heq] using
        hprior.opaqueBinding field accepted haccepted
  · intro field typed haccepted
    have heq : field ≠ code.sourceField := by
      intro heq
      subst field
      simp [State.bind] at haccepted
    have hpriorAccepted : state.memory.accepted field = some (.publicDefault typed) := by
      simpa only [State.bind, if_neg heq] using haccepted
    simpa only [State.bind, if_neg heq] using
      hprior.publicDefault field typed hpriorAccepted

/-- A source-certified public default represents the same graph commit without
creating an opaque handle or a private frozen snapshot. -/
theorem State.BindingsRepresent.defaultBind
    {state : State P L} {cfg : Config G}
    (hbindings : state.BindingsRepresent cfg) (hreachable : Reachable G cfg)
    (hwf : G.WF) (code : BindingCode P L) (node : Fin G.nodeCount)
    (hfieldTarget : code.sourceField = G.nodeTarget node)
    (written : TypedValue L) (hstep : CommitStep G cfg code.owner ⟨node, written⟩) :
    (state.defaultBind code written).BindingsRepresent
      (cfg.completeNode node written) := by
  have hnodeWF := hwf node hstep.row hstep.row_get
  unfold Graph.nodeWFAt at hnodeWF
  rw [hstep.sem_eq] at hnodeWF
  have hty : hstep.row.ty = written.ty :=
    hnodeWF.2.1.trans (congrArg TypedValue.ty hstep.written_eq_action)
  let spec : FieldSpec P L :=
    { ty := written.ty, owner := some code.owner, source := .event node }
  have hfield : G.field? code.sourceField = some spec := by
    rw [hfieldTarget, G.field?_nodeTarget hstep.row_get, hty, hnodeWF.2.2.1]
  have hprior := hbindings.completeNode hreachable node hstep.ready.1 written
  constructor
  · intro field handle haccepted
    have heq : field ≠ code.sourceField := by
      intro heq
      subst field
      simp [State.defaultBind] at haccepted
    have hpriorAccepted : state.memory.accepted field = some (.opaque handle) := by
      simpa only [State.defaultBind, if_neg heq] using haccepted
    simpa only [State.defaultBind, if_neg heq] using
      hprior.opaqueBinding field handle hpriorAccepted
  · intro field typed haccepted
    by_cases heq : field = code.sourceField
    · subst field
      have htyped : written = typed := by
        simpa [State.defaultBind] using haccepted
      subst typed
      refine ⟨spec, hfield, ?_, rfl, ?_⟩
      · simp [spec]
      · simp [hfieldTarget, Config.completeNode, Store.set]
    · have hpriorAccepted : state.memory.accepted field = some (.publicDefault typed) := by
        simpa only [State.defaultBind, if_neg heq] using haccepted
      simpa only [State.defaultBind, if_neg heq] using
        hprior.publicDefault field typed hpriorAccepted

/-- Public storage, reachability, and accepted private-binding provenance are
separate components of the proof-facing runtime relation. -/
structure State.Refines (state : State P L) (cfg : Config G) : Prop where
  memory : state.memory.Represents cfg
  reachable : Reachable G cfg
  bindings : state.BindingsRepresent cfg

/-- An unfinished graph output has no accepted native binding disposition. -/
theorem State.Refines.accepted_eq_none_of_not_done {state : State P L} {cfg : Config G}
    (hrefines : state.Refines cfg) (node : Fin G.nodeCount) (hnotDone : node ∉ cfg.done) :
    state.memory.accepted (G.nodeTarget node) = none := by
  apply hrefines.bindings.accepted_eq_none_of_store_eq_none (G.nodeTarget node)
  cases hstored : cfg.store (G.nodeTarget node) with
  | none => rfl
  | some typed =>
      have hpresent : Store.getAs cfg.store (G.nodeTarget node) typed.ty =
          some typed.value := by
        simp [Store.getAs, hstored, TypedValue.as?]
      have habsent := reachable_getAs_nodeTarget_eq_none hrefines.reachable node
        hnotDone typed.ty
      rw [habsent] at hpresent
      contradiction

/-- Empty commitment-service initialization refines the original graph
initialization. This is safety only: it does not provision sealed initial inputs
or prove that their future publication instructions can become ready. -/
theorem State.initial_refines (graph : Graph P L) :
    (State.initial (Memory.initial graph)).Refines (Config.initial graph) := by
  refine ⟨Memory.initial_represents graph, Reachable.initial, ?_⟩
  constructor
  · intro field handle haccepted
    cases haccepted
  · intro field typed haccepted
    cases haccepted

/-- Private preparation leaves the represented graph checkpoint unchanged. -/
theorem State.Refines.register {state : State P L} {cfg : Config G}
    (hrefines : state.Refines cfg) (who : P) (slot : Nat) (value : TypedValue L) :
    (state.register who slot value).Refines cfg :=
  ⟨hrefines.memory, hrefines.reachable,
    ⟨hrefines.bindings.opaqueBinding, hrefines.bindings.publicDefault⟩⟩

/-- Advancing the public clock changes no source field or binding witness. -/
theorem State.Refines.advance {state : State P L} {cfg : Config G}
    (hrefines : state.Refines cfg) (clock : Nat) :
    (state.advance clock).Refines cfg :=
  ⟨⟨hrefines.memory.completed, hrefines.memory.outside, hrefines.memory.stored,
      hrefines.memory.publicFields⟩, hrefines.reachable,
    ⟨hrefines.bindings.opaqueBinding, hrefines.bindings.publicDefault⟩⟩

/-- Binding admission preserves the complete relation, including the accepted
snapshot's connection to the source field. -/
theorem State.Refines.bind {state : State P L} {cfg : Config G}
    (hrefines : state.Refines cfg) (hwf : G.WF)
    (code : BindingCode P L) (node : Fin G.nodeCount)
    (hnode : code.node = node.val) (hfield : code.sourceField = G.nodeTarget node)
    (handle : CommitmentHandle P Nat) (howner : handle.1 = code.owner)
    (written : TypedValue L)
    (hstep : CommitStep G cfg code.owner ⟨node, written⟩)
    (hsnapshot : ∀ recovered,
      (state.prepared.lookup handle).bind (fun typed => typed.as? written.ty) = some recovered →
        recovered = written.value) :
    (state.bind code handle).Refines (cfg.completeNode node written) := by
  obtain ⟨hmemory, hreachable⟩ := state.bind_reachable_represents cfg hrefines.memory
    hwf hrefines.reachable code node hnode handle written hstep
  exact ⟨hmemory, hreachable, hrefines.bindings.bind hrefines.reachable hwf code node
    hfield handle howner written hstep hsnapshot⟩

/-- Installing a typed public default preserves the complete source relation. -/
theorem State.Refines.defaultBind {state : State P L} {cfg : Config G}
    (hrefines : state.Refines cfg) (hwf : G.WF)
    (code : BindingCode P L) (node : Fin G.nodeCount)
    (hnode : code.node = node.val) (hfield : code.sourceField = G.nodeTarget node)
    (written : TypedValue L)
    (hstep : CommitStep G cfg code.owner ⟨node, written⟩) :
    (state.defaultBind code written).Refines (cfg.completeNode node written) := by
  have hopaque := state.bind_reachable_represents cfg hrefines.memory hwf
    hrefines.reachable code node hnode (code.owner, code.sourceSlot) written hstep
  have hmemory : (state.defaultBind code written).memory.Represents
      (cfg.completeNode node written) := by
    exact ⟨hopaque.1.completed, hopaque.1.outside, hopaque.1.stored,
      hopaque.1.publicFields⟩
  exact ⟨hmemory, hopaque.2, hrefines.bindings.defaultBind
    hrefines.reachable hwf code node hfield written hstep⟩

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.State.Refines.bind' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.State.Refines.bind

/-- info: 'Vegas.ApplicationImage.State.Refines.defaultBind' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.State.Refines.defaultBind
