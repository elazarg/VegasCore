/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionPolicy
import Vegas.Compile.SealedReadOrigin
import Vegas.Compile.SealedDecodeLaws
import Interaction.SealedResolutionEvents

/-! # Public stores reconstructed from sealed-message events

Only public initial fields and opening events contribute values. Acceptance
events retain opaque handles. These graph-relative laws do not use source syntax,
source accounting, or a source payout projection.
-/

noncomputable section

namespace Vegas.EventGraph.Graph

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Initial graph fields whose ownership metadata marks them public. -/
def initialPublicStore (G : Graph Player L) : Store L := fun field =>
  match G.field? field with
  | none => none
  | some spec => if spec.owner = none then spec.initialValue? else none

/-- Replay public openings without inspecting accepted commitment handles. -/
def replayPublicOpenings (G : Graph Player L) (ty : L.Ty) (store : Store L) :
    List (SealedProgram.Event Player (L.Val ty)) → Store L
  | [] => store
  | .accepted _ _ :: rest => G.replayPublicOpenings ty store rest
  | .opened node value :: rest =>
      G.replayPublicOpenings ty (store.set (G.nodeTarget node) ⟨ty, value⟩) rest

/-- Store observable from public initial data and the public event log alone. -/
def publicSealedStore (G : Graph Player L) (ty : L.Ty)
    (events : List (SealedProgram.Event Player (L.Val ty))) : Store L :=
  G.replayPublicOpenings ty G.initialPublicStore events

private theorem replayPublicOpenings_available (G : Graph Player L)
    (ty : L.Ty) (store : Store L) (events : List (SealedProgram.Event Player (L.Val ty)))
    (field : Nat) (havailable : (Store.getAs store field ty).isSome) :
    (Store.getAs (G.replayPublicOpenings ty store events) field ty).isSome := by
  induction events generalizing store with
  | nil => exact havailable
  | cons event rest ih =>
      cases event with
      | accepted node handle => exact ih store havailable
      | opened node value =>
          apply ih
          by_cases heq : field = G.nodeTarget node
          · subst field
            simp [Store.getAs, TypedValue.as?]
          · rw [Store.getAs_set_ne store heq]
            exact havailable

/-- Any recorded opening makes its target field available to public outcome
evaluation. Later openings have the same type and preserve availability. -/
theorem publicSealedStore_available_of_opened (G : Graph Player L)
    (ty : L.Ty) (events : List (SealedProgram.Event Player (L.Val ty)))
    (node : Nat) (value : L.Val ty) (hopened : .opened node value ∈ events) :
    (Store.getAs (G.publicSealedStore ty events) (G.nodeTarget node) ty).isSome := by
  suffices ∀ store, (Store.getAs (G.replayPublicOpenings ty store events)
      (G.nodeTarget node) ty).isSome from this G.initialPublicStore
  induction events with
  | nil => simp at hopened
  | cons event rest ih =>
      intro store
      rcases List.mem_cons.mp hopened with rfl | htail
      · rw [replayPublicOpenings]
        apply G.replayPublicOpenings_available
        simp [Store.getAs, TypedValue.as?]
      · cases event <;> exact ih htail _

private theorem replayPublicOpenings_preserves_value (G : Graph Player L)
    (ty : L.Ty) (store : Store L) (events : List (SealedProgram.Event Player (L.Val ty)))
    (node : Nat) (value : L.Val ty)
    (hvalues : ∀ other, .opened node other ∈ events → other = value)
    (hstore : Store.getAs store (G.nodeTarget node) ty = some value) :
    Store.getAs (G.replayPublicOpenings ty store events) (G.nodeTarget node) ty =
      some value := by
  induction events generalizing store with
  | nil => exact hstore
  | cons event rest ih =>
      have htail : ∀ other, .opened node other ∈ rest → other = value := by
        intro other hother
        exact hvalues other (List.mem_cons_of_mem event hother)
      cases event with
      | accepted index handle => exact ih store htail hstore
      | opened index openedValue =>
          apply ih _ htail
          by_cases heq : index = node
          · subst index
            rw [hvalues openedValue (List.mem_cons_self ..)]
            simp [Store.getAs, TypedValue.as?]
          · have hne : G.nodeTarget node ≠ G.nodeTarget index := by
              unfold nodeTarget
              omega
            rw [Store.getAs_set_ne store hne]
            exact hstore

/-- If every opening at a node has the same value and an opening exists,
public reconstruction reads that value. Event-node uniqueness is unnecessary. -/
theorem publicSealedStore_getAs_of_opened (G : Graph Player L)
    (ty : L.Ty) (events : List (SealedProgram.Event Player (L.Val ty)))
    (node : Nat) (value : L.Val ty)
    (hopened : .opened node value ∈ events)
    (hvalues : ∀ other, .opened node other ∈ events → other = value) :
    Store.getAs (G.publicSealedStore ty events) (G.nodeTarget node) ty = some value := by
  suffices ∀ store, Store.getAs (G.replayPublicOpenings ty store events)
      (G.nodeTarget node) ty = some value from this G.initialPublicStore
  induction events with
  | nil => simp at hopened
  | cons event rest ih =>
      intro store
      have htail : ∀ other, .opened node other ∈ rest → other = value := by
        intro other hother
        exact hvalues other (List.mem_cons_of_mem event hother)
      rcases List.mem_cons.mp hopened with rfl | hrest
      · rw [replayPublicOpenings]
        apply G.replayPublicOpenings_preserves_value ty _ rest node value htail
        simp [Store.getAs, TypedValue.as?]
      · cases event <;> exact ih hrest htail _

private theorem replayPublicOpenings_getAs_initial (G : Graph Player L)
    (ty : L.Ty) (store : Store L) (events : List (SealedProgram.Event Player (L.Val ty)))
    (field : Nat) (fieldTy : L.Ty) (hfield : ∀ node, field ≠ G.nodeTarget node) :
    Store.getAs (G.replayPublicOpenings ty store events) field fieldTy =
      Store.getAs store field fieldTy := by
  induction events generalizing store with
  | nil => rfl
  | cons event rest ih =>
      cases event with
      | accepted node handle => exact ih store
      | opened node value =>
          rw [replayPublicOpenings, ih, Store.getAs_set_ne store (hfield node)]

/-- Public initial data survives replay unchanged; accepted handles supply no
public values and opening targets are freshly allocated event fields. -/
theorem publicSealedStore_getAs_initial (G : Graph Player L)
    (ty : L.Ty) (events : List (SealedProgram.Event Player (L.Val ty)))
    (field : Nat) (spec : FieldSpec Player L) (value : L.Val spec.ty)
    (hfield : G.field? field = some spec) (hsource : spec.source = .initial value)
    (hpublic : spec.owner = none) :
    Store.getAs (G.publicSealedStore ty events) field spec.ty = some value := by
  rw [publicSealedStore, G.replayPublicOpenings_getAs_initial ty _ events field spec.ty
    (G.initial_field_ne_target field spec value hfield hsource)]
  simp [Store.getAs, initialPublicStore, hfield, hpublic, FieldSpec.initialValue?,
    hsource, TypedValue.as?]

end Vegas.EventGraph.Graph

namespace Vegas.EventGraph.SealedFragment

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

omit [DecidableEq (L.Val ty)] in
/-- Every typed public field is available after completion, including runs
with commitment and reveal defaults. No source decoding is assumed. -/
theorem publicSealedStore_available_of_complete
    (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.PublicState Player (L.Val ty))
    (hinvariant : SealedResolution.PublicEventInvariant
      (supported.resolvingRuntime nullValue window) state)
    (hcomplete : (supported.resolvingRuntime nullValue window).complete state = true)
    (ref : FieldRef L) (hpublic : G.fieldRefPublic ref) :
    ∃ value, Store.getAs (G.publicSealedStore ty state.events)
      ref.field ref.ty = some value := by
  rcases supported.publicField_origin ref hpublic with
    ⟨spec, value, hfield, hsource, hty, howner⟩ |
      ⟨node, producer, owner, guard, htarget, hrefty, hsem, hcommit⟩
  · rw [← hty]
    exact ⟨value, G.publicSealedStore_getAs_initial ty state.events
      ref.field spec value hfield hsource howner⟩
  · have hcompleted : state.completed node.val = true := by
      apply List.all_eq_true.mp hcomplete node.val
      have hlen : supported.compile.rules.length = G.nodeCount := by
        simp [SealedFragment.compile, Graph.nodeOrder]
      simpa only [List.mem_range, resolvingRuntime, hlen] using node.isLt
    have hrule : supported.compile.rules[node.val]? =
        some ⟨.reveal owner producer.val, G.messagePrerequisites node⟩ := by
      rw [supported.compile_rule]
      exact congrArg some (G.sealedRule_reveal_eq node producer owner guard hsem hcommit)
    obtain ⟨value, hopened⟩ := hinvariant.opened_of_completed_reveal
      node.val owner producer.val (G.messagePrerequisites node) hrule hcompleted
    have havailable := G.publicSealedStore_available_of_opened ty
      state.events node.val value hopened
    rw [htarget, hrefty]
    exact Option.isSome_iff_exists.mp havailable

omit [DecidableEq (L.Val ty)] in
/-- Public values of a completed log agree with a specified reachable source
realization whenever every opening has that realization's value. The statement
uses public event provenance, not a particular commitment catalog or decoder. -/
theorem publicSealedStore_agrees_of_opened_values
    (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.PublicState Player (L.Val ty))
    (hinvariant : SealedResolution.PublicEventInvariant
      (supported.resolvingRuntime nullValue window) state)
    (hcomplete : (supported.resolvingRuntime nullValue window).complete state = true)
    (cfg : ReachableConfig G)
    (hvalues : ∀ index value, .opened index value ∈ state.events →
      cfg.1.store (G.nodeTarget index) = some (⟨ty, value⟩ : TypedValue L))
    (ref : FieldRef L) (hpublic : G.fieldRefPublic ref) :
    Store.getAs (G.publicSealedStore ty state.events) ref.field ref.ty =
      Store.getAs cfg.1.store ref.field ref.ty := by
  rcases supported.publicField_origin ref hpublic with
    ⟨spec, value, hfield, hsource, hty, howner⟩ |
      ⟨node, producer, owner, guard, htarget, hrefty, hsem, hcommit⟩
  · rw [← hty, G.publicSealedStore_getAs_initial ty state.events
      ref.field spec value hfield hsource howner]
    have hcfg := Graph.reachable_store_eq_initial_of_not_nodeTarget cfg.2 ref.field
      (fun node => G.initial_field_ne_target ref.field spec value hfield hsource node.val)
    simp [Store.getAs, hcfg, Graph.initialStore, hfield, FieldSpec.initialValue?,
      hsource, TypedValue.as?]
  · have hcompleted : state.completed node.val = true := by
      apply List.all_eq_true.mp hcomplete node.val
      have hlen : supported.compile.rules.length = G.nodeCount := by
        simp [SealedFragment.compile, Graph.nodeOrder]
      simpa only [List.mem_range, resolvingRuntime, hlen] using node.isLt
    have hrule : supported.compile.rules[node.val]? =
        some ⟨.reveal owner producer.val, G.messagePrerequisites node⟩ := by
      rw [supported.compile_rule]
      exact congrArg some (G.sealedRule_reveal_eq node producer owner guard hsem hcommit)
    obtain ⟨value, hopened⟩ := hinvariant.opened_of_completed_reveal
      node.val owner producer.val (G.messagePrerequisites node) hrule hcompleted
    have hsame : ∀ other, .opened node.val other ∈ state.events → other = value := by
      intro other hother
      have heq := Option.some.inj ((hvalues node.val other hother).symm.trans
        (hvalues node.val value hopened))
      have htyped := congrArg (fun entry : TypedValue L => entry.as? ty) heq
      simpa [TypedValue.as?] using htyped
    rw [htarget, hrefty, G.publicSealedStore_getAs_of_opened ty state.events node.val value
      hopened hsame]
    simp [Store.getAs, hvalues node.val value hopened, TypedValue.as?]

omit [DecidableEq (L.Val ty)] in
private theorem replayPublicOpenings_agrees
    (supported : SealedFragment G ty)
    (service : IdealCommitments Player Nat (L.Val ty))
    (allEvents events : List (SealedProgram.Event Player (L.Val ty)))
    (hsub : ∀ event, event ∈ events → event ∈ allEvents)
    (haccepted : ∀ node handle, .accepted node handle ∈ allEvents →
      ∃ owner value rule,
        supported.compile.rules[node]? = some rule ∧ rule.kind = .commit owner ∧
          handle = (owner, node) ∧ service.lookup handle = some value)
    (publicStore : Store L) (cfg result : Config G)
    (hagrees : ∀ field spec, G.field? field = some spec → spec.owner = none →
      publicStore field = cfg.store field)
    (hdecode : G.decodeSealedFrom ty service cfg events = some result) :
    ∀ field spec, G.field? field = some spec → spec.owner = none →
      G.replayPublicOpenings ty publicStore events field = result.store field := by
  induction events generalizing publicStore cfg with
  | nil =>
      cases Option.some.inj hdecode
      exact hagrees
  | cons event rest ih =>
      have htail : ∀ prior, prior ∈ rest → prior ∈ allEvents := by
        intro prior hprior
        exact hsub prior (List.mem_cons_of_mem event hprior)
      unfold Graph.decodeSealedFrom at hdecode
      unfold Graph.decodeSealedEvent at hdecode
      split at hdecode
      · rename_i hnode
        cases event with
        | accepted node handle =>
            cases hlookup : service.lookup handle with
            | none => simp [hlookup] at hdecode
            | some value =>
                simp only [hlookup, Option.map_some, Option.bind_some] at hdecode
                dsimp only [Graph.replayPublicOpenings]
                apply ih htail _ _ ?_ hdecode
                intro field spec hfield hpublic
                by_cases heq : field = G.nodeTarget node
                · subst field
                  obtain ⟨owner, stored, rule, hrule, hkind, hhandle, _⟩ :=
                    haccepted node handle (hsub _ (List.mem_cons_self ..))
                  obtain ⟨index, guard, hindex, hsem⟩ :=
                    supported.ruleAt_commit hrule hkind
                  have htarget := G.field?_nodeTarget
                    (G.nodes_get?_nodeRow index)
                  rw [hindex] at htarget
                  rw [hfield] at htarget
                  have hwf := supported.graphWF index (G.nodeRow index)
                    (G.nodes_get?_nodeRow index)
                  unfold Graph.nodeWFAt at hwf
                  rw [hsem] at hwf
                  have howner : spec.owner = some owner := by
                    rw [Option.some.inj htarget]
                    exact hwf.2.2.1
                  rw [hpublic] at howner
                  contradiction
                · simp only [Config.completeNode, SealedProgram.Event.node]
                  rw [Store.set_ne _ heq]
                  exact hagrees field spec hfield hpublic
        | opened node value =>
            simp only [Option.bind_some] at hdecode
            dsimp only [Graph.replayPublicOpenings]
            apply ih htail _ _ ?_ hdecode
            intro field spec hfield hpublic
            by_cases heq : field = G.nodeTarget node
            · subst field
              simp [Config.completeNode, SealedProgram.Event.node]
            · simp only [Config.completeNode, SealedProgram.Event.node]
              rw [Store.set_ne _ heq, Store.set_ne _ heq]
              exact hagrees field spec hfield hpublic
      · simp at hdecode

omit [DecidableEq (L.Val ty)] in
/-- Public reconstruction agrees with proof-side decoding on every typed
public graph field.  The result does not inspect the ideal service. -/
theorem publicSealedStore_agrees
    (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.ApplicationState Player (L.Val ty))
    (hinvariant : SealedResolution.EventInvariant
      (supported.resolvingRuntime nullValue window) state)
    (cfg : Config G)
    (hdecode : G.decodeSealedFrom ty state.service (Config.initial G)
      state.visible.events = some cfg)
    (ref : FieldRef L) (hpublic : G.fieldRefPublic ref) :
    Store.getAs (G.publicSealedStore ty state.visible.events) ref.field ref.ty =
      Store.getAs cfg.store ref.field ref.ty := by
  obtain ⟨spec, hfield, hty, howner⟩ := hpublic
  have hagrees := supported.replayPublicOpenings_agrees state.service
    state.visible.events state.visible.events (fun _ h => h)
    hinvariant.acceptedBinding.accepted G.initialPublicStore (Config.initial G) cfg
    (by
      intro field initialSpec hinitial hpublic
      simp only [Graph.initialPublicStore, hinitial, if_pos hpublic,
        Config.initial, Graph.initialStore]) hdecode ref.field spec hfield howner
  unfold Store.getAs Graph.publicSealedStore
  rw [hagrees]

end Vegas.EventGraph.SealedFragment
