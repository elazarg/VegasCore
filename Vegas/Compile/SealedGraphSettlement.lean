/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPublicStore
import Vegas.Compile.SealedSourceInputs
import Vegas.Compile.SealedReplay
import Vegas.EventGraph.Disclosure
import Interaction.SealedResolutionSettlement

/-! # Graph realizations of completed public settlement

For a sealed graph with unique direct reveals, every completed public settlement
has a legal terminal graph realization. A player's timed-out site is represented
by that player's configured default value in the same realization. Private native
choices and the opponents' graph policy laws need not agree with this witness;
the deviation coupling supplies those laws separately.
-/

noncomputable section

namespace Vegas.EventGraph.Graph

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Logical graph choices used only to witness a public settlement. They may
differ from private registrations after a publication defaults. -/
private def revealAssignment (G : Graph Player L) {ty : L.Ty}
    (fallback : L.Val ty) (store : Store L) : Fin G.nodeCount → L.Val ty := by
  classical
  exact fun producer =>
    if found : ∃ node, (G.nodeRow node).sem = .reveal (G.nodeTarget producer) then
      (Store.getAs store (G.nodeTarget (Classical.choose found).val) ty).getD fallback
    else fallback

end Vegas.EventGraph.Graph

namespace Vegas.EventGraph.SealedFragment

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty}

private theorem exists_terminal_values [Finite Player]
    (supported : SealedFragment G ty) (hguards : GuardLive G) (fallback : L.Val ty)
    (values : Fin G.nodeCount → L.Val ty) :
    ∃ cfg : ReachableConfig G,
      Terminal G cfg.1 ∧
      ∀ node owner guard, (G.nodeRow node).sem = .commit owner guard →
        cfg.1.nodeValues fallback node = values node := by
  let : Fintype Player := Fintype.ofFinite Player
  let graph := G
  let policies := fun who => supported.valuePolicy values who
  let initial : ReachableConfig graph := ⟨Config.initial graph, .initial⟩
  let law := runPolicyNodes supported.graphWF
    hguards policies initial graph.nodeOrder
  obtain ⟨cfg, hcfg⟩ := law.support_nonempty
  have hterminal : Terminal graph cfg.1 := runPolicyNodes_terminal
    supported.graphWF hguards
    policies initial graph.nodeOrder graph.nodeOrder_readyOrder
    (fun node => Or.inr (by simp)) cfg hcfg
  refine ⟨cfg, hterminal, ?_⟩
  intro node owner guard hsem
  have hchoices := runPolicyNodes_support_commitValues supported.graphWF
    hguards policies initial
    (CommitValuesSupported.initial _) graph.nodeOrder cfg hcfg
  obtain ⟨reads, _, choice, hchoice, hvalue⟩ := hchoices node (hterminal node) owner guard hsem
  simp only [policies, SealedFragment.valuePolicy, FinDist.mem_support_pure] at hchoice
  subst choice
  change cfg.1.store (graph.nodeTarget node) =
    some (⟨guard.ty, cast (congrArg L.Val
      (supported.commitType node owner guard hsem).symm) (values node)⟩ : TypedValue L)
    at hvalue
  rw [Config.nodeValues, Store.getAs, hvalue]
  simp only [TypedValue.as?, dif_pos (supported.commitType node owner guard hsem),
    cast_cast, cast_eq, Option.getD_some]

private theorem revealAssignment_reveal
    (hunique : G.UniqueReveals) (fallback : L.Val ty) (store : Store L)
    (node producer : Fin G.nodeCount)
    (hsem : (G.nodeRow node).sem =
      .reveal (G.nodeTarget producer)) :
    G.revealAssignment fallback store producer =
      (Store.getAs store (G.nodeTarget node) ty).getD fallback := by
  classical
  have found : ∃ node, (G.nodeRow node).sem =
      .reveal (G.nodeTarget producer) := ⟨node, hsem⟩
  rw [Graph.revealAssignment, dif_pos found]
  rw [hunique _ node _ (Classical.choose_spec found) hsem]

private theorem exists_terminal_public_store [Finite Player]
    (supported : SealedFragment G ty) (hguards : GuardLive G) (hunique : G.UniqueReveals)
    (fallback : L.Val ty)
    (store : Store L)
    (havailable : ∀ ref, G.fieldRefPublic ref →
      ∃ value, Store.getAs store ref.field ref.ty = some value)
    (hinitial : ∀ field (spec : FieldSpec Player L) (value : L.Val spec.ty),
      G.field? field = some spec →
      spec.source = .initial value → spec.owner = none →
      Store.getAs store field spec.ty = some value) :
    ∃ cfg : ReachableConfig G,
      Terminal G cfg.1 ∧
      (∀ ref, G.fieldRefPublic ref →
        Store.getAs store ref.field ref.ty = Store.getAs cfg.1.store ref.field ref.ty) ∧
      ∀ node owner guard, (G.nodeRow node).sem = .commit owner guard →
        cfg.1.nodeValues fallback node =
          G.revealAssignment fallback store node := by
  obtain ⟨cfg, hterminal, hvalues⟩ := supported.exists_terminal_values hguards fallback
    (G.revealAssignment fallback store)
  refine ⟨cfg, hterminal, ?_, hvalues⟩
  intro ref hpublic
  rcases supported.publicField_origin ref hpublic with
    ⟨spec, value, hfield, hsource, hty, howner⟩ |
      ⟨node, producer, owner, guard, htarget, hrefty, hsem, hcommit⟩
  · rw [← hty, hinitial ref.field spec value hfield hsource howner]
    have hcfg := Graph.reachable_store_eq_initial_of_not_nodeTarget cfg.2 ref.field
      (fun node => G.initial_field_ne_target
        ref.field spec value hfield hsource node.val)
    simp [Store.getAs, hcfg, Graph.initialStore, hfield, FieldSpec.initialValue?,
      hsource, TypedValue.as?]
  · have hav := havailable ref hpublic
    rw [htarget, hrefty] at hav ⊢
    obtain ⟨value, hvalue⟩ := hav
    rw [hvalue, Store.getAs, supported.terminal_reveal_store cfg hterminal fallback
      node producer hsem, hvalues producer owner guard hcommit,
      revealAssignment_reveal hunique fallback store node producer hsem,
      hvalue]
    simp [TypedValue.as?]

/-- Every completed invariant native state has the public store of a legal
terminal graph realization. This witness chooses the default at any commitment
whose direct reveals all publish that default, including commitments with no
direct reveal. Direct-reveal uniqueness is an explicit graph premise. Actual
private registrations and fixed source policy laws need not be preserved. -/
theorem public_store_graph_of_complete [Finite Player]
    (supported : SealedFragment G ty) (hguards : GuardLive G) (hunique : G.UniqueReveals)
    (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.PublicState Player (L.Val ty))
    (hinvariant : SealedResolution.PublicEventInvariant
      (supported.resolvingRuntime nullValue window) state)
    (hcomplete : (supported.resolvingRuntime nullValue window).complete
      state = true) :
    ∃ cfg : ReachableConfig G,
      Terminal G cfg.1 ∧
      (∀ ref, G.fieldRefPublic ref →
        Store.getAs (G.publicSealedStore ty state.events)
          ref.field ref.ty = Store.getAs cfg.1.store ref.field ref.ty) ∧
      ∀ node owner guard, (G.nodeRow node).sem = .commit owner guard →
        (∀ reveal, (G.nodeRow reveal).sem =
            .reveal (G.nodeTarget node) →
          Store.getAs (G.publicSealedStore ty state.events)
            (G.nodeTarget reveal) ty = some nullValue) →
        cfg.1.nodeValues nullValue node = nullValue := by
  classical
  obtain ⟨cfg, hterminal, hagrees, hvalues⟩ := supported.exists_terminal_public_store
    hguards hunique nullValue _
    (supported.publicSealedStore_available_of_complete nullValue window
      state hinvariant hcomplete)
    (G.publicSealedStore_getAs_initial ty state.events)
  refine ⟨cfg, hterminal, hagrees, ?_⟩
  intro node owner guard hsem hdefault
  rw [hvalues node owner guard hsem, Graph.revealAssignment]
  split
  · rename_i found
    rw [hdefault (Classical.choose found) (Classical.choose_spec found)]
    rfl
  · rfl

private theorem public_reveal_eq_default
    (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.PublicState Player (L.Val ty))
    (hinvariant : SealedResolution.PublicEventInvariant
      (supported.resolvingRuntime nullValue window) state)
    (hsettlement : SealedResolution.SettlementInvariant
      (supported.resolvingRuntime nullValue window) state)
    (hcomplete : (supported.resolvingRuntime nullValue window).complete
      state = true)
    (node producer : Fin G.nodeCount)
    (who : Player) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem =
      .reveal (G.nodeTarget producer))
    (hcommit : (G.nodeRow producer).sem = .commit who guard)
    (htimeout : node.val ∈ state.timeouts ∨ producer.val ∈ state.timeouts) :
    Store.getAs (G.publicSealedStore ty state.events)
      (G.nodeTarget node) ty = some nullValue := by
  let graph := G
  have hrule : supported.compile.rules[node.val]? =
      some ⟨.reveal who producer.val, graph.messagePrerequisites node⟩ := by
    rw [supported.compile_rule]
    exact congrArg some (graph.sealedRule_reveal_eq node producer who guard hsem hcommit)
  have hcompleted : state.completed node.val = true := by
    apply List.all_eq_true.mp hcomplete node.val
    have hlen : supported.compile.rules.length = graph.nodeCount := by
      simp [SealedFragment.compile, Graph.nodeOrder, graph]
    simpa only [List.mem_range, SealedFragment.resolvingRuntime, hlen] using node.isLt
  obtain ⟨value, hopened⟩ := hinvariant.opened_of_completed_reveal
    node.val who producer.val (graph.messagePrerequisites node) hrule hcompleted
  have hvalues : ∀ value, .opened node.val value ∈ state.events → value = nullValue := by
    intro value hvalue
    exact hsettlement.opened_eq_null_of_timeout node.val who producer.val
      (graph.messagePrerequisites node) value hrule hvalue htimeout
  apply graph.publicSealedStore_getAs_of_opened ty state.events node.val nullValue
  · rwa [hvalues value hopened] at hopened
  · exact hvalues

/-- A terminal graph realization matching all public fields records the default
at the supplied producer when either that producer or one specified direct
reveal times out.  The producer is retained in the conclusion for callers that
need an exact source decision boundary. -/
theorem public_store_graph_choice_at_producer_of_timeout [Finite Player]
    (supported : SealedFragment G ty) (hguards : GuardLive G) (hunique : G.UniqueReveals)
    (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.PublicState Player (L.Val ty))
    (hinvariant : SealedResolution.PublicEventInvariant
      (supported.resolvingRuntime nullValue window) state)
    (hsettlement : SealedResolution.SettlementInvariant
      (supported.resolvingRuntime nullValue window) state)
    (hcomplete : (supported.resolvingRuntime nullValue window).complete state = true)
    (producer : Fin G.nodeCount) (who : Player) (guard : EventGuard L)
    (hcommit : (G.nodeRow producer).sem = .commit who guard)
    (timeoutNode : Fin G.nodeCount) (htimeout : timeoutNode.val ∈ state.timeouts)
    (hsite : timeoutNode = producer ∨
      (G.nodeRow timeoutNode).sem = .reveal (G.nodeTarget producer)) :
    ∃ cfg : ReachableConfig G, Terminal G cfg.1 ∧
      (∀ ref, G.fieldRefPublic ref →
        Store.getAs (G.publicSealedStore ty state.events) ref.field ref.ty =
          Store.getAs cfg.1.store ref.field ref.ty) ∧
      cfg.1.store (G.nodeTarget producer) =
        some (⟨ty, nullValue⟩ : TypedValue L) := by
  obtain ⟨cfg, hterminal, hagrees, hdefaults⟩ :=
    supported.public_store_graph_of_complete hguards hunique nullValue window state
      hinvariant hcomplete
  refine ⟨cfg, hterminal, hagrees, ?_⟩
  rw [cfg.1.store_nodeValues (reachable_storeCoherent supported.graphWF cfg.2)
    nullValue producer (supported.rowType producer) (hterminal producer),
    hdefaults producer who guard hcommit ?_]
  intro reveal hreveal
  rcases hsite with heq | hdirect
  · exact supported.public_reveal_eq_default nullValue window state hinvariant hsettlement
      hcomplete reveal producer who guard hreveal hcommit
        (Or.inr (by simpa [heq] using htimeout))
  · have heq := hunique reveal timeoutNode _ hreveal hdirect
    subst reveal
    exact supported.public_reveal_eq_default nullValue window state hinvariant hsettlement
      hcomplete timeoutNode producer who guard hdirect hcommit (Or.inl htimeout)

/-- The same terminal graph realization matches all public fields and records
the timed-out owner's default at a commitment. This uses a graph disclosure
certificate, not a source-image assumption or an opponent-strategy claim. -/
theorem public_store_graph_choice_of_timeout [Finite Player]
    (supported : SealedFragment G ty) (hguards : GuardLive G) (hunique : G.UniqueReveals)
    (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.PublicState Player (L.Val ty))
    (hinvariant : SealedResolution.PublicEventInvariant
      (supported.resolvingRuntime nullValue window) state)
    (hsettlement : SealedResolution.SettlementInvariant
      (supported.resolvingRuntime nullValue window) state)
    (hcomplete : (supported.resolvingRuntime nullValue window).complete state = true)
    (node : Fin G.nodeCount) (who : Player) (htimeout : node.val ∈ state.timeouts)
    (howned : (∃ guard, (G.nodeRow node).sem = .commit who guard) ∨
      ∃ (producer : Fin G.nodeCount) (guard : EventGuard L),
        (G.nodeRow node).sem = .reveal (G.nodeTarget producer) ∧
        (G.nodeRow producer).sem = .commit who guard) :
    ∃ cfg : ReachableConfig G, Terminal G cfg.1 ∧
      (∀ ref, G.fieldRefPublic ref →
        Store.getAs (G.publicSealedStore ty state.events) ref.field ref.ty =
          Store.getAs cfg.1.store ref.field ref.ty) ∧
      ∃ (producer : Fin G.nodeCount) (guard : EventGuard L),
        (G.nodeRow producer).sem = .commit who guard ∧
        cfg.1.store (G.nodeTarget producer) = some (⟨ty, nullValue⟩ : TypedValue L) := by
  rcases howned with ⟨guard, hcommit⟩ | ⟨producer, guard, hsem, hcommit⟩
  · obtain ⟨cfg, hterminal, hagrees, hvalue⟩ :=
      supported.public_store_graph_choice_at_producer_of_timeout hguards hunique
        nullValue window state hinvariant hsettlement hcomplete node who guard hcommit
        node htimeout (Or.inl rfl)
    exact ⟨cfg, hterminal, hagrees, node, guard, hcommit, hvalue⟩
  · obtain ⟨cfg, hterminal, hagrees, hvalue⟩ :=
      supported.public_store_graph_choice_at_producer_of_timeout hguards hunique
        nullValue window state hinvariant hsettlement hcomplete producer who guard hcommit
        node htimeout (Or.inr hsem)
    exact ⟨cfg, hterminal, hagrees, producer, guard, hcommit, hvalue⟩

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.public_store_graph_of_complete'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.public_store_graph_of_complete

/-- info: 'Vegas.EventGraph.SealedFragment.public_store_graph_choice_at_producer_of_timeout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.public_store_graph_choice_at_producer_of_timeout

/-- info: 'Vegas.EventGraph.SealedFragment.public_store_graph_choice_of_timeout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.public_store_graph_choice_of_timeout
