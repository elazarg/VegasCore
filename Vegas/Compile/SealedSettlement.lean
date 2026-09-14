/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPublicOutcome
import Vegas.Compile.SourceChoice
import Interaction.SealedResolutionSettlement

/-! # Source choices explaining public timeout settlement

Public payout after a player's timeout has a legal source realization in which
that player chose the configured default. The witness preserves public results;
it need not preserve private registrations or the opponents' policy law.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty}

private theorem public_reveal_eq_default
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.PublicState Player (L.Val ty))
    (hinvariant : SealedResolution.PublicEventInvariant
      (compilation.supported.resolvingRuntime nullValue window) state)
    (hsettlement : SealedResolution.SettlementInvariant
      (compilation.supported.resolvingRuntime nullValue window) state)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      state = true)
    (node producer : Fin (compile source.core).graph.nodeCount)
    (who : Player) (guard : EventGuard L)
    (hsem : ((compile source.core).graph.nodeRow node).sem =
      .reveal ((compile source.core).graph.nodeTarget producer))
    (hcommit : ((compile source.core).graph.nodeRow producer).sem = .commit who guard)
    (htimeout : node.val ∈ state.timeouts ∨ producer.val ∈ state.timeouts) :
    Store.getAs ((compile source.core).graph.publicSealedStore ty state.events)
      ((compile source.core).graph.nodeTarget node) ty = some nullValue := by
  let graph := (compile source.core).graph
  have hrule : compilation.supported.compile.rules[node.val]? =
      some ⟨.reveal who producer.val, graph.messagePrerequisites node⟩ := by
    rw [compilation.supported.compile_rule]
    exact congrArg some (graph.sealedRule_reveal_eq node producer who guard hsem hcommit)
  have hcompleted : state.completed node.val = true := by
    apply List.all_eq_true.mp hcomplete node.val
    have hlen : compilation.supported.compile.rules.length = graph.nodeCount := by
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

/-- A timed-out commitment or reveal owned by `who` has the programmed payout
of a reachable source realization in which `who` chose the default. Both the
choice and the payout refer to the same independently decoded source outcome.
No timely-service hypothesis or policy restriction is used here. -/
theorem publicPayout_source_choice_of_timeout [Finite Player]
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.PublicState Player (L.Val ty))
    (hinvariant : SealedResolution.PublicEventInvariant
      (compilation.supported.resolvingRuntime nullValue window) state)
    (hsettlement : SealedResolution.SettlementInvariant
      (compilation.supported.resolvingRuntime nullValue window) state)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      state = true)
    (node : Fin (compile source.core).graph.nodeCount) (who : Player)
    (htimeout : node.val ∈ state.timeouts)
    (howned : (∃ guard, ((compile source.core).graph.nodeRow node).sem = .commit who guard) ∨
      ∃ (producer : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L),
        ((compile source.core).graph.nodeRow node).sem =
          .reveal ((compile source.core).graph.nodeTarget producer) ∧
        ((compile source.core).graph.nodeRow producer).sem = .commit who guard) :
    ∃ cfg : ReachableConfig (compile source.core).graph,
      ∃ hterminal : Terminal (compile source.core).graph cfg.1,
        source.core.prog.Chooses who nullValue
          (decodeSourceOutcome source.core.prog source.core.fresh
            (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
            cfg hterminal) ∧
        compilation.publicPayout? state.events =
          some (evalPayoffs (sourceTerminalPayoffs source.core.prog)
            (decodeSourceOutcome source.core.prog source.core.fresh
              (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
              cfg hterminal)) := by
  obtain ⟨cfg, hterminal, hagrees, hdefaults⟩ :=
    compilation.public_store_source_of_complete nullValue window state
      hinvariant hcomplete
  have hchoose (producer : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
      (hcommit : ((compile source.core).graph.nodeRow producer).sem = .commit who guard)
      (hdefault : ∀ reveal, ((compile source.core).graph.nodeRow reveal).sem =
          .reveal ((compile source.core).graph.nodeTarget producer) →
        Store.getAs ((compile source.core).graph.publicSealedStore ty state.events)
          ((compile source.core).graph.nodeTarget reveal) ty = some nullValue) :
      source.core.prog.Chooses who nullValue
        (decodeSourceOutcome source.core.prog source.core.fresh
          (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
          cfg hterminal) := by
    apply source.source_chooses_of_commit_store cfg hterminal producer who guard hcommit nullValue
    rw [cfg.1.store_nodeValues (reachable_storeCoherent compilation.supported.graphWF cfg.2)
      nullValue producer (compilation.supported.rowType producer) (hterminal producer),
      hdefaults producer who guard hcommit hdefault]
  refine ⟨cfg, hterminal, ?_, ?_⟩
  · rcases howned with ⟨guard, hcommit⟩ | ⟨producer, guard, hsem, hcommit⟩
    · apply hchoose node guard hcommit
      intro reveal hsem
      exact compilation.public_reveal_eq_default nullValue window state hinvariant hsettlement
        hcomplete reveal node who guard hsem hcommit (Or.inr htimeout)
    · apply hchoose producer guard hcommit
      intro reveal hreveal
      have heq := source.compiled_reveal_source_injective reveal node _ hreveal hsem
      subst reveal
      exact compilation.public_reveal_eq_default nullValue window state hinvariant hsettlement
        hcomplete node producer who guard hsem hcommit (Or.inl htimeout)
  · rw [compilation.publicPayout?_eq_graph_of_public_store state.events cfg.1.store hagrees]
    exact evalPayoffs?_eq_decodedSourceOutcome source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      cfg hterminal

end Vegas.SealedCompilation
