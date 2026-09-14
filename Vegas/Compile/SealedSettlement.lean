/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPublicOutcome
import Vegas.Compile.SourceChoice
import Interaction.SealedResolutionSettlement

/-! # Source interpretation of graph timeout settlement

The graph backend supplies a legal terminal realization recording the owner's
default. Source compilation supplies disclosure uniqueness and translates that
witness to a written-source choice and payout. No native execution proof occurs
in this adapter, and no unchanged-opponents law is inferred from a settlement witness.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty}

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
  obtain ⟨cfg, hterminal, hagrees, producer, guard, hcommit, hvalue⟩ :=
    compilation.supported.public_store_graph_choice_of_timeout
      (compile_guardLive source.core source.legal) source.compiled_uniqueReveals
      nullValue window state hinvariant hsettlement hcomplete node who htimeout howned
  refine ⟨cfg, hterminal, ?_, ?_⟩
  · exact source.source_chooses_of_commit_store cfg hterminal producer who guard hcommit
      nullValue hvalue
  · rw [compilation.publicPayout?_eq_graph_of_public_store state.events cfg.1.store hagrees]
    exact evalPayoffs?_eq_decodedSourceOutcome source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      cfg hterminal

end Vegas.SealedCompilation
