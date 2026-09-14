/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedSourceExtraction
import Vegas.Compile.SourceCorrespondence

/-! # Source execution with a disclosure-based replacement

Any legal function of earlier disclosed choices supplies a unilateral source
replacement. The canonical graph execution has exactly that source law, and
each supported realization uses the replacement at its actual declared inputs.
These facts do not depend on which native host supplied the choice function.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty}
variable (compilation : SealedCompilation source ty) (focal : Player)
variable (choose : (decision : Fin (compile source.core).graph.nodeCount) →
  (compilation.supported.priorHonestCoordinates focal decision → L.Val ty) → L.Val ty)
variable (profile : SourceBehavioralProfile source.core.prog)

/-- Canonical source-graph execution with exactly one replacement. Every
opponent retains its original source policy, including private-input dependence. -/
def sourceRunOfDisclosures : FinDist (ReachableConfig (compile source.core).graph) :=
  compilation.supported.runOfDisclosures (compile_publicPrefixReadable source.core)
    (compile_guardLive source.core source.legal) focal choose
    (fun who => compileSourcePolicy source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      rfl who (profile who))

theorem sourceRunOfDisclosures_source :
    (compilation.sourceRunOfDisclosures focal choose profile).map
        (observeSourceOutcome source.core) =
      (denoteSource source.core.prog
        (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
          (compilation.sourcePolicyOfDisclosures focal choose)) source.core.env).map some :=
  runPolicyNodes_source_deviation source.core source.legal profile focal _

theorem sourceRunOfDisclosures_terminal (cfg : ReachableConfig (compile source.core).graph)
    (hcfg : cfg ∈ (compilation.sourceRunOfDisclosures focal choose profile).support) :
    Terminal (compile source.core).graph cfg.1 :=
  compilation.supported.runOfDisclosures_terminal (compile_publicPrefixReadable source.core)
    (compile_guardLive source.core source.legal) focal choose _ cfg hcfg

/-- Actual complete source realizations supply exactly the earlier disclosure
values used by the replacement. No input agreement is left as a hypothesis. -/
theorem sourceRunOfDisclosures_consistent (fallback : L.Val ty)
    (cfg : ReachableConfig (compile source.core).graph)
    (hcfg : cfg ∈ (compilation.sourceRunOfDisclosures focal choose profile).support)
    (decision : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hdecision : ((compile source.core).graph.nodeRow decision).sem = .commit focal guard) :
    cfg.1.nodeValues fallback decision =
      choose decision (fun coordinate => cfg.1.nodeValues fallback coordinate.val) :=
  compilation.supported.runOfDisclosures_consistent (compile_publicPrefixReadable source.core)
    (compile_guardLive source.core source.legal) focal choose _ fallback cfg hcfg
    decision guard hdecision

end Vegas.SealedCompilation
