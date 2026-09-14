/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateSourceExtraction
import Vegas.Compile.SealedCandidateGraphCoupling
import Vegas.Compile.SealedPublicOutcome

/-! # Source composition of candidate graph/native coupling

The source adapter applies graph/native coupling to compiled source policies.
Its source marginal follows from source/graph correspondence; normal payout
agreement follows from the backend's public-field law and the compiler's
public payoff-read certificate. Runtime continuation proofs stay graph-relative.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (compilation : SealedCompilation source ty)
variable (nullValue : L.Val ty) (window : Nat) (focal : Player)
variable (deviator :
  List (compilation.supported.resolvingRuntime nullValue window).candidateApplication.PlayerEntry →
  (compilation.supported.resolvingRuntime nullValue window).candidateApplication.View →
  (compilation.supported.resolvingRuntime nullValue window).candidateApplication.PlayerCommand)
variable (environment :
  List
    (compilation.supported.resolvingRuntime nullValue
      window).candidateApplication.EnvironmentEntry →
  EnvironmentObservation
    (compilation.supported.resolvingRuntime nullValue window).candidateApplication →
  (compilation.supported.resolvingRuntime nullValue
    window).candidateApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player)) (fallback : L.Val ty)

/-- Retain a complete source realization, replay its native prefix through
first timeout, and run the actual native continuation. The invocation suffix
is determined by the retained prefix length, including waits and rejected
commands; private and environment histories are retained in its last state. -/
def extractedCandidateSourceCoupling (profile : SourceBehavioralProfile source.core.prog) :
    FinDist (ReachableConfig (compile source.core).graph ×
      (compilation.supported.resolvingRuntime nullValue
        window).candidateApplication.PolicyTrace) :=
  compilation.supported.candidateGraphCoupling
    (compile_publicPrefixReadable source.core) (compile_guardLive source.core source.legal)
    nullValue window focal deviator environment schedule fallback
    (fun who => compileSourcePolicy source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      rfl who (profile who))

/-- The source marginal is its written-order denotation against unchanged
opponents, with the same extracted policy throughout the source execution. -/
theorem extractedCandidateSourceCoupling_source
    (profile : SourceBehavioralProfile source.core.prog) :
    (compilation.extractedCandidateSourceCoupling nullValue window focal deviator environment
      schedule fallback profile).map (fun pair => observeSourceOutcome source.core pair.1) =
      (denoteSource source.core.prog
        (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
          (compilation.extractedCandidateSourcePolicy nullValue window focal deviator
            environment schedule fallback)) source.core.env).map some := by
  change ((compilation.extractedCandidateSourceCoupling nullValue window focal deviator
    environment schedule fallback profile).map ((observeSourceOutcome source.core) ∘ Prod.fst)) = _
  rw [← FinDist.map_comp]
  change ((compilation.supported.candidateGraphCoupling
    (compile_publicPrefixReadable source.core) (compile_guardLive source.core source.legal)
    _ _ _ _ _ _ _ _).map Prod.fst).map _ = _
  rw [compilation.supported.candidateGraphCoupling_graph]
  exact compilation.extractedCandidateSourceRun_source nullValue window focal deviator
    environment schedule fallback profile

/-- Normal completion pays exactly the retained source realization's graph
payout, reconstructed solely from public fields and opening events. -/
theorem extractedCandidateSourceCoupling_payout_of_complete_clear
    (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (trace :
      (compilation.supported.resolvingRuntime nullValue window).candidateApplication.PolicyTrace)
    (hpair : (cfg, trace) ∈ (compilation.extractedCandidateSourceCoupling nullValue window focal
      deviator environment schedule fallback profile).support)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      trace.last.native.application.visible = true)
    (hclear : trace.last.native.application.visible.timeouts = []) :
    compilation.publicPayout? trace.last.native.application.visible.events =
      evalPayoffs? (compile source.core).payoffs cfg.1.store :=
  compilation.publicPayout?_eq_graph_of_public_store _ _
    (compilation.supported.candidateGraphCoupling_public_store
      (compile_publicPrefixReadable source.core) (compile_guardLive source.core source.legal)
      nullValue window focal deviator environment schedule fallback _ cfg trace hpair
      hcomplete hclear)


end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.extractedCandidateSourceCoupling_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedCandidateSourceCoupling_source

/-- info: 'Vegas.SealedCompilation.extractedCandidateSourceCoupling_payout_of_complete_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedCandidateSourceCoupling_payout_of_complete_clear
