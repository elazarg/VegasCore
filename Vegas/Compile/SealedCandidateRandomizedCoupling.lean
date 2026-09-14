/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateContinuation
import Vegas.Compile.SealedCandidateGraphRandomized

/-! # Randomized pending-message deviation coupling

The graph/backend theorem supplies the joint native trace law and graph
deviation mixture. Source/graph correspondence transports its graph marginal
to ordinary written-source deviations against unchanged opponents. The
compiler's public payoff-read certificate transports normal payout agreement.

The pure focal and environment responses in the mixture may be correlated.
Each response still uses its own declared history and observation; predrawing
does not make the environment a game player. These laws do not identify
post-timeout outcomes or supply the informed-quitting utility bound.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (compilation : SealedCompilation source ty)
variable (nullValue : L.Val ty) (window : Nat) (focal : Player)
variable (environment :
  (compilation.supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentPolicy)
variable (schedule : List (@Invocation Player)) (fallback : L.Val ty)

/-- An arbitrary randomized focal replacement and randomized environment have
a finite mixture of the constructed deterministic-response source/native
couplings. It retains the exact joint stopped-prefix and full-native-trace law, and
its source marginal is a mixture of legal written-source deviations. Honest
policies and their dependent draws remain unchanged. Every normally completed
supported pair has the retained source realization's public payout.

The two pure responses are drawn jointly: the mixture need not factor into
independent focal and environment mixtures. Completion and the utility
comparison after informed quitting are separate strategic obligations. -/
theorem exists_randomized_candidate_source_coupling
    (profile : SourceBehavioralProfile source.core.prog)
    (replacement :
      (compilation.supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := fun who =>
      compilation.compileCandidatePolicy nullValue window who (profile who)
    let initial := PolicyExecution.initial runtime.candidateApplication
      (State.initial _ runtime.candidateInitial)
    let native := runtime.candidateApplication.tracePolicies
      (Profile.update (sig := policySignature Player runtime.candidateApplication)
        players focal replacement) environment schedule initial
    let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let PlayerResponse := List runtime.candidateApplication.PlayerEntry →
      runtime.candidateApplication.View → runtime.candidateApplication.PlayerCommand
    let EnvironmentResponse := List runtime.candidateApplication.EnvironmentEntry →
      runtime.candidateApplication.EnvironmentObservation →
        runtime.candidateApplication.EnvironmentPolicyCommand
    ∃ responsePairs : FinDist (PlayerResponse × EnvironmentResponse),
      (responsePairs.bind fun responses =>
        (compilation.extractedCandidateSourceCoupling nullValue window focal responses.1
          responses.2 schedule fallback profile).map (fun pair =>
            ((compilation.supported.candidateReplay nullValue window (pair.1.1.nodeValues fallback)
              focal responses.1 responses.2 schedule).prefixThrough stop, pair.2))) =
          native.map (fun trace => (trace.prefixThrough stop, trace)) ∧
      ((responsePairs.bind fun responses =>
        compilation.extractedCandidateSourceCoupling nullValue window focal responses.1
          responses.2 schedule fallback profile).map (fun pair => observeSourceOutcome
            source.core pair.1)) =
        responsePairs.bind (fun responses =>
          (denoteSource source.core.prog
            (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
              (compilation.extractedCandidateSourcePolicy nullValue window focal responses.1
                responses.2 schedule fallback)) source.core.env).map some) ∧
      ((responsePairs.bind fun responses =>
        compilation.extractedCandidateSourceCoupling nullValue window focal responses.1
          responses.2 schedule fallback profile).map Prod.snd) =
        runtime.candidateApplication.tracePolicies
          (Profile.update (sig := policySignature Player runtime.candidateApplication)
            players focal replacement) environment schedule initial ∧
      ∀ cfg trace, (cfg, trace) ∈ (responsePairs.bind fun responses =>
        compilation.extractedCandidateSourceCoupling nullValue window focal responses.1
          responses.2 schedule fallback profile).support →
        runtime.complete trace.last.native.application.visible = true →
        trace.last.native.application.visible.timeouts = [] →
        compilation.publicPayout? trace.last.native.application.visible.events =
          evalPayoffs? (compile source.core).payoffs cfg.1.store := by
  intro runtime players initial native stop PlayerResponse EnvironmentResponse
  obtain ⟨responsePairs, hjoint, hgraph, hnative, hpublic⟩ :=
    compilation.supported.exists_randomized_candidate_graph_coupling
      (compile_publicPrefixReadable source.core) (compile_guardLive source.core source.legal)
      nullValue window focal environment schedule fallback
      (fun who => compileSourcePolicy source.core.prog source.core.fresh
        (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
        rfl who (profile who)) replacement
  refine ⟨responsePairs, hjoint, ?_, hnative, ?_⟩
  · have hsource := congrArg (fun law => law.map (observeSourceOutcome source.core)) hgraph
    simp only [FinDist.map_comp, FinDist.map_bind, Function.comp_def] at hsource
    rw [FinDist.map_bind]
    refine hsource.trans ?_
    apply FinDist.bind_congr
    intro responses _
    exact compilation.extractedCandidateSourceRun_source nullValue window focal responses.1
      responses.2 schedule fallback profile
  · intro cfg trace hpair hcomplete hclear
    exact compilation.publicPayout?_eq_graph_of_public_store _ _
      (hpublic cfg trace hpair hcomplete hclear)

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.exists_randomized_candidate_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.exists_randomized_candidate_source_coupling
