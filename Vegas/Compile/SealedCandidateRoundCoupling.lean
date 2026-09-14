/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateGraphRounds
import Vegas.Compile.SealedCandidateContinuation

/-! # Source composition of the candidate stopped-round coupling

The backend supplies the graph/native joint law. Source/graph correspondence
transports its graph marginal to a finite mixture of written-source deviations;
the compiler's public payoff-read certificate transports normal settlement.
No source execution or probability induction occurs in this adapter.

Timeouts remain in the actual native marginal. The public payout equality is
restricted to normal completion, not asserted for selectively chosen defaults.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Finite Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- An arbitrary native replacement and adaptive wire policy admit a coupling
of the actual stopped-round result with a finite mixture of legal unilateral
source deviations. Normally completed pairs have equal public payouts. The
finite budget ensures native completion, possibly by timeout; no fairness or
quitting-utility condition is assumed by this probability theorem. -/
theorem exists_randomized_candidate_round_source_coupling
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots count : Nat) (focal : Player)
    (fallback : L.Val ty) (profile : SourceBehavioralProfile source.core.prog)
    (replacement :
      (compilation.supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy)
    (wire :
      (compilation.supported.resolvingRuntime nullValue window).candidateApplication.WirePolicy) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    ∃ deviations : FinDist (SourceBehavioralPolicy source.core.prog focal),
    ∃ coupling : FinDist (Option (VEnv L (sourceTerminalCtx source.core.prog)) ×
        runtime.candidateApplication.PolicyExecution),
      coupling.map Prod.fst = deviations.bind (fun policy =>
        (denoteSource source.core.prog
          (Profile.update (sig := sourceGameSignature source.core.prog) profile focal policy)
          source.core.env).map some) ∧
      coupling.map Prod.snd = runtime.candidateRoundDriver.runRounds principals serviceSlots
        (Profile.update (sig := policySignature Player runtime.candidateApplication)
          (fun who => compilation.compileCandidatePolicy nullValue window who (profile who))
          focal replacement) wire count
        (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial)) ∧
      ∀ outcome next, (outcome, next) ∈ coupling.support →
        (∃ final, outcome = some final) ∧
        ((compile source.core).graph.nodeCount * (window + 1) ≤ count →
          runtime.complete next.native.application.visible = true) ∧
        (runtime.complete next.native.application.visible = true →
          next.native.application.visible.timeouts = [] →
          compilation.publicPayout? next.native.application.visible.events =
            outcome.map (evalPayoffs (sourceTerminalPayoffs source.core.prog))) := by
  classical
  let := Fintype.ofFinite Player
  intro runtime
  let graphProfile := fun who => compileSourcePolicy source.core.prog source.core.fresh
    (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
    rfl who (profile who)
  obtain ⟨responses, hgraph, hnative, hpairs⟩ :=
    compilation.supported.exists_randomized_candidate_round_graph_coupling
      (compile_publicPrefixReadable source.core) (compile_guardLive source.core source.legal)
      nullValue window principals serviceSlots count focal fallback graphProfile replacement wire
  let graphCoupling := responses.bind fun response =>
    compilation.supported.candidateGraphRoundCoupling
      (compile_publicPrefixReadable source.core) (compile_guardLive source.core source.legal)
      nullValue window principals serviceSlots count focal response.1 response.2 fallback
      graphProfile
  let coupling := graphCoupling.map fun pair => (observeSourceOutcome source.core pair.1, pair.2)
  let deviations : FinDist (SourceBehavioralPolicy source.core.prog focal) :=
    responses.map fun response =>
      compilation.extractedCandidateSourcePolicy nullValue window focal response.1 response.2
        (roundSchedule principals serviceSlots count) fallback
  refine ⟨deviations, coupling, ?_, ?_, ?_⟩
  · have hsource := congrArg (fun law => law.map (observeSourceOutcome source.core)) hgraph
    simp only [FinDist.map_comp, FinDist.map_bind, Function.comp_def] at hsource
    simp only [coupling, graphCoupling, FinDist.map_comp, FinDist.map_bind, Function.comp_def]
    refine hsource.trans ?_
    dsimp only [deviations]
    refine Eq.trans ?_ (FinDist.bind_map _ _ _).symm
    apply FinDist.bind_congr
    intro response _
    exact compilation.extractedCandidateSourceRun_source nullValue window focal response.1
      response.2 (roundSchedule principals serviceSlots count) fallback profile
  · simpa only [coupling, graphCoupling, graphProfile, runtime, compileCandidatePolicy,
      compileResolvingPolicy, FinDist.map_comp, Function.comp_def] using hnative
  · intro outcome next hpair
    simp only [coupling, FinDist.support_map, Set.mem_image] at hpair
    obtain ⟨⟨cfg, actual⟩, hpair, heq⟩ := hpair
    have houtcome : observeSourceOutcome source.core cfg = outcome := congrArg Prod.fst heq
    have hnext : actual = next := congrArg Prod.snd heq
    subst actual outcome
    obtain ⟨hterminal, hcomplete, hpublic⟩ := hpairs cfg next hpair
    refine ⟨⟨_, observeSourceOutcome_of_terminal source.core cfg hterminal⟩, hcomplete, ?_⟩
    intro hdone hclear
    rw [compilation.publicPayout?_eq_graph_of_public_store _ _ (hpublic hdone hclear),
      observeSourceOutcome_of_terminal source.core cfg hterminal]
    exact evalPayoffs?_eq_decodedSourceOutcome source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      cfg hterminal

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.exists_randomized_candidate_round_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.exists_randomized_candidate_round_source_coupling
