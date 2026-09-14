/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateGraphCoupling
import Interaction.MessageApplicationPredraw

/-! # Arbitrary randomized candidate deviations against graph opponents

Joint predrawing of the focal player and the environment retains the complete
native trace law. The resulting coupling has a finite mixture of unilateral
graph deviations as its graph marginal, against unchanged graph opponents.
Each sampled response still uses its own history and observation. Correlation
in the response-pair mixture does not make the environment a strategic player.
Timeout utility comparisons are not consequences of these marginal laws.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (supported : SealedFragment G ty) (hinfo : G.PublicPrefixReadable) (hguards : GuardLive G)
variable (nullValue : L.Val ty) (window : Nat) (focal : Player)
variable (environment :
  (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentPolicy)
variable (schedule : List (@Invocation Player)) (fallback : L.Val ty)

/-- An arbitrary randomized focal replacement and randomized environment have
a finite mixture of the constructed deterministic-response graph/native
couplings. It retains the exact joint stopped-prefix and full-native-trace law, and
its graph marginal is a mixture of legal graph deviations. Honest
policies and their dependent draws remain unchanged. Every normally completed
supported pair agrees with the retained graph realization on public fields.

The two pure responses are drawn jointly: the mixture need not factor into
independent focal and environment mixtures. Completion and the utility
comparison after informed quitting are separate strategic obligations. -/
theorem exists_randomized_candidate_graph_coupling
    (profile : CommitPolicyProfile G)
    (replacement :
      (supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy) :
    let runtime := supported.resolvingRuntime nullValue window
    let players := fun who =>
      runtime.candidatePlayerPolicy (supported.resolvingPolicy nullValue window who (profile who))
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
        (supported.candidateGraphCoupling hinfo hguards nullValue window focal responses.1
          responses.2 schedule fallback profile).map (fun pair =>
            ((supported.candidateReplay nullValue window (pair.1.1.nodeValues fallback)
              focal responses.1 responses.2 schedule).prefixThrough stop, pair.2))) =
          native.map (fun trace => (trace.prefixThrough stop, trace)) ∧
      ((responsePairs.bind fun responses =>
        supported.candidateGraphCoupling hinfo hguards nullValue window focal responses.1
          responses.2 schedule fallback profile).map Prod.fst) =
        responsePairs.bind (fun responses =>
          supported.candidateGraphRun hinfo hguards nullValue window focal responses.1
            responses.2 schedule fallback profile) ∧
      ((responsePairs.bind fun responses =>
        supported.candidateGraphCoupling hinfo hguards nullValue window focal responses.1
          responses.2 schedule fallback profile).map Prod.snd) =
        runtime.candidateApplication.tracePolicies
          (Profile.update (sig := policySignature Player runtime.candidateApplication)
            players focal replacement) environment schedule initial ∧
      ∀ cfg trace, (cfg, trace) ∈ (responsePairs.bind fun responses =>
        supported.candidateGraphCoupling hinfo hguards nullValue window focal responses.1
          responses.2 schedule fallback profile).support →
        runtime.complete trace.last.native.application.visible = true →
        trace.last.native.application.visible.timeouts = [] →
        ∀ ref : FieldRef L, G.fieldRefPublic ref →
          Store.getAs (G.publicSealedStore ty trace.last.native.application.visible.events)
            ref.field ref.ty = Store.getAs cfg.1.store ref.field ref.ty := by
  intro runtime players initial native stop PlayerResponse EnvironmentResponse
  obtain ⟨responsePairs, responsePairs_trace⟩ :=
    runtime.candidateApplication.exists_joint_response_mixture_tracePolicies players environment
      focal schedule initial replacement
  refine ⟨responsePairs, ?_, ?_, ?_, ?_⟩
  · have h := congrArg (fun law => law.map
      (fun trace : runtime.candidateApplication.PolicyTrace =>
        (trace.prefixThrough stop, trace))) responsePairs_trace
    rw [FinDist.map_bind] at h
    refine Eq.trans ?_ h
    apply FinDist.bind_congr
    intro responses _
    exact supported.candidateGraphCoupling_prefix_native hinfo hguards nullValue window focal
      responses.1 responses.2 schedule fallback _
  · rw [FinDist.map_bind]
    apply FinDist.bind_congr
    intro responses _
    exact supported.candidateGraphCoupling_graph hinfo hguards nullValue window focal responses.1
      responses.2 schedule fallback profile
  · rw [FinDist.map_bind]
    refine Eq.trans ?_ responsePairs_trace
    apply FinDist.bind_congr
    intro responses _
    exact supported.candidateGraphCoupling_native hinfo hguards nullValue window focal
      responses.1 responses.2 schedule fallback _
  · intro cfg trace hpair hcomplete hclear
    simp only [FinDist.support_bind, Set.mem_iUnion] at hpair
    obtain ⟨responses, _, hpair⟩ := hpair
    exact supported.candidateGraphCoupling_public_store hinfo hguards nullValue window focal
      responses.1 responses.2 schedule fallback profile cfg trace hpair hcomplete hclear

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.exists_randomized_candidate_graph_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.exists_randomized_candidate_graph_coupling
