/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateSourceExtraction
import Vegas.Compile.SealedCandidateGraphNative

/-! # Source composition of the candidate graph/native prefix law

The source compiler supplies the graph information and legal-move certificates.
The runtime prefix law then follows by applying the independent graph theorem
to the compiled source profile. No native probability calculation occurs here.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (compilation : SealedCompilation source ty)
variable (nullValue : L.Val ty) (window : Nat) (focal : Player)
variable (deviator :
  List (compilation.supported.resolvingRuntime nullValue window).candidateApplication.PlayerEntry →
  (compilation.supported.resolvingRuntime nullValue window).candidateApplication.View →
  (compilation.supported.resolvingRuntime nullValue window).candidateApplication.PlayerCommand)
variable (environment :
  List (compilation.supported.resolvingRuntime
    nullValue window).candidateApplication.EnvironmentEntry →
  (compilation.supported.resolvingRuntime
    nullValue window).candidateApplication.EnvironmentObservation →
  (compilation.supported.resolvingRuntime
    nullValue window).candidateApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player))

/-- Exact native marginal of the written-source realization under the
extracted focal policy, through the first timeout. Opponents retain their
original, potentially dependent source kernels. Equality concerns complete
native prefixes, including private command records, pending messages, delivery,
inclusion, clock, and receipts; these proof records are not player views.

The focal and environment responses are fixed functions. This theorem neither
identifies the post-timeout continuation with a source run nor removes the
utility condition needed for informed quitting. -/
theorem extractedCandidateSourceRun_native_prefix_law [Fintype Player] (fallback : L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := Profile.update (sig := policySignature Player runtime.candidateApplication)
      (fun who => compilation.compileCandidatePolicy nullValue window who (profile who)) focal
      (fun history view => FinDist.pure (deviator history view))
    let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    (compilation.extractedCandidateSourceRun nullValue window focal deviator environment schedule
      fallback profile).map (fun cfg =>
        (compilation.supported.candidateReplay nullValue window (cfg.1.nodeValues fallback) focal
          deviator environment schedule).prefixThrough stop) =
      (runtime.candidateApplication.tracePolicies players
        (fun history view => FinDist.pure (environment history view)) schedule
        (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).map
          (PolicyTrace.prefixThrough stop) :=
  compilation.supported.candidateGraphRun_native_prefix_law
    (compile_publicPrefixReadable source.core) (compile_guardLive source.core source.legal)
    nullValue window focal deviator environment schedule fallback _

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.extractedCandidateSourceRun_native_prefix_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedCandidateSourceRun_native_prefix_law
