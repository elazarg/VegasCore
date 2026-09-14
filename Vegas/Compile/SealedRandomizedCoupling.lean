/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedContinuation
import Interaction.MessageApplicationPredraw

/-! # Randomized pending-message deviation coupling

Predrawing the focal policy and the environment preserves their complete native
trace law. Applying the source/native coupling to each fixed pair of responses
therefore preserves the joint law of the stopped prefix and complete trace.
The retained source marginal is a finite mixture of ordinary source deviations
against unchanged opponents.

The pure focal and environment responses in the mixture may be correlated. The
environment remains a distinct participant and its response is still local to
its own history and observation. These laws do not identify post-timeout
outcomes or supply the informed-quitting utility bound.
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
  (compilation.supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicy)
variable (schedule : List (@Invocation Player)) (fallback : L.Val ty)

/-- An arbitrary randomized focal replacement and randomized environment have
a finite mixture of the constructed deterministic-response source/native
couplings. It retains the exact joint stopped-prefix and full-native-trace law, and
its source marginal is a mixture of legal written-source deviations. Honest
policies and their dependent draws remain unchanged.

The two pure responses are drawn jointly: the mixture need not factor into
independent focal and environment mixtures. Completion and the utility
comparison after informed quitting are separate strategic obligations. Normal
completed runs have pointwise source agreement by
`SealedCompilation.mixtureSourceCoupling_decode_of_complete_clear`. -/
theorem exists_randomized_source_coupling
    (profile : SourceBehavioralProfile source.core.prog)
    (replacement :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := fun who =>
      compilation.compileResolvingPolicy nullValue window who (profile who)
    let initial := PolicyExecution.initial runtime.messageApplication
      (State.initial _ runtime.initial)
    let native := runtime.messageApplication.tracePolicies
      (Profile.update (sig := policySignature Player runtime.messageApplication)
        players focal replacement) environment schedule initial
    let stop := fun execution : runtime.messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let PlayerResponse := List runtime.messageApplication.PlayerEntry →
      runtime.messageApplication.View → runtime.messageApplication.PlayerCommand
    let EnvironmentResponse := List runtime.messageApplication.EnvironmentEntry →
      runtime.messageApplication.EnvironmentObservation →
        runtime.messageApplication.EnvironmentPolicyCommand
    ∃ responsePairs : FinDist (PlayerResponse × EnvironmentResponse),
      (responsePairs.bind fun responses =>
        (compilation.extractedSourceCoupling nullValue window focal responses.1 responses.2
          schedule fallback profile).map (fun pair =>
            ((compilation.supported.resolvingReplay nullValue window (pair.1.1.nodeValues fallback)
              focal responses.1 responses.2 schedule).prefixThrough stop, pair.2))) =
          native.map (fun trace => (trace.prefixThrough stop, trace)) ∧
      ((responsePairs.bind fun responses =>
        compilation.extractedSourceCoupling nullValue window focal responses.1 responses.2
          schedule fallback profile).map (fun pair => observeSourceOutcome source.core pair.1)) =
        responsePairs.bind (fun responses =>
          (denoteSource source.core.prog
            (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
              (compilation.extractedSourcePolicy nullValue window focal responses.1 responses.2
                schedule fallback)) source.core.env).map some) ∧
      ((responsePairs.bind fun responses =>
        compilation.extractedSourceCoupling nullValue window focal responses.1 responses.2
          schedule fallback profile).map Prod.snd) =
        runtime.messageApplication.tracePolicies
          (Profile.update (sig := policySignature Player runtime.messageApplication)
            players focal replacement) environment schedule initial := by
  intro runtime players initial native stop PlayerResponse EnvironmentResponse
  obtain ⟨responsePairs, responsePairs_trace⟩ :=
    runtime.messageApplication.exists_joint_response_mixture_tracePolicies players environment
      focal schedule initial replacement
  refine ⟨responsePairs, ?_, ?_, ?_⟩
  · have h := congrArg (fun law => law.map
      (fun trace : runtime.messageApplication.PolicyTrace =>
        (trace.prefixThrough stop, trace))) responsePairs_trace
    rw [FinDist.map_bind] at h
    refine Eq.trans ?_ h
    apply FinDist.bind_congr
    intro responses _
    exact compilation.extractedSourceCoupling_prefix_native nullValue window focal responses.1
      responses.2 schedule fallback profile
  · rw [FinDist.map_bind]
    apply FinDist.bind_congr
    intro responses _
    exact compilation.extractedSourceCoupling_source nullValue window focal responses.1 responses.2
      schedule fallback profile
  · rw [FinDist.map_bind]
    refine Eq.trans ?_ responsePairs_trace
    apply FinDist.bind_congr
    intro responses _
    exact compilation.extractedSourceCoupling_native nullValue window focal responses.1 responses.2
      schedule fallback profile

/-- Every supported normally completed pair in a mixture of the constructed
couplings has exactly the retained source configuration as its native decoding.
This applies in particular to the mixture for an arbitrary randomized focal
policy and environment; the observation being compared is independent of the
sampled response pair. -/
theorem mixtureSourceCoupling_decode_of_complete_clear
    (profile : SourceBehavioralProfile source.core.prog)
    (responsePairs : FinDist
      ((List
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.PlayerEntry →
          (compilation.supported.resolvingRuntime nullValue window).messageApplication.View →
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.PlayerCommand) ×
        (List
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.EnvironmentEntry →
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.EnvironmentObservation →
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.EnvironmentPolicyCommand)))
    (cfg : ReachableConfig (compile source.core).graph)
    (trace :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyTrace)
    (hpair : (cfg, trace) ∈ (responsePairs.bind fun responses =>
      compilation.extractedSourceCoupling nullValue window focal responses.1 responses.2 schedule
        fallback profile).support)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      trace.last.native.application.visible = true)
    (hclear : trace.last.native.application.visible.timeouts = []) :
    (compile source.core).graph.decodeSealedFrom ty trace.last.native.application.service
      (Config.initial _) trace.last.native.application.visible.events = some cfg.1 := by
  simp only [FinDist.support_bind, Set.mem_iUnion] at hpair
  obtain ⟨responses, _, hpair⟩ := hpair
  exact compilation.extractedSourceCoupling_decode_of_complete_clear nullValue window focal
    responses.1 responses.2 schedule fallback profile cfg trace hpair hcomplete hclear

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.exists_randomized_source_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.exists_randomized_source_coupling

/-- info: 'Vegas.SealedCompilation.mixtureSourceCoupling_decode_of_complete_clear' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.mixtureSourceCoupling_decode_of_complete_clear
