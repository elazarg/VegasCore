/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedContinuation
import Interaction.MessageApplicationPredraw

/-! # Randomized pending-message deviation coupling

Predrawing the focal policy preserves its complete native trace law. Applying
the source/native coupling to each fixed response therefore preserves the
joint law of the stopped prefix and final execution. The retained source
marginal is a finite mixture of ordinary source deviations against unchanged
opponents. The environment is still a fixed observation-local response
function; its commands may depend on pending messages and its own history.

The mixture may depend on the original opponent profile. These laws do not
identify post-timeout outcomes or supply the informed-quitting utility bound.
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
  List
    (compilation.supported.resolvingRuntime nullValue window).messageApplication.EnvironmentEntry →
  EnvironmentObservation
    (compilation.supported.resolvingRuntime nullValue window).messageApplication →
  (compilation.supported.resolvingRuntime nullValue
    window).messageApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player)) (fallback : L.Val ty)

/-- An arbitrary randomized native replacement has a finite mixture of the
constructed source/native couplings. It retains the exact joint stopped-prefix
and final-native law, and its source marginal is a mixture of legal written-source
deviations. Honest policies and their dependent draws remain unchanged.

Completion and the utility comparison after informed quitting are separate
strategic obligations. Normal completed runs have pointwise source agreement
by `SealedCompilation.mixtureSourceCoupling_decode_of_complete_clear`. -/
theorem exists_randomized_source_coupling
    (profile : SourceBehavioralProfile source.core.prog)
    (replacement :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := fun who =>
      compilation.compileResolvingPolicy nullValue window who (profile who)
    let env := fun history view => FinDist.pure (environment history view)
    let initial := PolicyExecution.initial runtime.messageApplication
      (State.initial _ runtime.initial)
    let native := runtime.messageApplication.tracePolicies
      (Profile.update (sig := policySignature Player runtime.messageApplication)
        players focal replacement) env schedule initial
    let stop := fun execution : runtime.messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    ∃ responses : FinDist (List runtime.messageApplication.PlayerEntry →
        runtime.messageApplication.View → runtime.messageApplication.PlayerCommand),
      (responses.bind fun response =>
        (compilation.extractedSourceCoupling nullValue window focal response environment schedule
          fallback profile).map (fun pair =>
            ((compilation.supported.resolvingReplay nullValue window (pair.1.1.nodeValues fallback)
              focal response environment schedule).prefixThrough stop, pair.2))) =
          native.map (fun trace => (trace.prefixThrough stop, trace.last)) ∧
      ((responses.bind fun response => compilation.extractedSourceCoupling nullValue window focal
        response environment schedule fallback profile).map
          (fun pair => observeSourceOutcome source.core pair.1)) =
        responses.bind (fun response =>
          (denoteSource source.core.prog
            (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
              (compilation.extractedSourcePolicy nullValue window focal response environment
                schedule fallback)) source.core.env).map some) ∧
      ((responses.bind fun response => compilation.extractedSourceCoupling nullValue window focal
        response environment schedule fallback profile).map Prod.snd) =
        runtime.messageApplication.runPolicies
          (Profile.update (sig := policySignature Player runtime.messageApplication)
            players focal replacement) env schedule initial := by
  intro runtime players env initial native stop
  obtain ⟨responses, hresponses⟩ :=
    runtime.messageApplication.exists_native_response_mixture_tracePolicies players env focal
      schedule initial replacement
  refine ⟨responses, ?_, ?_, ?_⟩
  · have h := congrArg (fun law => law.map
      (fun trace : runtime.messageApplication.PolicyTrace =>
        (trace.prefixThrough stop, trace.last))) hresponses
    rw [FinDist.map_bind] at h
    refine Eq.trans ?_ h
    apply FinDist.bind_congr
    intro response _
    exact compilation.extractedSourceCoupling_prefix_native nullValue window focal response
      environment schedule fallback profile
  · rw [FinDist.map_bind]
    apply FinDist.bind_congr
    intro response _
    exact compilation.extractedSourceCoupling_source nullValue window focal response environment
      schedule fallback profile
  · have h := congrArg (fun law => law.map PolicyTrace.last) hresponses
    rw [FinDist.map_bind, runtime.messageApplication.tracePolicies_last] at h
    rw [FinDist.map_bind]
    refine Eq.trans ?_ h
    apply FinDist.bind_congr
    intro response _
    rw [runtime.messageApplication.tracePolicies_last]
    exact compilation.extractedSourceCoupling_native nullValue window focal response environment
      schedule fallback profile

/-- Every supported normally completed pair in a mixture of the constructed
couplings has exactly the retained source configuration as its native decoding.
This applies in particular to the mixture for an arbitrary randomized deviation;
the observation being compared is independent of its sampled response function. -/
theorem mixtureSourceCoupling_decode_of_complete_clear
    (profile : SourceBehavioralProfile source.core.prog)
    (responses : FinDist
      (List
        (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry →
        (compilation.supported.resolvingRuntime nullValue window).messageApplication.View →
        (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerCommand))
    (cfg : ReachableConfig (compile source.core).graph)
    (final :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hpair : (cfg, final) ∈ (responses.bind fun response =>
      compilation.extractedSourceCoupling nullValue window focal response environment schedule
        fallback profile).support)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      final.native.application.visible = true)
    (hclear : final.native.application.visible.timeouts = []) :
    (compile source.core).graph.decodeSealedFrom ty final.native.application.service
      (Config.initial _) final.native.application.visible.events = some cfg.1 := by
  simp only [FinDist.support_bind, Set.mem_iUnion] at hpair
  obtain ⟨response, _, hpair⟩ := hpair
  exact compilation.extractedSourceCoupling_decode_of_complete_clear nullValue window focal
    response environment schedule fallback profile cfg final hpair hcomplete hclear

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.exists_randomized_source_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.exists_randomized_source_coupling

/-- info: 'Vegas.SealedCompilation.mixtureSourceCoupling_decode_of_complete_clear' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.mixtureSourceCoupling_decode_of_complete_clear
