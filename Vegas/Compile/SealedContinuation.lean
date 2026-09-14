/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedNativeLikelihood
import Interaction.MessageApplicationContinuation

/-! # Source/native coupling with the actual timeout continuation

The source realization determines the native prefix through first timeout.
Resuming the original policies from that prefix gives the complete native law,
while retaining the ordinary source law as the other marginal. Subsequent
honest choices use their actual native inputs, which can differ from those of
the retained source realization after timeout. The marginal identities alone
assert neither terminal outcome equality nor a utility comparison.
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
  List (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry →
  (compilation.supported.resolvingRuntime nullValue window).messageApplication.View →
  (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerCommand)
variable (environment :
  List
    (compilation.supported.resolvingRuntime nullValue window).messageApplication.EnvironmentEntry →
  EnvironmentObservation
    (compilation.supported.resolvingRuntime nullValue window).messageApplication →
  (compilation.supported.resolvingRuntime nullValue
    window).messageApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player)) (fallback : L.Val ty)

/-- Retain a complete source realization, replay its native prefix through
first timeout, and run the actual native continuation. The invocation suffix
is determined by the retained prefix length, including waits and rejected
commands; private and environment histories are retained in its last state. -/
def extractedSourceCoupling (profile : SourceBehavioralProfile source.core.prog) :
    FinDist (ReachableConfig (compile source.core).graph ×
      (compilation.supported.resolvingRuntime nullValue
        window).messageApplication.PolicyExecution) :=
  let runtime := compilation.supported.resolvingRuntime nullValue window
  let players := Profile.update (sig := policySignature Player runtime.messageApplication)
    (fun who => compilation.compileResolvingPolicy nullValue window who (profile who)) focal
    (fun history view => FinDist.pure (deviator history view))
  let stop := fun execution : runtime.messageApplication.PolicyExecution =>
    !execution.native.application.visible.timeouts.isEmpty
  (compilation.extractedSourceRun nullValue window focal deviator environment schedule fallback
    profile).bind fun cfg =>
      let stopped := (compilation.supported.resolvingReplay nullValue window
        (cfg.1.nodeValues fallback) focal deviator environment schedule).prefixThrough stop
      (runtime.messageApplication.runPolicies players
        (fun history view => FinDist.pure (environment history view))
        (schedule.drop stopped.length) stopped.last).map fun final => (cfg, final)

/-- Attaching a normalized native suffix does not change the retained source
realization, even when that suffix responds to a timeout settlement. -/
theorem extractedSourceCoupling_realization (profile : SourceBehavioralProfile source.core.prog) :
    (compilation.extractedSourceCoupling nullValue window focal deviator environment schedule
      fallback profile).map Prod.fst =
      compilation.extractedSourceRun nullValue window focal deviator environment schedule
        fallback profile := by
  simp only [extractedSourceCoupling, FinDist.map_bind, FinDist.map_comp,
    Function.comp_def, FinDist.map_const, FinDist.bind_pure]

/-- The source marginal is its written-order denotation against unchanged
opponents, with the same extracted policy throughout the source execution. -/
theorem extractedSourceCoupling_source (profile : SourceBehavioralProfile source.core.prog) :
    (compilation.extractedSourceCoupling nullValue window focal deviator environment schedule
      fallback profile).map (fun pair => observeSourceOutcome source.core pair.1) =
      (denoteSource source.core.prog
        (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
          (compilation.extractedSourcePolicy nullValue window focal deviator environment schedule
            fallback)) source.core.env).map some := by
  change ((compilation.extractedSourceCoupling nullValue window focal deviator environment schedule
    fallback profile).map ((observeSourceOutcome source.core) ∘ Prod.fst)) = _
  rw [← FinDist.map_comp, compilation.extractedSourceCoupling_realization]
  exact compilation.extractedSourceRun_source nullValue window focal deviator environment schedule
    fallback profile

/-- The coupling preserves the joint law of the stopped native prefix and
the eventual execution. Thus it retains their dependence, not just the two
separate marginal laws. -/
theorem extractedSourceCoupling_prefix_native
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := Profile.update (sig := policySignature Player runtime.messageApplication)
      (fun who => compilation.compileResolvingPolicy nullValue window who (profile who)) focal
      (fun history view => FinDist.pure (deviator history view))
    let stop := fun execution : runtime.messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    (compilation.extractedSourceCoupling nullValue window focal deviator environment schedule
      fallback profile).map (fun pair =>
        ((compilation.supported.resolvingReplay nullValue window (pair.1.1.nodeValues fallback)
          focal deviator environment schedule).prefixThrough stop, pair.2)) =
      (runtime.messageApplication.tracePolicies players
        (fun history view => FinDist.pure (environment history view)) schedule
        (PolicyExecution.initial _ (State.initial _ runtime.initial))).map
          (fun trace => (trace.prefixThrough stop, trace.last)) := by
  intro runtime players stop
  have hprefix := compilation.extractedSourceRun_native_prefix_law nullValue window focal deviator
    environment schedule fallback profile
  rw [runtime.messageApplication.tracePolicies_prefix_last_law players
    (fun history view => FinDist.pure (environment history view)) stop]
  rw [← hprefix]
  simp only [extractedSourceCoupling, FinDist.map_bind, FinDist.map_comp, Function.comp_def,
    FinDist.bind_map]
  rfl

/-- The other marginal is the complete native execution, including its actual
post-timeout behavior. No settlement, fairness, or source/native utility premise
is needed for this execution-law identity. -/
theorem extractedSourceCoupling_native (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := Profile.update (sig := policySignature Player runtime.messageApplication)
      (fun who => compilation.compileResolvingPolicy nullValue window who (profile who)) focal
      (fun history view => FinDist.pure (deviator history view))
    (compilation.extractedSourceCoupling nullValue window focal deviator environment schedule
      fallback profile).map Prod.snd =
      runtime.messageApplication.runPolicies players
        (fun history view => FinDist.pure (environment history view)) schedule
        (PolicyExecution.initial _ (State.initial _ runtime.initial)) := by
  intro runtime players
  have h := congrArg (fun law => law.map Prod.snd)
    (compilation.extractedSourceCoupling_prefix_native nullValue window focal deviator environment
      schedule fallback profile)
  simp only [FinDist.map_comp, Function.comp_def] at h
  change (compilation.extractedSourceCoupling nullValue window focal deviator environment schedule
    fallback profile).map Prod.snd =
      (runtime.messageApplication.tracePolicies players
        (fun history view => FinDist.pure (environment history view)) schedule
        (PolicyExecution.initial _ (State.initial _ runtime.initial))).map PolicyTrace.last at h
  exact h.trans (runtime.messageApplication.tracePolicies_last ..)

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.extractedSourceCoupling_source' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedSourceCoupling_source

/-- info: 'Vegas.SealedCompilation.extractedSourceCoupling_prefix_native' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedSourceCoupling_prefix_native

/-- info: 'Vegas.SealedCompilation.extractedSourceCoupling_native' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedSourceCoupling_native
