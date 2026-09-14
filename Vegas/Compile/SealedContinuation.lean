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

/-- In the absence of timeout, no post-cutoff suffix was resampled: the actual
final execution is the complete fixed-response replay of the retained source
realization. The statement concerns supported pairs in the constructed coupling,
not a consequence inferred from its marginal equalities. -/
theorem extractedSourceCoupling_clear
    (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (final :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hpair : (cfg, final) ∈ (compilation.extractedSourceCoupling nullValue window focal deviator
      environment schedule fallback profile).support)
    (hclear : final.native.application.visible.timeouts = []) :
    cfg ∈ (compilation.extractedSourceRun nullValue window focal deviator environment schedule
      fallback profile).support ∧
    final = (compilation.supported.resolvingReplay nullValue window (cfg.1.nodeValues fallback)
      focal deviator environment schedule).last ∧
    final = compilation.supported.resolvingStop nullValue window (cfg.1.nodeValues fallback)
      focal deviator environment schedule := by
  simp only [extractedSourceCoupling, FinDist.support_bind, Set.mem_iUnion,
    FinDist.support_map, Set.mem_image, Prod.mk.injEq] at hpair
  obtain ⟨realization, hrealization, result, hresult, rfl, rfl⟩ := hpair
  refine ⟨hrealization, ?_⟩
  let runtime := compilation.supported.resolvingRuntime nullValue window
  let replayed := compilation.supported.resolvingReplay nullValue window
    (realization.1.nodeValues fallback) focal deviator environment schedule
  let stop := fun execution : runtime.messageApplication.PolicyExecution =>
    !execution.native.application.visible.timeouts.isEmpty
  have hbefore := runtime.runPolicies_clear_before _ _ _ _ _ hresult hclear
  have hstopped : replayed.prefixThrough stop = replayed := by
    apply replayed.prefixThrough_eq_of_last_false stop
    change (!(replayed.prefixThrough stop).last.native.application.visible.timeouts.isEmpty) = false
    rw [hbefore]
    rfl
  have hlength : replayed.length = schedule.length := by
    apply runtime.messageApplication.tracePolicies_length
      (compilation.supported.resolvingValuePlayers nullValue window
        (realization.1.nodeValues fallback) focal
        (fun history view => FinDist.pure (deviator history view)))
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _ runtime.initial)) replayed
    rw [compilation.supported.resolvingReplay_law, FinDist.mem_support_pure]
  change result ∈ (runtime.messageApplication.runPolicies _ _
    (schedule.drop (replayed.prefixThrough stop).length)
    (replayed.prefixThrough stop).last).support at hresult
  rw [hstopped, hlength, List.drop_length, runPolicies, FinDist.mem_support_pure] at hresult
  refine ⟨hresult, ?_⟩
  change result = replayed.firstRelease stop
  rw [← PolicyTrace.prefixThrough_last, hstopped]
  exact hresult

/-- A completed timeout-free native execution decodes to the exact retained
source configuration. Together with the source marginal this identifies the
source outcome on normal completion; it is stronger than merely exhibiting
some source execution with the same accepted events. -/
theorem extractedSourceCoupling_decode_of_complete_clear
    (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (final :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hpair : (cfg, final) ∈ (compilation.extractedSourceCoupling nullValue window focal deviator
      environment schedule fallback profile).support)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      final.native.application.visible = true)
    (hclear : final.native.application.visible.timeouts = []) :
    (compile source.core).graph.decodeSealedFrom ty final.native.application.service
      (Config.initial _) final.native.application.visible.events = some cfg.1 := by
  let runtime := compilation.supported.resolvingRuntime nullValue window
  obtain ⟨hcfg, _, hstop⟩ := compilation.extractedSourceCoupling_clear nullValue window focal
    deviator environment schedule fallback profile cfg final hpair hclear
  have hnative : final ∈ ((compilation.extractedSourceCoupling nullValue window focal deviator
      environment schedule fallback profile).map Prod.snd).support := by
    rw [FinDist.support_map]
    exact ⟨(cfg, final), hpair, rfl⟩
  rw [compilation.extractedSourceCoupling_native] at hnative
  have hbinding := runtime.runPolicies_beforeTimeoutBinding _ _ schedule _ final
    SealedResolution.BeforeTimeoutBinding.initial hnative hclear
  apply compilation.supported.decodeSealed_eq_source cfg
    (compilation.extractedSourceRun_terminal nullValue window focal deviator environment schedule
      fallback profile cfg hcfg) fallback _ hbinding ?_ ?_
  · intro owner node guard hnode value hvalue
    exact compilation.extractedSourceRun_registered nullValue window focal deviator environment
      schedule fallback profile cfg hcfg owner node guard hnode value (by rwa [← hstop])
  · intro node
    have hindex : node.val < runtime.program.rules.length := by
      change node.val < compilation.program.rules.length
      rw [compilation.program_rule_count]
      exact node.isLt
    have hdone := List.all_eq_true.mp hcomplete node.val (List.mem_range.mpr hindex)
    simpa only [SealedResolution.PublicState.completed, hclear, List.contains_nil,
      Bool.or_false] using hdone

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

/-- info: 'Vegas.SealedCompilation.extractedSourceCoupling_clear' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedSourceCoupling_clear

/-- info: 'Vegas.SealedCompilation.extractedSourceCoupling_decode_of_complete_clear' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedSourceCoupling_decode_of_complete_clear
