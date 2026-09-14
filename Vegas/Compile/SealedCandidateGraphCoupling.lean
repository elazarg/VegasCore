/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateGraphNative
import Interaction.MessageApplicationContinuation
import Vegas.Compile.SealedPublicOutcome
import Interaction.SealedCandidateEvents

/-! # Graph/native coupling with the actual timeout continuation

A complete graph realization determines the native prefix through first timeout.
Resuming the actual policies retains the complete native law and the ordinary
graph law as marginals. On normal completion their public fields agree pointwise.
No fairness or quitting-utility premise is needed for these coupling laws;
utility comparisons after timeout are separate.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (supported : SealedFragment G ty) (hinfo : G.PublicPrefixReadable) (hguards : GuardLive G)
variable (nullValue : L.Val ty) (window : Nat) (focal : Player)
variable (deviator :
  List (supported.resolvingRuntime nullValue window).candidateApplication.PlayerEntry →
  (supported.resolvingRuntime nullValue window).candidateApplication.View →
  (supported.resolvingRuntime nullValue window).candidateApplication.PlayerCommand)
variable (environment :
  List (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentEntry →
  (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentObservation →
  (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player)) (fallback : L.Val ty)

/-- Retain a complete graph realization, replay its native prefix through
first timeout, and run the actual native continuation. The invocation suffix
is determined by the retained prefix length, including waits and rejected
commands; private and environment histories are retained in its last state. -/
def candidateGraphCoupling (profile : CommitPolicyProfile G) :
    FinDist (ReachableConfig G ×
      (supported.resolvingRuntime nullValue
        window).candidateApplication.PolicyTrace) :=
  let runtime := supported.resolvingRuntime nullValue window
  let players := Profile.update (sig := policySignature Player runtime.candidateApplication)
    (fun who => runtime.candidatePlayerPolicy
      (supported.resolvingPolicy nullValue window who (profile who))) focal
    (fun history view => FinDist.pure (deviator history view))
  let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
    !execution.native.application.visible.timeouts.isEmpty
  runtime.candidateApplication.couplePrefix players
    (fun history view => FinDist.pure (environment history view)) schedule
    (supported.candidateGraphRun hinfo hguards nullValue window focal deviator environment
      schedule fallback profile) (fun cfg => (supported.candidateReplay nullValue window
        (cfg.1.nodeValues fallback) focal deviator environment schedule).prefixThrough stop)

/-- Attaching a normalized native suffix does not change the retained graph
realization, even when that suffix responds to a timeout settlement. -/
theorem candidateGraphCoupling_graph
    (profile : CommitPolicyProfile G) :
    (supported.candidateGraphCoupling hinfo hguards nullValue window focal deviator environment
      schedule fallback profile).map Prod.fst =
      supported.candidateGraphRun hinfo hguards nullValue window focal deviator environment
        schedule fallback profile := by
  exact MessageApplication.couplePrefix_fst _ _ _ _ _ _

/-- The coupling preserves the joint law of the stopped native prefix and the
complete native trace. Thus it retains their dependence, not just separate
marginal laws. -/
theorem candidateGraphCoupling_prefix_native
    (profile : CommitPolicyProfile G) :
    let runtime := supported.resolvingRuntime nullValue window
    let players := Profile.update (sig := policySignature Player runtime.candidateApplication)
      (fun who => runtime.candidatePlayerPolicy
        (supported.resolvingPolicy nullValue window who (profile who))) focal
      (fun history view => FinDist.pure (deviator history view))
    let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    (supported.candidateGraphCoupling hinfo hguards nullValue window focal deviator environment
      schedule fallback profile).map (fun pair =>
        ((supported.candidateReplay nullValue window (pair.1.1.nodeValues fallback)
          focal deviator environment schedule).prefixThrough stop, pair.2)) =
      (runtime.candidateApplication.tracePolicies players
        (fun history view => FinDist.pure (environment history view)) schedule
        (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).map
          (fun trace => (trace.prefixThrough stop, trace)) := by
  intro runtime players stop
  exact runtime.candidateApplication.couplePrefix_prefix_native players
    (fun history view => FinDist.pure (environment history view)) stop schedule
    (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial)) _ _
    (supported.candidateGraphRun_native_prefix_law hinfo hguards nullValue window focal deviator
      environment schedule fallback profile)

/-- The other marginal is the complete native trace, including its actual
post-timeout behavior. No settlement, fairness, or graph/native utility
premise is needed for this trace-law identity. -/
theorem candidateGraphCoupling_native
    (profile : CommitPolicyProfile G) :
    let runtime := supported.resolvingRuntime nullValue window
    let players := Profile.update (sig := policySignature Player runtime.candidateApplication)
      (fun who => runtime.candidatePlayerPolicy
        (supported.resolvingPolicy nullValue window who (profile who))) focal
      (fun history view => FinDist.pure (deviator history view))
    (supported.candidateGraphCoupling hinfo hguards nullValue window focal deviator environment
      schedule fallback profile).map Prod.snd =
      runtime.candidateApplication.tracePolicies players
        (fun history view => FinDist.pure (environment history view)) schedule
        (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial)) := by
  intro runtime players
  exact runtime.candidateApplication.couplePrefix_native players
    (fun history view => FinDist.pure (environment history view))
    (fun execution => !execution.native.application.visible.timeouts.isEmpty) schedule
    (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial)) _ _
    (supported.candidateGraphRun_native_prefix_law hinfo hguards nullValue window focal deviator
      environment schedule fallback profile)

/-- In the absence of timeout, no post-cutoff suffix was resampled: the actual
full trace is the complete fixed-response replay of the retained graph
realization. The statement concerns supported pairs in the constructed coupling,
not a consequence inferred from its marginal equalities. -/
theorem candidateGraphCoupling_clear
    (profile : CommitPolicyProfile G)
    (cfg : ReachableConfig G)
    (trace :
      (supported.resolvingRuntime nullValue window).candidateApplication.PolicyTrace)
    (hpair : (cfg, trace) ∈ (supported.candidateGraphCoupling hinfo hguards nullValue window focal
      deviator environment schedule fallback profile).support)
    (hclear : trace.last.native.application.visible.timeouts = []) :
    cfg ∈ (supported.candidateGraphRun hinfo hguards nullValue window focal deviator environment
      schedule fallback profile).support ∧
    trace = supported.candidateReplay nullValue window (cfg.1.nodeValues fallback)
      focal deviator environment schedule ∧
    trace.last = supported.candidateStop nullValue window (cfg.1.nodeValues fallback)
      focal deviator environment schedule := by
  simp only [candidateGraphCoupling, MessageApplication.couplePrefix,
    FinDist.support_bind, Set.mem_iUnion,
    FinDist.support_map, Set.mem_image, Prod.mk.injEq] at hpair
  obtain ⟨realization, hrealization, suffix, hsuffix, rfl, rfl⟩ := hpair
  refine ⟨hrealization, ?_⟩
  let runtime := supported.resolvingRuntime nullValue window
  let replayed := supported.candidateReplay nullValue window
    (realization.1.nodeValues fallback) focal deviator environment schedule
  let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
    !execution.native.application.visible.timeouts.isEmpty
  have hsuffixLast : suffix.last.native.application.visible.timeouts = [] := by
    simpa only [PolicyTrace.append_last] using hclear
  have hbefore := runtime.runPolicies_candidate_clear_before _ _ _ _ _
    (by
      rw [← runtime.candidateApplication.tracePolicies_last, FinDist.support_map]
      exact ⟨suffix, hsuffix, rfl⟩)
    hsuffixLast
  have hstopped : replayed.prefixThrough stop = replayed := by
    apply replayed.prefixThrough_eq_of_last_false stop
    change (!(replayed.prefixThrough stop).last.native.application.visible.timeouts.isEmpty) = false
    rw [hbefore]
    rfl
  have hlength : replayed.length = schedule.length := by
    apply runtime.candidateApplication.tracePolicies_length
      (supported.candidateValuePlayers nullValue window
        (realization.1.nodeValues fallback) focal
        (fun history view => FinDist.pure (deviator history view)))
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial)) replayed
    rw [supported.candidateReplay_law, FinDist.mem_support_pure]
  change suffix ∈ (runtime.candidateApplication.tracePolicies _ _
    (schedule.drop (replayed.prefixThrough stop).length)
    (replayed.prefixThrough stop).last).support at hsuffix
  rw [hstopped, hlength, List.drop_length, tracePolicies,
    FinDist.mem_support_pure] at hsuffix
  subst suffix
  constructor
  · rw [hstopped]
    exact PolicyTrace.append_finish_last replayed
  · rw [PolicyTrace.append_last]
    change replayed.last = replayed.firstRelease stop
    rw [← PolicyTrace.prefixThrough_last, hstopped]

/-- On normal completion, every public typed field agrees with the retained
graph realization. This is a pointwise property of the constructed coupling,
not a consequence of its marginal identities or an arbitrary settlement witness. -/
theorem candidateGraphCoupling_public_store
    (profile : CommitPolicyProfile G)
    (cfg : ReachableConfig G)
    (trace :
      (supported.resolvingRuntime nullValue window).candidateApplication.PolicyTrace)
    (hpair : (cfg, trace) ∈ (supported.candidateGraphCoupling hinfo hguards nullValue window focal
      deviator environment schedule fallback profile).support)
    (hcomplete : (supported.resolvingRuntime nullValue window).complete
      trace.last.native.application.visible = true)
    (hclear : trace.last.native.application.visible.timeouts = [])
    (ref : FieldRef L) (hpublic : G.fieldRefPublic ref) :
    Store.getAs (G.publicSealedStore ty
      trace.last.native.application.visible.events) ref.field ref.ty =
        Store.getAs cfg.1.store ref.field ref.ty := by
  let runtime := supported.resolvingRuntime nullValue window
  let players := Profile.update (sig := policySignature Player runtime.candidateApplication)
    (fun who => runtime.candidatePlayerPolicy
      (supported.resolvingPolicy nullValue window who (profile who))) focal
    (fun history view => FinDist.pure (deviator history view))
  let nativeEnvironment : runtime.candidateApplication.EnvironmentPolicy :=
    fun history view => FinDist.pure (environment history view)
  let initial := PolicyExecution.initial runtime.candidateApplication
    (State.initial _ runtime.candidateInitial)
  obtain ⟨hcfg, _, hstop⟩ := supported.candidateGraphCoupling_clear hinfo hguards nullValue window
    focal deviator environment schedule fallback profile cfg trace hpair hclear
  have hterminal := supported.candidateGraphRun_terminal hinfo hguards nullValue window focal
    deviator environment schedule fallback profile cfg hcfg
  have hnative : trace ∈ ((supported.candidateGraphCoupling hinfo hguards nullValue window focal
      deviator environment schedule fallback profile).map Prod.snd).support := by
    rw [FinDist.support_map]
    exact ⟨(cfg, trace), hpair, rfl⟩
  rw [supported.candidateGraphCoupling_native] at hnative
  have hfinal : trace.last ∈ (runtime.candidateApplication.runPolicies players nativeEnvironment
      schedule initial).support := by
    rw [← runtime.candidateApplication.tracePolicies_last, FinDist.support_map]
    exact ⟨trace, hnative, rfl⟩
  have hinvariant := runtime.runPolicies_candidate_publicEvents players nativeEnvironment
    schedule initial trace.last (SealedResolution.PublicEventInvariant.initial _) hfinal
  have hopening := runtime.runPolicies_candidate_openings players nativeEnvironment schedule
    initial trace.last SealedResolution.CandidateOpeningInvariant.initial hfinal
  have haccepted := supported.candidateGraphRun_accepted hinfo hguards
    nullValue window focal deviator environment schedule fallback _ cfg hcfg (fun _ => false)
  dsimp only at haccepted
  simp only [PolicyTrace.firstRelease_false_eq_last, PolicyTrace.prefixThrough_last] at haccepted
  dsimp only [SealedFragment.candidateStop] at hstop
  rw [← hstop] at haccepted
  exact supported.publicSealedStore_agrees_of_opened_values nullValue window
    trace.last.native.application.visible hinvariant hcomplete cfg
    (supported.candidate_opened_graph_value cfg hterminal nullValue window
      trace.last.native.application hopening hclear haccepted) ref hpublic

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.candidateGraphCoupling_prefix_native'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidateGraphCoupling_prefix_native

/-- info: 'Vegas.EventGraph.SealedFragment.candidateGraphCoupling_public_store'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidateGraphCoupling_public_store
