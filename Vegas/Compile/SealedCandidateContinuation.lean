/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateNativeLikelihood
import Interaction.MessageApplicationContinuation
import Vegas.Compile.SealedPublicOutcome
import Interaction.SealedCandidateEvents

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
  let runtime := compilation.supported.resolvingRuntime nullValue window
  let players := Profile.update (sig := policySignature Player runtime.candidateApplication)
    (fun who => compilation.compileCandidatePolicy nullValue window who (profile who)) focal
    (fun history view => FinDist.pure (deviator history view))
  let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
    !execution.native.application.visible.timeouts.isEmpty
  runtime.candidateApplication.couplePrefix players
    (fun history view => FinDist.pure (environment history view)) schedule
    (compilation.extractedCandidateSourceRun nullValue window focal deviator environment
      schedule fallback profile) (fun cfg => (compilation.supported.candidateReplay nullValue window
        (cfg.1.nodeValues fallback) focal deviator environment schedule).prefixThrough stop)

/-- Attaching a normalized native suffix does not change the retained source
realization, even when that suffix responds to a timeout settlement. -/
theorem extractedCandidateSourceCoupling_realization
    (profile : SourceBehavioralProfile source.core.prog) :
    (compilation.extractedCandidateSourceCoupling nullValue window focal deviator environment
      schedule fallback profile).map Prod.fst =
      compilation.extractedCandidateSourceRun nullValue window focal deviator environment
        schedule fallback profile := by
  exact MessageApplication.couplePrefix_fst _ _ _ _ _ _

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
  rw [← FinDist.map_comp, compilation.extractedCandidateSourceCoupling_realization]
  exact compilation.extractedCandidateSourceRun_source nullValue window focal deviator
    environment schedule fallback profile

/-- The coupling preserves the joint law of the stopped native prefix and the
complete native trace. Thus it retains their dependence, not just separate
marginal laws. -/
theorem extractedCandidateSourceCoupling_prefix_native
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := Profile.update (sig := policySignature Player runtime.candidateApplication)
      (fun who => compilation.compileCandidatePolicy nullValue window who (profile who)) focal
      (fun history view => FinDist.pure (deviator history view))
    let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    (compilation.extractedCandidateSourceCoupling nullValue window focal deviator environment
      schedule fallback profile).map (fun pair =>
        ((compilation.supported.candidateReplay nullValue window (pair.1.1.nodeValues fallback)
          focal deviator environment schedule).prefixThrough stop, pair.2)) =
      (runtime.candidateApplication.tracePolicies players
        (fun history view => FinDist.pure (environment history view)) schedule
        (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).map
          (fun trace => (trace.prefixThrough stop, trace)) := by
  intro runtime players stop
  exact runtime.candidateApplication.couplePrefix_prefix_native players
    (fun history view => FinDist.pure (environment history view)) stop schedule
    (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial)) _ _
    (compilation.extractedCandidateSourceRun_native_prefix_law nullValue window focal deviator
      environment schedule fallback profile)

/-- The other marginal is the complete native trace, including its actual
post-timeout behavior. No settlement, fairness, or source/native utility
premise is needed for this trace-law identity. -/
theorem extractedCandidateSourceCoupling_native
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := Profile.update (sig := policySignature Player runtime.candidateApplication)
      (fun who => compilation.compileCandidatePolicy nullValue window who (profile who)) focal
      (fun history view => FinDist.pure (deviator history view))
    (compilation.extractedCandidateSourceCoupling nullValue window focal deviator environment
      schedule fallback profile).map Prod.snd =
      runtime.candidateApplication.tracePolicies players
        (fun history view => FinDist.pure (environment history view)) schedule
        (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial)) := by
  intro runtime players
  exact runtime.candidateApplication.couplePrefix_native players
    (fun history view => FinDist.pure (environment history view))
    (fun execution => !execution.native.application.visible.timeouts.isEmpty) schedule
    (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial)) _ _
    (compilation.extractedCandidateSourceRun_native_prefix_law nullValue window focal deviator
      environment schedule fallback profile)

/-- In the absence of timeout, no post-cutoff suffix was resampled: the actual
full trace is the complete fixed-response replay of the retained source
realization. The statement concerns supported pairs in the constructed coupling,
not a consequence inferred from its marginal equalities. -/
theorem extractedCandidateSourceCoupling_clear
    (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (trace :
      (compilation.supported.resolvingRuntime nullValue window).candidateApplication.PolicyTrace)
    (hpair : (cfg, trace) ∈ (compilation.extractedCandidateSourceCoupling nullValue window focal
      deviator environment schedule fallback profile).support)
    (hclear : trace.last.native.application.visible.timeouts = []) :
    cfg ∈ (compilation.extractedCandidateSourceRun nullValue window focal deviator environment
      schedule fallback profile).support ∧
    trace = compilation.supported.candidateReplay nullValue window (cfg.1.nodeValues fallback)
      focal deviator environment schedule ∧
    trace.last = compilation.supported.candidateStop nullValue window (cfg.1.nodeValues fallback)
      focal deviator environment schedule := by
  simp only [extractedCandidateSourceCoupling, MessageApplication.couplePrefix,
    FinDist.support_bind, Set.mem_iUnion,
    FinDist.support_map, Set.mem_image, Prod.mk.injEq] at hpair
  obtain ⟨realization, hrealization, suffix, hsuffix, rfl, rfl⟩ := hpair
  refine ⟨hrealization, ?_⟩
  let runtime := compilation.supported.resolvingRuntime nullValue window
  let replayed := compilation.supported.candidateReplay nullValue window
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
      (compilation.supported.candidateValuePlayers nullValue window
        (realization.1.nodeValues fallback) focal
        (fun history view => FinDist.pure (deviator history view)))
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial)) replayed
    rw [compilation.supported.candidateReplay_law, FinDist.mem_support_pure]
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
source realization. This is a pointwise property of the constructed coupling,
not a consequence of its marginal identities or an arbitrary settlement witness. -/
theorem extractedCandidateSourceCoupling_public_store
    (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (trace :
      (compilation.supported.resolvingRuntime nullValue window).candidateApplication.PolicyTrace)
    (hpair : (cfg, trace) ∈ (compilation.extractedCandidateSourceCoupling nullValue window focal
      deviator environment schedule fallback profile).support)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      trace.last.native.application.visible = true)
    (hclear : trace.last.native.application.visible.timeouts = [])
    (ref : FieldRef L) (hpublic : (compile source.core).graph.fieldRefPublic ref) :
    Store.getAs ((compile source.core).graph.publicSealedStore ty
      trace.last.native.application.visible.events) ref.field ref.ty =
        Store.getAs cfg.1.store ref.field ref.ty := by
  let runtime := compilation.supported.resolvingRuntime nullValue window
  let players := Profile.update (sig := policySignature Player runtime.candidateApplication)
    (fun who => compilation.compileCandidatePolicy nullValue window who (profile who)) focal
    (fun history view => FinDist.pure (deviator history view))
  let nativeEnvironment : runtime.candidateApplication.EnvironmentPolicy :=
    fun history view => FinDist.pure (environment history view)
  let initial := PolicyExecution.initial runtime.candidateApplication
    (State.initial _ runtime.candidateInitial)
  obtain ⟨hcfg, _, hstop⟩ := compilation.extractedCandidateSourceCoupling_clear nullValue window
    focal deviator environment schedule fallback profile cfg trace hpair hclear
  have hterminal := compilation.sourceRunOfDisclosures_terminal focal _ profile cfg hcfg
  have hnative : trace ∈ ((compilation.extractedCandidateSourceCoupling nullValue window focal
      deviator environment schedule fallback profile).map Prod.snd).support := by
    rw [FinDist.support_map]
    exact ⟨(cfg, trace), hpair, rfl⟩
  rw [compilation.extractedCandidateSourceCoupling_native] at hnative
  have hfinal : trace.last ∈ (runtime.candidateApplication.runPolicies players nativeEnvironment
      schedule initial).support := by
    rw [← runtime.candidateApplication.tracePolicies_last, FinDist.support_map]
    exact ⟨trace, hnative, rfl⟩
  have hinvariant := runtime.runPolicies_candidate_publicEvents players nativeEnvironment
    schedule initial trace.last (SealedResolution.PublicEventInvariant.initial _) hfinal
  have hopening := runtime.runPolicies_candidate_openings players nativeEnvironment schedule
    initial trace.last SealedResolution.CandidateOpeningInvariant.initial hfinal
  have haccepted := compilation.supported.candidateGraphRun_accepted
    (compile_publicPrefixReadable source.core) (compile_guardLive source.core source.legal)
    nullValue window focal deviator environment schedule fallback _ cfg hcfg (fun _ => false)
  dsimp only at haccepted
  simp only [PolicyTrace.firstRelease_false_eq_last, PolicyTrace.prefixThrough_last] at haccepted
  dsimp only [SealedFragment.candidateStop] at hstop
  rw [← hstop] at haccepted
  exact compilation.supported.publicSealedStore_agrees_of_opened_values nullValue window
    trace.last.native.application.visible hinvariant hcomplete cfg
    (compilation.supported.candidate_opened_source_value cfg hterminal nullValue window
      trace.last.native.application hopening hclear haccepted) ref hpublic

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
    (compilation.extractedCandidateSourceCoupling_public_store nullValue window focal deviator
      environment schedule fallback profile cfg trace hpair hcomplete hclear)

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.extractedCandidateSourceCoupling_prefix_native'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedCandidateSourceCoupling_prefix_native

/-- info: 'Vegas.SealedCompilation.extractedCandidateSourceCoupling_payout_of_complete_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedCandidateSourceCoupling_payout_of_complete_clear
