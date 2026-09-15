/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateGraphCoupling
import Vegas.Compile.SealedCandidatePublicPrefix
import Vegas.Compile.SealedFirstTimeoutPrerequisites
import Interaction.SealedResolutionFirstTimeout

/-! # The public source of a candidate timeout comparison

A supported graph/native pair that reaches a timeout retains a specific
commitment producer whose earlier public inputs agree with the graph outcome.
The producer is recovered at the first timeout, before defaults can change
the continuation. Its public inputs remain equal at the later native readout,
despite arbitrary intervening traffic and defaults. Quitting incentives and
deadline-relative attribution to a deviator are separate from this coupling law.
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

/-- A timeout readout has a defaulted commitment producer whose public
declared inputs still match the retained graph realization. The timeout may
be at the commitment or its reveal; the comparison boundary is the producer
in either case. This is a joint coupling fact, not a marginal-law consequence. -/
theorem candidateGraphCoupling_timeout_public_prefix
    (hwindow : 0 < window) (profile : CommitPolicyProfile G) (cfg : ReachableConfig G)
    (trace : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyTrace)
    (hpair : (cfg, trace) ∈ (supported.candidateGraphCoupling hinfo hguards nullValue window
      focal deviator environment schedule fallback profile).support)
    (checkpoint : Nat)
    (htimeout : (trace.drop checkpoint).first.native.application.visible.timeouts ≠ []) :
    ∃ (timeoutNode producer : Fin G.nodeCount) (owner : Player) (guard : EventGuard L),
      timeoutNode.val ∈ (trace.drop checkpoint).first.native.application.visible.timeouts ∧
      (G.nodeRow producer).sem = .commit owner guard ∧
      (timeoutNode = producer ∨
        (G.nodeRow timeoutNode).sem = .reveal (G.nodeTarget producer)) ∧
      ∀ ref ∈ guard.choiceReads, G.fieldRefPublic ref →
        Store.getAs (G.publicSealedStore ty
          (trace.drop checkpoint).first.native.application.visible.events) ref.field ref.ty =
            Store.getAs cfg.1.store ref.field ref.ty := by
  let runtime := supported.resolvingRuntime nullValue window
  let prepare := fun (candidates : CommitmentCandidates Player Nat (L.Val ty)) owner slot value =>
    candidates.prepare owner slot value
  let players := Profile.update (sig := policySignature Player runtime.candidateApplication)
    (fun who => runtime.candidatePlayerPolicy
      (supported.resolvingPolicy nullValue window who (profile who))) focal
    (fun history view => FinDist.pure (deviator history view))
  let nativeEnvironment : runtime.candidateApplication.EnvironmentPolicy :=
    fun history view => FinDist.pure (environment history view)
  let initial := PolicyExecution.initial runtime.candidateApplication
    (State.initial _ runtime.candidateInitial)
  let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
    !execution.native.application.visible.timeouts.isEmpty
  have hnative : trace ∈ (runtime.candidateApplication.tracePolicies players nativeEnvironment
      schedule initial).support := by
    rw [← supported.candidateGraphCoupling_native hinfo hguards nullValue window focal deviator
      environment schedule fallback profile, FinDist.support_map]
    exact ⟨(cfg, trace), hpair, rfl⟩
  have hselectedStop : stop (trace.drop checkpoint).first = true := by
    simpa [stop] using htimeout
  have hstop : (trace.firstRelease stop).native.application.visible.timeouts ≠ [] := by
    simpa [stop] using trace.release_firstRelease_of_drop_first stop checkpoint hselectedStop
  have hcutBound := trace.prefixThrough_length_le_of_drop_first stop checkpoint hselectedStop
  have hinitialClear : initial.native.application.visible.timeouts = [] := by
    change (runtime.refresh false {}).timeouts = []
    rw [runtime.refresh_false_timeouts]
  obtain ⟨index, _hindex, hcut, hselected, hclear, hready⟩ :=
    runtime.tracePolicies_first_timeout_prerequisites prepare runtime.candidateHandle
      runtime.candidateHandle_records hwindow players nativeEnvironment schedule initial trace
      hnative (SealedResolution.PublicState.ReadySound.initial runtime) hinitialClear hstop
  change (trace.prefixThrough stop).length = index + 1 at hcut
  have hindexBound : index + 1 ≤ checkpoint := by omega
  obtain ⟨timeoutIndex, hfirstTimeout⟩ := List.exists_mem_of_ne_nil _ hstop
  obtain ⟨rule, _timestamp, hrule, _hstamped, hrequires⟩ := hready timeoutIndex hfirstTimeout
  obtain ⟨timeoutNode, hnode, _⟩ := supported.ruleAt_exists_node hrule
  subst timeoutIndex
  have hbefore := (runtime.candidateApplication.tracePolicies_drop_support players
    nativeEnvironment schedule initial trace hnative index).1
  have hpublic := runtime.runPolicies_candidate_publicEvents
    runtime.candidateHandle_sound players nativeEnvironment
    (schedule.take index) initial (trace.drop index).first
    (SealedResolution.PublicEventInvariant.initial runtime) hbefore
  have hcandidates := runtime.runPolicies_candidate_prerequisites players nativeEnvironment
    (schedule.take index) (trace.drop index).first hbefore
  obtain ⟨producer, owner, guard, hcommit, hsite, hprerequisites⟩ :=
    supported.ready_node_producer_prerequisites nullValue window
      (trace.drop index).first.native.application.visible hpublic hcandidates hclear
      timeoutNode rule hrule hrequires
  have hafter := runtime.candidateApplication.tracePolicies_between players nativeEnvironment
    schedule initial trace hnative index (checkpoint - index)
  rw [Nat.add_sub_of_le (by omega : index ≤ checkpoint)] at hafter
  have htimeoutSuffix := runtime.candidateApplication.tracePolicies_between players
    nativeEnvironment schedule initial trace hnative (index + 1) (checkpoint - (index + 1))
  rw [Nat.add_sub_of_le hindexBound, ← hselected] at htimeoutSuffix
  have hpersistent := runtime.runPolicies_timeout_mem prepare runtime.candidateHandle
    runtime.candidateHandle_records players nativeEnvironment
    ((schedule.drop (index + 1)).take (checkpoint - (index + 1)))
    (trace.firstRelease stop) (trace.drop checkpoint).first timeoutNode.val
    hfirstTimeout htimeoutSuffix
  refine ⟨timeoutNode, producer, owner, guard, hpersistent, hcommit, hsite, ?_⟩
  intro ref href hrefPublic
  exact supported.candidate_publicRead_eq_of_prereqs_done nullValue window players
    nativeEnvironment ((schedule.drop index).take (checkpoint - index))
    (trace.drop index).first (trace.drop checkpoint).first hpublic hafter producer owner guard
    hcommit hprerequisites cfg
    (supported.candidateGraphCoupling_opened_before_timeout hinfo hguards nullValue window
      focal deviator environment schedule fallback profile cfg trace hpair index (by
        change index < (trace.prefixThrough stop).length
        omega))
    ref href hrefPublic

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.candidateGraphCoupling_timeout_public_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidateGraphCoupling_timeout_public_prefix
