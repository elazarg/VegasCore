/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateGraphRounds
import Vegas.Compile.SealedCandidateTimeoutPrefix
import Vegas.Compile.SealedGraphSettlement
import Interaction.SealedCandidateSettlement

/-! # Prefix-aligned settlement at a candidate timeout

The actual stopped candidate readout is paired with a legal terminal graph
settlement that records the designated default at the first-timeout producer.
The settlement and the retained unilateral graph continuation agree on every
public input read by that producer's source guard.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (supported : SealedFragment G ty) (hinfo : G.PublicPrefixReadable)
variable (hguards : GuardLive G) (hunique : G.UniqueReveals)
variable (nullValue : L.Val ty) (window : Nat) (principals : List Player)
variable (serviceSlots count : Nat) (focal : Player)
variable (deviator :
  List (supported.resolvingRuntime nullValue window).candidateApplication.PlayerEntry →
  (supported.resolvingRuntime nullValue window).candidateApplication.View →
  (supported.resolvingRuntime nullValue window).candidateApplication.PlayerCommand)
variable (environment :
  List (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentEntry →
  (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentObservation →
  (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentPolicyCommand)
variable (fallback : L.Val ty)

/-- A completed timed-out readout of the actual candidate round has a terminal
graph settlement at its specific first-timeout producer.  The selected public
store connects that settlement to the retained graph continuation on every
public guard input. -/
theorem candidateGraphRoundCoupling_timeout_settlement
    (hwindow : 0 < window) (hunique : G.UniqueReveals)
    (profile : CommitPolicyProfile G)
    (continuedCfg : ReachableConfig G)
    (selected : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution)
    (hpair : (continuedCfg, selected) ∈
      (supported.candidateGraphRoundCoupling hinfo hguards nullValue window principals
        serviceSlots count focal deviator environment fallback profile).support)
    (hcomplete : (supported.resolvingRuntime nullValue window).complete
      selected.native.application.visible = true)
    (htimeouts : selected.native.application.visible.timeouts ≠ []) :
    ∃ (timeoutNode producer : Fin G.nodeCount) (owner : Player) (guard : EventGuard L)
      (quittingCfg : ReachableConfig G),
      timeoutNode.val ∈ selected.native.application.visible.timeouts ∧
      (G.nodeRow producer).sem = .commit owner guard ∧
      (timeoutNode = producer ∨
        (G.nodeRow timeoutNode).sem = .reveal (G.nodeTarget producer)) ∧
      Terminal G quittingCfg.1 ∧
      quittingCfg.1.store (G.nodeTarget producer) =
        some (⟨ty, nullValue⟩ : TypedValue L) ∧
      (∀ ref, G.fieldRefPublic ref →
        Store.getAs (G.publicSealedStore ty selected.native.application.visible.events)
          ref.field ref.ty = Store.getAs quittingCfg.1.store ref.field ref.ty) ∧
      ∀ ref ∈ guard.choiceReads, G.fieldRefPublic ref →
        Store.getAs quittingCfg.1.store ref.field ref.ty =
          Store.getAs continuedCfg.1.store ref.field ref.ty := by
  let runtime := supported.resolvingRuntime nullValue window
  let players := Profile.update (sig := policySignature Player runtime.candidateApplication)
    (fun who => runtime.candidatePlayerPolicy
      (supported.resolvingPolicy nullValue window who (profile who))) focal
    (fun history view => FinDist.pure (deviator history view))
  let nativeEnvironment : runtime.candidateApplication.EnvironmentPolicy :=
    fun history view => FinDist.pure (environment history view)
  let schedule := roundSchedule principals serviceSlots count
  let width := (roundInvocations principals serviceSlots).length
  let release := fun execution : runtime.candidateApplication.PolicyExecution =>
    runtime.complete execution.native.application.visible
  let initial := PolicyExecution.initial runtime.candidateApplication
    (State.initial _ runtime.candidateInitial)
  simp only [candidateGraphRoundCoupling, FinDist.support_map, Set.mem_image] at hpair
  obtain ⟨⟨graphCfg, trace⟩, hpair, heq⟩ := hpair
  have hcfgEq : graphCfg = continuedCfg := congrArg Prod.fst heq
  have hselectedEq : trace.firstReleaseEvery width release count = selected :=
    congrArg Prod.snd heq
  subst graphCfg
  have hnative : trace ∈ (runtime.candidateApplication.tracePolicies players nativeEnvironment
      schedule initial).support := by
    have hmap : trace ∈ ((supported.candidateGraphCoupling hinfo hguards nullValue window
        focal deviator environment schedule fallback profile).map Prod.snd).support := by
      rw [FinDist.support_map]
      exact ⟨(continuedCfg, trace), hpair, rfl⟩
    rw [supported.candidateGraphCoupling_native] at hmap
    exact hmap
  obtain ⟨checkpoint, _hcheckpoint, hindexed, _hrelease⟩ :=
    trace.firstReleaseEvery_indexed width release count
  have hdropEq : (trace.drop checkpoint).first = selected :=
    hindexed.symm.trans hselectedEq
  obtain ⟨timeoutNode, producer, owner, guard, htimeout, hcommit, hsite, hprefix⟩ :=
    supported.candidateGraphCoupling_timeout_public_prefix hinfo hguards nullValue window focal
      deviator environment schedule fallback hwindow profile continuedCfg trace hpair checkpoint
      (by simpa only [hdropEq] using htimeouts)
  have hselectedRun := (runtime.candidateApplication.tracePolicies_drop_support players
    nativeEnvironment schedule initial trace hnative checkpoint).1
  rw [hdropEq] at hselectedRun
  have hpublic := runtime.runPolicies_candidate_publicEvents
    runtime.candidateHandle_sound players nativeEnvironment
    (schedule.take checkpoint) initial selected
    (SealedResolution.PublicEventInvariant.initial runtime) hselectedRun
  have hsettlement := SealedResolution.runPolicies_candidate_settlementInvariant runtime
    players nativeEnvironment (schedule.take checkpoint) initial selected
    (SealedResolution.SettlementInvariant.initial runtime) hselectedRun
  obtain ⟨quittingCfg, hterminal, hagrees, hnull⟩ :=
    supported.public_store_graph_choice_at_producer_of_timeout hguards hunique nullValue window
      selected.native.application.visible hpublic hsettlement hcomplete producer owner guard
      hcommit timeoutNode (by simpa only [hdropEq] using htimeout) hsite
  refine ⟨timeoutNode, producer, owner, guard, quittingCfg, ?_, hcommit, hsite,
    hterminal, hnull, hagrees, ?_⟩
  · simpa only [hdropEq] using htimeout
  · intro ref href hrefPublic
    exact (hagrees ref hrefPublic).symm.trans
      (by simpa only [hdropEq] using hprefix ref href hrefPublic)

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.candidateGraphRoundCoupling_timeout_settlement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidateGraphRoundCoupling_timeout_settlement
