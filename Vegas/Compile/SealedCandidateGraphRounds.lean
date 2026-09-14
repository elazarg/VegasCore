/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateGraphRandomized
import Vegas.Compile.SealedTermination
import Interaction.SealedCandidateCompletion
import Interaction.MessageApplicationRoundTrace

/-! # Candidate deviation coupling for the actual stopped-round driver

The native readout is the first completed round boundary, or the final budget
boundary. It retains the graph marginal. Normal public results persist through
the unused native suffix, so the full-trace coupling also supplies pointwise
public-field agreement at the selected boundary. No service or quitting-utility
premise is used; timeouts may still determine the completed result.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (supported : SealedFragment G ty) (hinfo : G.PublicPrefixReadable) (hguards : GuardLive G)
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

/-- Select the driver's actual stopping boundary without changing the retained
graph realization. Fixed response functions need not obey a service condition. -/
def candidateGraphRoundCoupling (profile : CommitPolicyProfile G) :
    FinDist (ReachableConfig G ×
      (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution) :=
  let runtime := supported.resolvingRuntime nullValue window
  let schedule := roundSchedule principals serviceSlots count
  let readout := PolicyTrace.firstReleaseEvery
    (roundInvocations principals serviceSlots).length
    (fun execution : runtime.candidateApplication.PolicyExecution =>
      runtime.complete execution.native.application.visible) count
  (supported.candidateGraphCoupling hinfo hguards nullValue window focal deviator environment
    schedule fallback profile).map fun pair => (pair.1, readout pair.2)

/-- Native stopping leaves the ordinary graph law against unchanged opponents
as the other marginal. -/
theorem candidateGraphRoundCoupling_graph (profile : CommitPolicyProfile G) :
    (supported.candidateGraphRoundCoupling hinfo hguards nullValue window principals serviceSlots
      count focal deviator environment fallback profile).map Prod.fst =
      supported.candidateGraphRun hinfo hguards nullValue window focal deviator environment
        (roundSchedule principals serviceSlots count) fallback profile := by
  simpa only [candidateGraphRoundCoupling, FinDist.map_comp, Function.comp_def] using
    supported.candidateGraphCoupling_graph hinfo hguards nullValue window focal deviator
      environment (roundSchedule principals serviceSlots count) fallback profile

/-- Every retained graph configuration is terminal, including when the native
round budget is exhausted before completion. -/
theorem candidateGraphRoundCoupling_terminal (profile : CommitPolicyProfile G)
    (cfg : ReachableConfig G)
    (selected : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution)
    (hpair : (cfg, selected) ∈ (supported.candidateGraphRoundCoupling hinfo hguards nullValue
      window principals serviceSlots count focal deviator environment fallback profile).support) :
    Terminal G cfg.1 := by
  have hcfg : cfg ∈ ((supported.candidateGraphRoundCoupling hinfo hguards nullValue window
      principals serviceSlots count focal deviator environment fallback profile).map
        Prod.fst).support :=
    (FinDist.support_map _ _).symm ▸ ⟨(cfg, selected), hpair, rfl⟩
  rw [supported.candidateGraphRoundCoupling_graph] at hcfg
  exact supported.candidateGraphRun_terminal hinfo hguards nullValue window focal deviator
    environment _ fallback profile cfg hcfg

/-- The selected normally completed public result agrees with the same retained
graph configuration. Unused full-trace traffic may change histories and the
private catalog, but cannot change that public result. -/
theorem candidateGraphRoundCoupling_public_store (profile : CommitPolicyProfile G)
    (cfg : ReachableConfig G)
    (selected : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution)
    (hpair : (cfg, selected) ∈ (supported.candidateGraphRoundCoupling hinfo hguards nullValue window
      principals serviceSlots count focal deviator environment fallback profile).support)
    (hcomplete : (supported.resolvingRuntime nullValue window).complete
      selected.native.application.visible = true)
    (hclear : selected.native.application.visible.timeouts = [])
    (ref : FieldRef L) (hpublic : G.fieldRefPublic ref) :
    Store.getAs (G.publicSealedStore ty selected.native.application.visible.events)
      ref.field ref.ty = Store.getAs cfg.1.store ref.field ref.ty := by
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
  have hcfgEq : graphCfg = cfg := congrArg Prod.fst heq
  have hselectedEq : trace.firstReleaseEvery width release count = selected :=
    congrArg Prod.snd heq
  subst graphCfg
  have hnative : trace ∈ (runtime.candidateApplication.tracePolicies players nativeEnvironment
      schedule initial).support := by
    have hmap : trace ∈ ((supported.candidateGraphCoupling hinfo hguards nullValue window
        focal deviator environment schedule fallback profile).map Prod.snd).support := by
      rw [FinDist.support_map]
      exact ⟨(cfg, trace), hpair, rfl⟩
    rw [supported.candidateGraphCoupling_native] at hmap
    exact hmap
  obtain ⟨_front, suffix, _hschedule, _hselected, hsuffix⟩ :=
    runtime.candidateApplication.tracePolicies_firstReleaseEvery_split
      players nativeEnvironment width count release (by simp [width, roundInvocations])
      schedule initial trace (by simp [schedule, width, roundSchedule_length]) hnative
  rw [hselectedEq] at hsuffix
  obtain ⟨hevents, hfinalClear, hfinalComplete⟩ :=
    runtime.runPolicies_complete_clear _ _ runtime.candidateHandle_eq_none_of_complete_clear
      players nativeEnvironment suffix selected trace.last hcomplete hclear hsuffix
  have hagree := supported.candidateGraphCoupling_public_store hinfo hguards nullValue window focal
    deviator environment schedule fallback profile cfg trace hpair hfinalComplete hfinalClear
    ref hpublic
  simpa only [hevents] using hagree

omit deviator environment in
/-- Arbitrary randomized native deviations and adaptive wire policies admit a
coupling with the actual stopped driver, a finite mixture of unilateral graph
deviations, and pointwise public-field agreement on normal completion. The
usual finite round budget guarantees completion, possibly by timeout. -/
theorem exists_randomized_candidate_round_graph_coupling (profile : CommitPolicyProfile G)
    (replacement :
      (supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy)
    (wire : (supported.resolvingRuntime nullValue window).candidateApplication.WirePolicy) :
    let runtime := supported.resolvingRuntime nullValue window
    let players := fun who =>
      runtime.candidatePlayerPolicy (supported.resolvingPolicy nullValue window who (profile who))
    let schedule := roundSchedule principals serviceSlots count
    let initial := PolicyExecution.initial runtime.candidateApplication
      (State.initial _ runtime.candidateInitial)
    let PlayerResponse := List runtime.candidateApplication.PlayerEntry →
      runtime.candidateApplication.View → runtime.candidateApplication.PlayerCommand
    let EnvironmentResponse := List runtime.candidateApplication.EnvironmentEntry →
      runtime.candidateApplication.EnvironmentObservation →
        runtime.candidateApplication.EnvironmentPolicyCommand
    ∃ responsePairs : FinDist (PlayerResponse × EnvironmentResponse),
      ((responsePairs.bind fun responses =>
        supported.candidateGraphRoundCoupling hinfo hguards nullValue window principals serviceSlots
          count focal responses.1 responses.2 fallback profile).map Prod.fst) =
        responsePairs.bind (fun responses =>
          supported.candidateGraphRun hinfo hguards nullValue window focal responses.1 responses.2
            schedule fallback profile) ∧
      ((responsePairs.bind fun responses =>
        supported.candidateGraphRoundCoupling hinfo hguards nullValue window principals serviceSlots
          count focal responses.1 responses.2 fallback profile).map Prod.snd) =
        runtime.candidateRoundDriver.runRounds principals serviceSlots
          (Profile.update (sig := policySignature Player runtime.candidateApplication)
            players focal replacement) wire count initial ∧
      ∀ cfg selected, (cfg, selected) ∈ (responsePairs.bind fun responses =>
        supported.candidateGraphRoundCoupling hinfo hguards nullValue window principals serviceSlots
          count focal responses.1 responses.2 fallback profile).support →
        Terminal G cfg.1 ∧
        (G.nodeCount * (window + 1) ≤ count →
          runtime.complete selected.native.application.visible = true) ∧
        (runtime.complete selected.native.application.visible = true →
          selected.native.application.visible.timeouts = [] →
          ∀ ref : FieldRef L, G.fieldRefPublic ref →
            Store.getAs (G.publicSealedStore ty selected.native.application.visible.events)
              ref.field ref.ty = Store.getAs cfg.1.store ref.field ref.ty) := by
  intro runtime players schedule initial PlayerResponse EnvironmentResponse
  obtain ⟨responsePairs, _, hgraph, htrace, _⟩ :=
    supported.exists_randomized_candidate_graph_coupling hinfo hguards nullValue window focal
      (runtime.candidateRoundDriver.environmentPolicy serviceSlots wire) schedule fallback profile
      replacement
  have hnative :
      ((responsePairs.bind fun responses =>
        supported.candidateGraphRoundCoupling hinfo hguards nullValue window principals serviceSlots
          count focal responses.1 responses.2 fallback profile).map Prod.snd) =
        runtime.candidateRoundDriver.runRounds principals serviceSlots
          (Profile.update (sig := policySignature Player runtime.candidateApplication)
            players focal replacement) wire count initial := by
    let readout := PolicyTrace.firstReleaseEvery
      (roundInvocations principals serviceSlots).length
      (fun execution : runtime.candidateApplication.PolicyExecution =>
        runtime.complete execution.native.application.visible) count
    have hreadout := congrArg (fun law => law.map readout) htrace
    rw [runtime.candidateRoundDriver.runRounds_eq_tracePolicies principals serviceSlots
      _ wire count initial (by rfl)]
    simpa only [candidateGraphRoundCoupling, FinDist.map_bind, FinDist.map_comp, Function.comp_def]
      using hreadout
  refine ⟨responsePairs, ?_, hnative, ?_⟩
  · simpa only [candidateGraphRoundCoupling, FinDist.map_bind, FinDist.map_comp, Function.comp_def]
      using hgraph
  · intro cfg selected hpair
    have hselected : selected ∈ ((responsePairs.bind fun responses =>
        supported.candidateGraphRoundCoupling hinfo hguards nullValue window principals serviceSlots
          count focal responses.1 responses.2 fallback profile).map Prod.snd).support := by
      rw [FinDist.support_map]
      exact ⟨(cfg, selected), hpair, rfl⟩
    rw [hnative] at hselected
    simp only [FinDist.support_bind, Set.mem_iUnion] at hpair
    obtain ⟨responses, _, hpair⟩ := hpair
    refine ⟨supported.candidateGraphRoundCoupling_terminal hinfo hguards nullValue window principals
      serviceSlots count focal responses.1 responses.2 fallback profile cfg selected hpair, ?_, ?_⟩
    · intro hbound
      exact supported.candidateRuntime_runRounds_complete nullValue window principals serviceSlots
        _ wire count hbound selected hselected
    · exact supported.candidateGraphRoundCoupling_public_store hinfo hguards nullValue window
        principals serviceSlots count focal responses.1 responses.2 fallback profile cfg selected
        hpair

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.exists_randomized_candidate_round_graph_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.exists_randomized_candidate_round_graph_coupling
