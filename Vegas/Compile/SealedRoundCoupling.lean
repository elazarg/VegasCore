/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionDriver
import Interaction.SealedResolutionCompletion
import Vegas.Compile.SealedRandomizedCoupling
import Vegas.Compile.SealedTermination

/-! # Source coupling for the sealed round driver

The full-trace source coupling can be read at the first completed round
boundary. Predrawing a randomized focal replacement and the periodic round
environment then gives an explicit finite mixture whose native marginal is
the actual round driver. The source marginal remains a mixture of legal
written-source deviations against unchanged opponents.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Read the retained complete native trace at the first completed round
boundary, or at the final requested boundary if completion has not occurred. -/
def extractedRoundSourceCoupling
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots count : Nat) (focal : Player)
    (deviator :
      List
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.PlayerEntry →
        (compilation.supported.resolvingRuntime nullValue window).messageApplication.View →
        (compilation.supported.resolvingRuntime nullValue
          window).messageApplication.PlayerCommand)
    (environment :
      List
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.EnvironmentEntry →
        (compilation.supported.resolvingRuntime nullValue
          window).messageApplication.EnvironmentObservation →
        (compilation.supported.resolvingRuntime nullValue
          window).messageApplication.EnvironmentPolicyCommand)
    (fallback : L.Val ty) (profile : SourceBehavioralProfile source.core.prog) :
    FinDist (ReachableConfig (compile source.core).graph ×
      (compilation.supported.resolvingRuntime nullValue
        window).messageApplication.PolicyExecution) :=
  let runtime := compilation.supported.resolvingRuntime nullValue window
  let schedule := SealedResolution.roundSchedule principals serviceSlots count
  let readout := PolicyTrace.firstReleaseEvery
    (SealedResolution.roundInvocations principals serviceSlots).length
    (fun execution : runtime.messageApplication.PolicyExecution =>
      runtime.complete execution.native.application.visible) count
  (compilation.extractedSourceCoupling nullValue window focal deviator environment schedule
    fallback profile).map fun pair => (pair.1, readout pair.2)

/-- Every source configuration retained by a round-readout coupling is a
terminal realization of the compiled source graph.  Selecting an earlier
native round boundary does not alter that source component. -/
theorem extractedRoundSourceCoupling_terminal
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots count : Nat) (focal : Player)
    (deviator :
      List
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.PlayerEntry →
        (compilation.supported.resolvingRuntime nullValue window).messageApplication.View →
        (compilation.supported.resolvingRuntime nullValue
          window).messageApplication.PlayerCommand)
    (environment :
      List
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.EnvironmentEntry →
        (compilation.supported.resolvingRuntime nullValue
          window).messageApplication.EnvironmentObservation →
        (compilation.supported.resolvingRuntime nullValue
          window).messageApplication.EnvironmentPolicyCommand)
    (fallback : L.Val ty) (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (selected :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hpair : (cfg, selected) ∈
      (compilation.extractedRoundSourceCoupling nullValue window principals serviceSlots count
        focal deviator environment fallback profile).support) :
    Terminal (compile source.core).graph cfg.1 := by
  let schedule := SealedResolution.roundSchedule principals serviceSlots count
  simp only [extractedRoundSourceCoupling, FinDist.support_map, Set.mem_image] at hpair
  obtain ⟨⟨sourceCfg, trace⟩, hsource, heq⟩ := hpair
  have hcfgEq : sourceCfg = cfg := congrArg Prod.fst heq
  subst sourceCfg
  have hcfg : cfg ∈
      ((compilation.extractedSourceCoupling nullValue window focal deviator environment schedule
        fallback profile).map Prod.fst).support := by
    rw [FinDist.support_map]
    exact ⟨(cfg, trace), hsource, rfl⟩
  rw [compilation.extractedSourceCoupling_realization] at hcfg
  exact compilation.extractedSourceRun_terminal nullValue window focal deviator environment
    schedule fallback profile cfg hcfg

/-- A normally completed timeout-free round readout decodes to the retained
source realization. The full trace may contain later traffic, so the proof
uses the supported continuation from the selected boundary and persistence of
both public completion and occupied private registrations. -/
private theorem extractedRoundSourceCoupling_decode_of_complete_clear
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots count : Nat) (focal : Player)
    (deviator :
      List
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.PlayerEntry →
        (compilation.supported.resolvingRuntime nullValue window).messageApplication.View →
        (compilation.supported.resolvingRuntime nullValue
          window).messageApplication.PlayerCommand)
    (environment :
      List
          (compilation.supported.resolvingRuntime nullValue
            window).messageApplication.EnvironmentEntry →
        (compilation.supported.resolvingRuntime nullValue
          window).messageApplication.EnvironmentObservation →
        (compilation.supported.resolvingRuntime nullValue
          window).messageApplication.EnvironmentPolicyCommand)
    (fallback : L.Val ty) (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (selected :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hpair : (cfg, selected) ∈
      (compilation.extractedRoundSourceCoupling nullValue window principals serviceSlots count
        focal deviator environment fallback profile).support)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      selected.native.application.visible = true)
    (hclear : selected.native.application.visible.timeouts = []) :
    (compile source.core).graph.decodeSealedFrom ty selected.native.application.service
      (Config.initial _) selected.native.application.visible.events = some cfg.1 := by
  let runtime := compilation.supported.resolvingRuntime nullValue window
  let players := Profile.update (sig := policySignature Player runtime.messageApplication)
    (fun who => compilation.compileResolvingPolicy nullValue window who (profile who)) focal
    (fun history view => FinDist.pure (deviator history view))
  let nativeEnvironment : runtime.messageApplication.EnvironmentPolicy :=
    fun history view => FinDist.pure (environment history view)
  let schedule := SealedResolution.roundSchedule principals serviceSlots count
  let width := (SealedResolution.roundInvocations principals serviceSlots).length
  let release := fun execution : runtime.messageApplication.PolicyExecution =>
    runtime.complete execution.native.application.visible
  let initial := PolicyExecution.initial runtime.messageApplication
    (State.initial _ runtime.initial)
  simp only [extractedRoundSourceCoupling, FinDist.support_map, Set.mem_image] at hpair
  obtain ⟨⟨sourceCfg, trace⟩, hpair, heq⟩ := hpair
  have hcfgEq : sourceCfg = cfg := congrArg Prod.fst heq
  have hselectedEq :
      trace.firstReleaseEvery width release count = selected := congrArg Prod.snd heq
  subst sourceCfg
  have hnative : trace ∈
      (runtime.messageApplication.tracePolicies players nativeEnvironment schedule
        initial).support := by
    have hmap : trace ∈
        ((compilation.extractedSourceCoupling nullValue window focal deviator environment
          schedule fallback profile).map Prod.snd).support := by
      rw [FinDist.support_map]
      exact ⟨(cfg, trace), hpair, rfl⟩
    rw [compilation.extractedSourceCoupling_native] at hmap
    exact hmap
  obtain ⟨front, suffix, _hschedule, hselected, hsuffix⟩ :=
    runtime.messageApplication.tracePolicies_firstReleaseEvery_split
      players nativeEnvironment width count release (by
        simp [width, SealedResolution.roundInvocations]) schedule initial trace (by
          simp [schedule, width, SealedResolution.roundSchedule_length]) hnative
  rw [hselectedEq] at hselected hsuffix
  obtain ⟨_hevents, hfinalClear, _hfinalComplete⟩ :=
    runtime.runPolicies_complete_clear players nativeEnvironment suffix
      selected trace.last hcomplete hclear hsuffix
  obtain ⟨hcfg, _htrace, hstop⟩ :=
    compilation.extractedSourceCoupling_clear nullValue window focal deviator environment
      schedule fallback profile cfg trace hpair hfinalClear
  have hbindingBefore := runtime.runPolicies_beforeTimeoutBinding players nativeEnvironment
    front initial selected
      SealedResolution.BeforeTimeoutBinding.initial hselected
  change (compile source.core).graph.decodeSealed ty
      ⟨selected.native.application.service, MessagePool.empty Player _,
        selected.native.application.visible.events⟩ = some cfg.1
  apply compilation.supported.decodeSealed_eq_source cfg
    (compilation.extractedSourceRun_terminal nullValue window focal deviator environment
      schedule fallback profile cfg hcfg) fallback _ (hbindingBefore hclear) ?_ ?_
  · intro owner node guard hnode value hlookup
    have hfinalLookup := runtime.runPolicies_lookup_of_eq_some players nativeEnvironment suffix
      selected trace.last (owner, node.val) value hlookup hsuffix
    rw [hstop] at hfinalLookup
    exact compilation.extractedSourceRun_registered nullValue window focal deviator environment
      schedule fallback profile cfg hcfg owner node guard hnode value hfinalLookup
  · intro node
    have hindex : node.val < runtime.program.rules.length := by
      change node.val < compilation.program.rules.length
      rw [compilation.program_rule_count]
      exact node.isLt
    have hdone := List.all_eq_true.mp hcomplete node.val (List.mem_range.mpr hindex)
    simpa only [SealedResolution.PublicState.completed, hclear, List.contains_nil,
      Bool.or_false] using hdone

/-- A randomized focal replacement and wire policy induce an explicit mixture
of round-readout source couplings. Its source marginal is the corresponding
mixture of written-source deviations, while its native marginal is exactly the
actual resolving round driver from the canonical initial state. -/
theorem exists_randomized_round_source_coupling
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots count : Nat) (focal : Player)
    (fallback : L.Val ty) (profile : SourceBehavioralProfile source.core.prog)
    (replacement :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (wire :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.WirePolicy) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let players := fun who =>
      compilation.compileResolvingPolicy nullValue window who (profile who)
    let schedule := SealedResolution.roundSchedule principals serviceSlots count
    let initial := PolicyExecution.initial runtime.messageApplication
      (State.initial _ runtime.initial)
    let PlayerResponse := List runtime.messageApplication.PlayerEntry →
      runtime.messageApplication.View → runtime.messageApplication.PlayerCommand
    let EnvironmentResponse := List runtime.messageApplication.EnvironmentEntry →
      runtime.messageApplication.EnvironmentObservation →
        runtime.messageApplication.EnvironmentPolicyCommand
    ∃ responsePairs : FinDist (PlayerResponse × EnvironmentResponse),
      ((responsePairs.bind fun responses =>
        compilation.extractedRoundSourceCoupling nullValue window principals serviceSlots count
          focal responses.1 responses.2 fallback profile).map
            (fun pair => observeSourceOutcome source.core pair.1)) =
        responsePairs.bind (fun responses =>
          (denoteSource source.core.prog
            (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
              (compilation.extractedSourcePolicy nullValue window focal responses.1 responses.2
                schedule fallback)) source.core.env).map some) ∧
      ((responsePairs.bind fun responses =>
        compilation.extractedRoundSourceCoupling nullValue window principals serviceSlots count
          focal responses.1 responses.2 fallback profile).map Prod.snd) =
        runtime.runRounds principals serviceSlots
          (Profile.update (sig := policySignature Player runtime.messageApplication)
            players focal replacement) wire count initial := by
  intro runtime players schedule initial PlayerResponse EnvironmentResponse
  obtain ⟨responsePairs, _, hsource, htrace⟩ :=
    compilation.exists_randomized_source_coupling nullValue window focal
      (runtime.roundEnvironment serviceSlots wire) schedule fallback profile replacement
  refine ⟨responsePairs, ?_, ?_⟩
  · simpa only [extractedRoundSourceCoupling, FinDist.map_bind, FinDist.map_comp,
      Function.comp_def] using hsource
  · let readout := PolicyTrace.firstReleaseEvery
      (SealedResolution.roundInvocations principals serviceSlots).length
      (fun execution : runtime.messageApplication.PolicyExecution =>
        runtime.complete execution.native.application.visible) count
    have hreadout := congrArg (fun law => law.map readout) htrace
    rw [FinDist.map_bind] at hreadout
    have hdriver := runtime.runRounds_eq_tracePolicies principals serviceSlots
      (Profile.update (sig := policySignature Player runtime.messageApplication)
        players focal replacement) wire count initial (by rfl)
    rw [hdriver]
    simpa only [extractedRoundSourceCoupling, FinDist.map_bind, FinDist.map_comp,
      Function.comp_def] using hreadout

/-- Every pair supported by a finite mixture of the explicit round-readout
couplings retains a terminal compiled source configuration. -/
theorem mixtureRoundSourceCoupling_terminal
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots count : Nat) (focal : Player)
    (fallback : L.Val ty) (profile : SourceBehavioralProfile source.core.prog)
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
    (selected :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hpair : (cfg, selected) ∈ (responsePairs.bind fun responses ↦
      compilation.extractedRoundSourceCoupling nullValue window principals serviceSlots count
        focal responses.1 responses.2 fallback profile).support) :
    Terminal (compile source.core).graph cfg.1 := by
  simp only [FinDist.support_bind, Set.mem_iUnion] at hpair
  obtain ⟨responses, _, hpair⟩ := hpair
  exact compilation.extractedRoundSourceCoupling_terminal nullValue window principals
    serviceSlots count focal responses.1 responses.2 fallback profile cfg selected hpair

/-- Every normally completed timeout-free pair in a mixture of the explicit
round-readout couplings decodes to its retained source realization. This
applies directly to the response mixture constructed for randomized focal and
wire policies. -/
theorem mixtureRoundSourceCoupling_decode_of_complete_clear
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots count : Nat) (focal : Player)
    (fallback : L.Val ty) (profile : SourceBehavioralProfile source.core.prog)
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
    (selected :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hpair : (cfg, selected) ∈ (responsePairs.bind fun responses =>
      compilation.extractedRoundSourceCoupling nullValue window principals serviceSlots count
        focal responses.1 responses.2 fallback profile).support)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      selected.native.application.visible = true)
    (hclear : selected.native.application.visible.timeouts = []) :
    (compile source.core).graph.decodeSealedFrom ty selected.native.application.service
      (Config.initial _) selected.native.application.visible.events = some cfg.1 := by
  simp only [FinDist.support_bind, Set.mem_iUnion] at hpair
  obtain ⟨responses, _, hpair⟩ := hpair
  exact compilation.extractedRoundSourceCoupling_decode_of_complete_clear nullValue window
    principals serviceSlots count focal responses.1 responses.2 fallback profile cfg selected
      hpair hcomplete hclear

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.exists_randomized_round_source_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.exists_randomized_round_source_coupling

/-- info: 'Vegas.SealedCompilation.mixtureRoundSourceCoupling_decode_of_complete_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.mixtureRoundSourceCoupling_decode_of_complete_clear

/-- info: 'Vegas.SealedCompilation.mixtureRoundSourceCoupling_terminal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.mixtureRoundSourceCoupling_terminal
