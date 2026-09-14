/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedRoundCoupling

/-! # First-timeout information in source/native round couplings

The local history and view at first timeout are retained from the same actual
native trace as the round-driver readout.  They are not reconstructed from the
source realization or from a deterministic response chosen in the mixture.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- A fixed-response source coupling retaining first-timeout local information
and the actual completed-round readout from one common full native trace. -/
def extractedStoppingRoundSourceCoupling
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
    let runtime := compilation.supported.resolvingRuntime nullValue window
    FinDist (ReachableConfig (compile source.core).graph ×
      ((List runtime.messageApplication.PlayerEntry × runtime.messageApplication.View) ×
        runtime.messageApplication.PolicyExecution)) :=
  let runtime := compilation.supported.resolvingRuntime nullValue window
  let schedule := SealedResolution.roundSchedule principals serviceSlots count
  let readout := PolicyTrace.firstReleaseEvery
    (SealedResolution.roundInvocations principals serviceSlots).length
    (fun execution : runtime.messageApplication.PolicyExecution =>
      runtime.complete execution.native.application.visible) count
  (compilation.extractedSourceCoupling nullValue window focal deviator environment schedule
    fallback profile).map fun pair =>
      (pair.1, (SealedResolution.firstTimeoutLocalInfo runtime focal pair.2, readout pair.2))

/-- Forgetting first-timeout local information recovers exactly the existing
round source coupling. -/
theorem extractedStoppingRoundSourceCoupling_erase
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
    (compilation.extractedStoppingRoundSourceCoupling nullValue window principals serviceSlots
      count focal deviator environment fallback profile).map
        (fun pair => (pair.1, pair.2.2)) =
      compilation.extractedRoundSourceCoupling nullValue window principals serviceSlots count
        focal deviator environment fallback profile := by
  simp only [extractedStoppingRoundSourceCoupling, extractedRoundSourceCoupling,
    FinDist.map_comp, Function.comp_def]

/-- A focal registration visible in the actual first-timeout local history is
the corresponding value in the retained complete source realization. -/
theorem extractedStoppingRoundSourceCoupling_locked
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
    (info : List
      (compilation.supported.resolvingRuntime nullValue
        window).messageApplication.PlayerEntry ×
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.View)
    (selected :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hpair : (cfg, (info, selected)) ∈
      (compilation.extractedStoppingRoundSourceCoupling nullValue window principals serviceSlots
        count focal deviator environment fallback profile).support)
    (decision : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hdecision : ((compile source.core).graph.nodeRow decision).sem = .commit focal guard)
    (value : L.Val ty)
    (hcache : (compilation.supported.compile.registrationEncoding decision.val).cachedValue
      (compilation.supported.resolvingRuntime nullValue window).messageApplication info.1 =
        some value) :
    cfg.1.nodeValues fallback decision = value := by
  let runtime := compilation.supported.resolvingRuntime nullValue window
  let schedule := SealedResolution.roundSchedule principals serviceSlots count
  let players := Profile.update (sig := policySignature Player runtime.messageApplication)
    (fun who => compilation.compileResolvingPolicy nullValue window who (profile who)) focal
    (fun history view => FinDist.pure (deviator history view))
  let nativeEnvironment : runtime.messageApplication.EnvironmentPolicy :=
    fun history view => FinDist.pure (environment history view)
  let initial := PolicyExecution.initial runtime.messageApplication
    (State.initial _ runtime.initial)
  let stop : runtime.messageApplication.PolicyExecution → Bool := fun execution =>
    !execution.native.application.visible.timeouts.isEmpty
  simp only [extractedStoppingRoundSourceCoupling, FinDist.support_map,
    Set.mem_image] at hpair
  obtain ⟨⟨sourceCfg, trace⟩, hcoupled, heq⟩ := hpair
  have hcfgEq : sourceCfg = cfg := congrArg Prod.fst heq
  subst sourceCfg
  have hinfoEq : SealedResolution.firstTimeoutLocalInfo runtime focal trace = info :=
    congrArg (fun pair => pair.2.1) heq
  have hsource : cfg ∈ (compilation.extractedSourceRun nullValue window focal deviator
      environment schedule fallback profile).support := by
    rw [← compilation.extractedSourceCoupling_realization nullValue window focal deviator
      environment schedule fallback profile, FinDist.support_map]
    exact ⟨(cfg, trace), hcoupled, rfl⟩
  let replayStopped :=
    (compilation.supported.resolvingReplay nullValue window (cfg.1.nodeValues fallback)
      focal deviator environment schedule).prefixThrough stop
  have hreplayPair : (replayStopped, trace) ∈
      ((compilation.extractedSourceCoupling nullValue window focal deviator environment schedule
        fallback profile).map (fun pair =>
          ((compilation.supported.resolvingReplay nullValue window
            (pair.1.1.nodeValues fallback) focal deviator environment schedule).prefixThrough stop,
            pair.2))).support := by
    rw [FinDist.support_map]
    exact ⟨(cfg, trace), hcoupled, rfl⟩
  rw [compilation.extractedSourceCoupling_prefix_native nullValue window focal deviator
    environment schedule fallback profile] at hreplayPair
  simp only [FinDist.support_map, Set.mem_image] at hreplayPair
  obtain ⟨actual, hactual, heqActual⟩ := hreplayPair
  have hactualEq : actual = trace := congrArg Prod.snd heqActual
  subst actual
  have hstoppedEq : trace.prefixThrough stop = replayStopped :=
    by simpa only [stop] using congrArg Prod.fst heqActual
  obtain ⟨front, suffix, hschedule, hfront⟩ :=
    runtime.messageApplication.tracePolicies_prefixThrough_support players nativeEnvironment
      stop schedule initial trace hactual
  have hrun : (trace.prefixThrough stop).last ∈
      (runtime.messageApplication.runPolicies players nativeEnvironment front initial).support := by
    rw [← runtime.messageApplication.tracePolicies_last, FinDist.support_map]
    exact ⟨trace.prefixThrough stop, hfront, rfl⟩
  have hmemory := SealedResolution.RegistrationMemory.runPolicies players nativeEnvironment
    front initial (trace.prefixThrough stop).last
    SealedResolution.RegistrationMemory.initial hrun
  change (runtime.program.registrationEncoding decision.val).cachedValue
    runtime.messageApplication info.1 = some value at hcache
  rw [← hinfoEq] at hcache
  have hlookupActual :
      (trace.prefixThrough stop).last.native.application.service.lookup
        (focal, decision.val) = some value := by
    rw [hmemory focal decision.val]
    simpa only [SealedResolution.firstTimeoutLocalInfo, stop] using hcache
  have hlookupReplay : replayStopped.last.native.application.service.lookup
      (focal, decision.val) = some value := by
    rw [← hstoppedEq]
    exact hlookupActual
  apply compilation.extractedSourceRun_locked nullValue window focal deviator environment
    schedule fallback profile cfg hsource decision guard hdecision value
  simpa only [replayStopped, EventGraph.SealedFragment.resolvingStop,
    PolicyTrace.prefixThrough_last] using hlookupReplay

/-- A randomized focal replacement and wire policy admit a source coupling
whose native component jointly retains the actual first-timeout local
information and actual round readout. -/
theorem exists_randomized_stopping_round_source_coupling
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
    let readout := PolicyTrace.firstReleaseEvery
      (SealedResolution.roundInvocations principals serviceSlots).length
      (fun execution : runtime.messageApplication.PolicyExecution =>
        runtime.complete execution.native.application.visible) count
    let PlayerResponse := List runtime.messageApplication.PlayerEntry →
      runtime.messageApplication.View → runtime.messageApplication.PlayerCommand
    let EnvironmentResponse := List runtime.messageApplication.EnvironmentEntry →
      runtime.messageApplication.EnvironmentObservation →
        runtime.messageApplication.EnvironmentPolicyCommand
    ∃ responsePairs : FinDist (PlayerResponse × EnvironmentResponse),
      let coupling := responsePairs.bind fun responses =>
        compilation.extractedStoppingRoundSourceCoupling nullValue window principals
          serviceSlots count focal responses.1 responses.2 fallback profile
      coupling.map (fun pair => observeSourceOutcome source.core pair.1) =
        responsePairs.bind (fun responses =>
          (denoteSource source.core.prog
            (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
              (compilation.extractedSourcePolicy nullValue window focal responses.1 responses.2
                schedule fallback)) source.core.env).map some) ∧
      coupling.map Prod.snd =
        (runtime.messageApplication.tracePolicies
          (Profile.update (sig := policySignature Player runtime.messageApplication)
            players focal replacement)
          (runtime.roundEnvironment serviceSlots wire) schedule initial).map
            (fun trace =>
              (SealedResolution.firstTimeoutLocalInfo runtime focal trace, readout trace)) ∧
      coupling.map (fun pair => pair.2.2) =
        runtime.roundDriver.runRounds principals serviceSlots
          (Profile.update (sig := policySignature Player runtime.messageApplication)
            players focal replacement) wire count initial := by
  intro runtime players schedule initial readout PlayerResponse EnvironmentResponse
  obtain ⟨responsePairs, _hprefix, hsource, htrace⟩ :=
    compilation.exists_randomized_source_coupling nullValue window focal
      (runtime.roundEnvironment serviceSlots wire) schedule fallback profile replacement
  refine ⟨responsePairs, ?_, ?_, ?_⟩
  · simpa only [extractedStoppingRoundSourceCoupling, FinDist.map_bind,
      FinDist.map_comp, Function.comp_def] using hsource
  · have h := congrArg (FinDist.map fun trace : runtime.messageApplication.PolicyTrace =>
      (SealedResolution.firstTimeoutLocalInfo runtime focal trace, readout trace)) htrace
    rw [FinDist.map_bind] at h
    simpa only [extractedStoppingRoundSourceCoupling, FinDist.map_bind,
      FinDist.map_comp, Function.comp_def] using h
  · have hreadout := congrArg (FinDist.map readout) htrace
    rw [FinDist.map_bind] at hreadout
    have hdriver := runtime.runRounds_eq_tracePolicies principals serviceSlots
      (Profile.update (sig := policySignature Player runtime.messageApplication)
        players focal replacement) wire count initial (by rfl)
    rw [hdriver]
    simpa only [extractedStoppingRoundSourceCoupling, FinDist.map_bind,
      FinDist.map_comp, Function.comp_def] using hreadout

/-- Every source component retained alongside stopping information is a
terminal realization. -/
theorem mixtureStoppingRoundSourceCoupling_terminal
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
    (info : List
      (compilation.supported.resolvingRuntime nullValue
        window).messageApplication.PlayerEntry ×
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.View)
    (selected :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hpair : (cfg, (info, selected)) ∈ (responsePairs.bind fun responses =>
      compilation.extractedStoppingRoundSourceCoupling nullValue window principals serviceSlots
        count focal responses.1 responses.2 fallback profile).support) :
    Terminal (compile source.core).graph cfg.1 := by
  simp only [FinDist.support_bind, Set.mem_iUnion] at hpair
  obtain ⟨responses, _, hpair⟩ := hpair
  apply compilation.extractedRoundSourceCoupling_terminal nullValue window principals
    serviceSlots count focal responses.1 responses.2 fallback profile cfg selected
  rw [← compilation.extractedStoppingRoundSourceCoupling_erase nullValue window principals
    serviceSlots count focal responses.1 responses.2 fallback profile,
    FinDist.support_map]
  exact ⟨(cfg, (info, selected)), hpair, rfl⟩

/-- Normal timeout-free stopping pairs decode to their retained source
realization; retaining local information does not alter the existing theorem. -/
theorem mixtureStoppingRoundSourceCoupling_decode_of_complete_clear
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
    (info : List
      (compilation.supported.resolvingRuntime nullValue
        window).messageApplication.PlayerEntry ×
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.View)
    (selected :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hpair : (cfg, (info, selected)) ∈ (responsePairs.bind fun responses =>
      compilation.extractedStoppingRoundSourceCoupling nullValue window principals serviceSlots
        count focal responses.1 responses.2 fallback profile).support)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      selected.native.application.visible = true)
    (hclear : selected.native.application.visible.timeouts = []) :
    (compile source.core).graph.decodeSealedFrom ty selected.native.application.service
      (Config.initial _) selected.native.application.visible.events = some cfg.1 := by
  simp only [FinDist.support_bind, Set.mem_iUnion] at hpair
  obtain ⟨responses, hresponses, hpair⟩ := hpair
  apply compilation.mixtureRoundSourceCoupling_decode_of_complete_clear nullValue window
    principals serviceSlots count focal fallback profile responsePairs cfg selected ?_
      hcomplete hclear
  simp only [FinDist.support_bind, Set.mem_iUnion]
  refine ⟨responses, hresponses, ?_⟩
  rw [← compilation.extractedStoppingRoundSourceCoupling_erase nullValue window principals
    serviceSlots count focal responses.1 responses.2 fallback profile,
    FinDist.support_map]
  exact ⟨(cfg, (info, selected)), hpair, rfl⟩

end Vegas.SealedCompilation
