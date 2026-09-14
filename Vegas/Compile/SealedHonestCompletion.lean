/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SourceCorrespondence
import Vegas.Compile.SealedAssignedReplay
import Vegas.Compile.SealedSourceInputs
import Interaction.SealedResolutionDriver

/-! # Complete all-assigned executions decode their source realization

An all-assigned resolving run registers exactly the values of its graph
assignment.  Consequently, any timeout-free completed snapshot of that run
decodes to the same terminal reachable configuration.  The round-boundary
corollary applies this fact at the first completed boundary selected by the
ordinary round driver.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Any normally completed, timeout-free snapshot supported by the
all-assigned policies decodes to the terminal assignment supplying those
policies. The environment policy and invocation schedule are arbitrary. -/
theorem runPolicies_resolvingAssigned_decode_of_complete_clear
    (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (cfg : ReachableConfig G) (hterminal : Terminal G cfg.1) (fallback : L.Val ty)
    (environment :
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player))
    (selected :
      (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hselected : selected ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.runPolicies
        (supported.resolvingAssignedPlayers nullValue window (cfg.1.nodeValues fallback))
        environment schedule
        (PolicyExecution.initial _
          (State.initial _ (supported.resolvingRuntime nullValue window).initial))).support)
    (hcomplete : (supported.resolvingRuntime nullValue window).complete
      selected.native.application.visible = true)
    (hclear : selected.native.application.visible.timeouts = []) :
    G.decodeSealedFrom ty selected.native.application.service (Config.initial G)
      selected.native.application.visible.events = some cfg.1 := by
  let runtime := supported.resolvingRuntime nullValue window
  have hbinding := runtime.runPolicies_beforeTimeoutBinding
    (supported.resolvingAssignedPlayers nullValue window (cfg.1.nodeValues fallback))
    environment schedule _ selected SealedResolution.BeforeTimeoutBinding.initial hselected
  change G.decodeSealed ty
      ⟨selected.native.application.service, MessagePool.empty Player _,
        selected.native.application.visible.events⟩ = some cfg.1
  apply supported.decodeSealed_eq_source cfg hterminal fallback _ (hbinding hclear) ?_ ?_
  · intro owner node guard hnode value hlookup
    exact (supported.runPolicies_resolvingAssigned_lookup nullValue window
      (cfg.1.nodeValues fallback) environment schedule selected hselected owner node value
      hlookup).1.symm
  · intro node
    have hindex : node.val < runtime.program.rules.length := by
      change node.val < supported.compile.rules.length
      simp [SealedFragment.compile, Graph.nodeOrder]
    have hdone := List.all_eq_true.mp hcomplete node.val (List.mem_range.mpr hindex)
    simpa only [SealedResolution.PublicState.completed, hclear, List.contains_nil,
      Bool.or_false] using hdone

/-- The first completed round boundary of an all-assigned replay decodes to
the assignment that generated it, provided that selected boundary is a normal
completion rather than a timeout. -/
theorem resolvingAssignedReplay_firstCompleteEvery_decode
    (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots count : Nat)
    (cfg : ReachableConfig G) (hterminal : Terminal G cfg.1) (fallback : L.Val ty)
    (environment :
      List (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentEntry →
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentObservation →
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicyCommand)
    (selected :
      (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hselected : selected =
      ((supported.resolvingAssignedReplay nullValue window (cfg.1.nodeValues fallback)
        environment
          (SealedResolution.roundSchedule principals serviceSlots count)).firstReleaseEvery
          (SealedResolution.roundInvocations principals serviceSlots).length
          (fun execution :
              (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution =>
            (supported.resolvingRuntime nullValue window).complete
            execution.native.application.visible) count))
    (hcomplete : (supported.resolvingRuntime nullValue window).complete
      selected.native.application.visible = true)
    (hclear : selected.native.application.visible.timeouts = []) :
    G.decodeSealedFrom ty selected.native.application.service (Config.initial G)
      selected.native.application.visible.events = some cfg.1 := by
  let runtime := supported.resolvingRuntime nullValue window
  let players := supported.resolvingAssignedPlayers nullValue window
    (cfg.1.nodeValues fallback)
  let nativeEnvironment : runtime.messageApplication.EnvironmentPolicy :=
    fun history view => FinDist.pure (environment history view)
  let schedule := SealedResolution.roundSchedule principals serviceSlots count
  let width := (SealedResolution.roundInvocations principals serviceSlots).length
  let release := fun execution : runtime.messageApplication.PolicyExecution =>
    runtime.complete execution.native.application.visible
  let initial := PolicyExecution.initial runtime.messageApplication
    (State.initial _ runtime.initial)
  let trace := supported.resolvingAssignedReplay nullValue window
    (cfg.1.nodeValues fallback) environment schedule
  have htrace : trace ∈
      (runtime.messageApplication.tracePolicies players nativeEnvironment schedule
        initial).support := by
    rw [supported.resolvingAssignedReplay_law, FinDist.mem_support_pure]
  obtain ⟨front, _suffix, _hschedule, hfront, _hsuffix⟩ :=
    runtime.messageApplication.tracePolicies_firstReleaseEvery_split players nativeEnvironment
      width count release (by simp [width, SealedResolution.roundInvocations]) schedule initial
      trace (by simp [schedule, width, SealedResolution.roundSchedule_length]) htrace
  have hselectedRun : selected ∈
      (runtime.messageApplication.runPolicies players nativeEnvironment front initial).support := by
    rw [hselected]
    exact hfront
  exact supported.runPolicies_resolvingAssigned_decode_of_complete_clear nullValue window cfg
    hterminal fallback nativeEnvironment front selected hselectedRun hcomplete hclear

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.resolvingAssignedReplay_firstCompleteEvery_decode'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.resolvingAssignedReplay_firstCompleteEvery_decode
