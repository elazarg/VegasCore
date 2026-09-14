/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedHonestCylinder

/-! # All-player source likelihood of an assigned native replay -/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (compilation : SealedCompilation source ty)

/-- The original source kernel's probability of an occupied registration in
the all-assigned replay. Unoccupied source slots contribute one. -/
def assignedRegistrationFactor
    (nullValue : L.Val ty) (window : Nat)
    (environment :
      List
        (MessageApplication.EnvironmentEntry
          (compilation.supported.resolvingRuntime nullValue window).messageApplication) →
      MessageApplication.EnvironmentObservation
        (compilation.supported.resolvingRuntime nullValue window).messageApplication →
      MessageApplication.EnvironmentPolicyCommand
        (compilation.supported.resolvingRuntime nullValue window).messageApplication)
    (schedule : List (@Invocation Player))
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player) (slot : Nat) : ℝ :=
  let runtime := compilation.supported.resolvingRuntime nullValue window
  let trace := compilation.supported.resolvingAssignedReplay nullValue window reference
    environment schedule
  let stop := fun execution : runtime.messageApplication.PolicyExecution =>
    !execution.native.application.visible.timeouts.isEmpty
  match (trace.prefixThrough stop).last.native.application.service.lookup (who, slot) with
  | none => 1
  | some value =>
      let selected := runtime.messageApplication.commandCheckpoint
        (compilation.supported.resolvingAssignedPlayers nullValue window reference) trace stop
        who (.privateCommand ⟨(slot, value)⟩)
      (compilation.compileResolvingPolicy nullValue window who (profile who)
        (selected.principalHistory who)
        (State.observe runtime.messageApplication selected.native who)).prob
          (.privateCommand ⟨(slot, value)⟩)

/-- At a selected pre-timeout registration checkpoint, the compiled original
kernel has exactly the corresponding written-source decision probability. -/
theorem assignedReplay_registration_probability
    (nullValue : L.Val ty) (window : Nat)
    (environment :
      List
        (MessageApplication.EnvironmentEntry
          (compilation.supported.resolvingRuntime nullValue window).messageApplication) →
      MessageApplication.EnvironmentObservation
        (compilation.supported.resolvingRuntime nullValue window).messageApplication →
      MessageApplication.EnvironmentPolicyCommand
        (compilation.supported.resolvingRuntime nullValue window).messageApplication)
    (schedule : List (@Invocation Player)) (fallback : L.Val ty)
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog)
    (release :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
        Bool) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let tracePrefix := (compilation.supported.resolvingAssignedReplay nullValue window reference
      environment schedule).prefixThrough
        (fun execution : runtime.messageApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)
    ∀ cfg ∈ (source.sourceRealization
      ((compilation.recordedChoiceRestriction (fun _ => true)
        tracePrefix.last.native.application.service.lookup).apply profile)).support,
    let stopped := tracePrefix.firstRelease release
    stopped.native.application.visible.timeouts = [] →
    ∀ who slot value,
      .privateCommand ⟨(slot, value)⟩ ∈
        (compilation.supported.resolvingAssignedPlayers nullValue window reference who
          (stopped.principalHistory who)
          (State.observe runtime.messageApplication stopped.native who)).support →
    ∀ policy : SourceBehavioralPolicy source.core.prog who,
    ∃ final, observeSourceOutcome source.core cfg = some final ∧
      ∃ Δ name choiceTy guard, ∃ site :
        SourceDecisionSite who source.core.prog Δ name choiceTy guard,
        site.depth = slot ∧ ∀ chosen,
          (compilation.compileResolvingPolicy nullValue window who policy
            (stopped.principalHistory who)
            (State.observe runtime.messageApplication stopped.native who)).prob
              (.privateCommand ⟨(slot, chosen)⟩) =
            ((policy site ((site.recorded final).tail.toView who).eraseEnv).map
              (fun choice => (⟨choiceTy, choice.1⟩ : TypedValue L))).prob ⟨ty, chosen⟩ := by
  intro runtime tracePrefix cfg hcfg stopped hclear who slot value hcommand policy
  let players := compilation.supported.resolvingAssignedPlayers nullValue window reference
  let env := fun history view => FinDist.pure (environment history view)
  let initial := PolicyExecution.initial runtime.messageApplication
    (State.initial runtime.messageApplication runtime.initial)
  let stop := fun execution : runtime.messageApplication.PolicyExecution =>
    !execution.native.application.visible.timeouts.isEmpty
  let trace := compilation.supported.resolvingAssignedReplay nullValue window reference
    environment schedule
  have htrace : trace ∈
      (runtime.messageApplication.tracePolicies players env schedule initial).support := by
    rw [compilation.supported.resolvingAssignedReplay_law, FinDist.mem_support_pure]
  obtain ⟨front, _, _, hprefix⟩ :=
    runtime.messageApplication.tracePolicies_prefixThrough_support players env stop schedule
      initial trace htrace
  obtain ⟨before, after, _, hbefore, hafter⟩ :=
    runtime.messageApplication.tracePolicies_firstRelease_split players env release front initial
      tracePrefix hprefix
  have hterminal := source.sourceRealization_terminal _ cfg hcfg
  have hmemory := SealedResolution.RegistrationMemory.runPolicies players env before initial stopped
    SealedResolution.RegistrationMemory.initial hbefore
  have hbinding := runtime.runPolicies_beforeTimeoutBinding players env before initial stopped
    SealedResolution.BeforeTimeoutBinding.initial hbefore hclear
  have hvalues : ∀ owner (node : Fin (compile source.core).graph.nodeCount) guard,
      ((compile source.core).graph.nodeRow node).sem = .commit owner guard → ∀ registered,
      stopped.native.application.service.lookup (owner, node.val) = some registered →
        cfg.1.nodeValues fallback node = registered := by
    intro owner node guard hsem registered hlookup
    apply compilation.sourceRealization_registered (fun _ => true)
      tracePrefix.last.native.application.service profile fallback cfg hcfg owner rfl
      node guard hsem registered
    exact runtime.runPolicies_lookup_of_eq_some players env after stopped tracePrefix.last
      (owner, node.val) registered hlookup hafter
  exact compilation.registration_source_probability nullValue window fallback cfg hterminal
    stopped hclear hmemory (hbinding.copy rfl rfl) hvalues who
    (compilation.supported.valuePolicy reference who) policy slot value hcommand

omit [Fintype Player] in
/-- The all-owner restriction weight is constant on its normalized source law,
with one factor for every written source decision. -/
theorem assignedRestriction_weight_eq_product
    [Finite Player]
    (nullValue : L.Val ty) (window : Nat)
    (environment :
      List (MessageApplication.EnvironmentEntry
        (compilation.supported.resolvingRuntime nullValue window).messageApplication) →
      MessageApplication.EnvironmentObservation
        (compilation.supported.resolvingRuntime nullValue window).messageApplication →
      MessageApplication.EnvironmentPolicyCommand
        (compilation.supported.resolvingRuntime nullValue window).messageApplication)
    (schedule : List (@Invocation Player))
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let stopped := (compilation.supported.resolvingAssignedReplay nullValue window reference
      environment schedule).prefixThrough
        (fun execution : runtime.messageApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)
    let restriction := compilation.recordedChoiceRestriction (fun _ => true)
      stopped.last.native.application.service.lookup
    ∀ final ∈ (denoteSource source.core.prog (restriction.apply profile)
      source.core.env).support,
      restriction.weight profile source.core.env final =
        (source.core.prog.decisionPositions.map fun slot =>
          compilation.assignedRegistrationFactor nullValue window environment schedule
            reference profile slot.1 slot.2).prod := by
  classical
  let : Fintype Player := Fintype.ofFinite Player
  intro runtime stopped restriction final hfinal
  have hsource := source.sourceRealization_source (restriction.apply profile)
  have hsome : some final ∈
      ((denoteSource source.core.prog (restriction.apply profile) source.core.env).map
        some).support := by
    rw [FinDist.support_map]
    exact ⟨final, hfinal, rfl⟩
  rw [← hsource, FinDist.support_map] at hsome
  obtain ⟨cfg, hcfg, hobserve⟩ := hsome
  apply SourceChoiceRestriction.weight_eq_decision_product source.core.prog profile
    (restriction.apply profile) restriction source.core.env final hfinal
  intro who Δ name choiceTy guard site
  dsimp only
  cases hlookup : stopped.last.native.application.service.lookup (who, site.depth) with
  | none =>
      constructor
      · intro _
        simp only [assignedRegistrationFactor]
        erw [hlookup]
      · intro fixed hfixed
        simp only [restriction, recordedChoiceRestriction, ↓reduceIte, hlookup,
          Option.map_none] at hfixed
        cases hfixed
  | some value =>
      constructor
      · intro hnone
        simp only [restriction, recordedChoiceRestriction, ↓reduceIte, hlookup,
          Option.map_some] at hnone
        cases hnone
      · intro fixed hfixed
        have hvalue := compilation.recordedChoiceRestriction_fixed_value (fun _ => true)
          stopped.last.native.application.service.lookup who rfl site _ value hlookup fixed hfixed
        let trace := compilation.supported.resolvingAssignedReplay nullValue window reference
          environment schedule
        let stop := fun execution : runtime.messageApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty
        let players := compilation.supported.resolvingAssignedPlayers nullValue window reference
        let release := fun execution : runtime.messageApplication.PolicyExecution =>
          !stop execution && decide (.privateCommand ⟨(site.depth, value)⟩ ∈
            (players who (execution.principalHistory who)
              (State.observe runtime.messageApplication execution.native who)).support)
        have htrace : trace ∈ (runtime.messageApplication.tracePolicies players
            (fun history view => FinDist.pure (environment history view)) schedule
            (PolicyExecution.initial _ (State.initial _ runtime.initial))).support := by
          rw [compilation.supported.resolvingAssignedReplay_law, FinDist.mem_support_pure]
        have hselected := runtime.registrationCheckpoint_selected players
          (fun history view => FinDist.pure (environment history view)) schedule _ trace
          htrace stop who site.depth value (by intro h; cases h) hlookup
        have hclear :
            (stopped.firstRelease release).native.application.visible.timeouts = [] := by
          simpa only [MessageApplication.commandCheckpoint, stop,
            Bool.not_eq_eq_eq_not, Bool.not_false, List.isEmpty_iff] using hselected.1
        obtain ⟨outcome, houtcome, ctx, label, actionTy, sourceGuard, actual, hdepth, hprob⟩ :=
          compilation.assignedReplay_registration_probability nullValue window environment
            schedule nullValue reference profile release cfg hcfg hclear who site.depth value
            hselected.2 (profile who)
        have heq : outcome = final := Option.some.inj (houtcome.symm.trans hobserve)
        subst outcome
        obtain ⟨rfl, rfl, rfl, hguard, hsite⟩ :=
          actual.indices_eq_of_depth_eq site hdepth
        cases eq_of_heq hguard
        cases eq_of_heq hsite
        have hmass :
            ((profile who actual ((actual.recorded final).tail.toView who).eraseEnv).map
              (fun choice => (⟨actionTy, choice.1⟩ : TypedValue L))).prob
                ⟨actionTy, fixed.1⟩ =
            ((profile who actual ((actual.recorded final).tail.toView who).eraseEnv).map
              Subtype.val).prob fixed.1 := by
          rw [FinDist.prob_map_eq_probOf_preimage_singleton,
            FinDist.prob_map_eq_probOf_preimage_singleton]
          apply FinDist.probOf_congr
          intro choice _
          simp only [Set.mem_preimage, Set.mem_singleton_iff, TypedValue.mk.injEq,
            heq_eq_eq, true_and]
        have hnative := hprob value
        rw [← hvalue] at hnative
        have hfactor := hnative.trans hmass
        simp only [assignedRegistrationFactor]
        erw [hlookup]
        exact hfactor

/-- The original written-source probability of the all-assigned replay prefix
through first timeout is the product of its original registration factors. -/
theorem sourceRealization_replay_prob_eq_product
    (nullValue : L.Val ty) (window : Nat)
    (environment :
      List (MessageApplication.EnvironmentEntry
        (compilation.supported.resolvingRuntime nullValue window).messageApplication) →
      MessageApplication.EnvironmentObservation
        (compilation.supported.resolvingRuntime nullValue window).messageApplication →
      MessageApplication.EnvironmentPolicyCommand
        (compilation.supported.resolvingRuntime nullValue window).messageApplication)
    (schedule : List (@Invocation Player)) (fallback : L.Val ty)
    (reference : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (profile : SourceBehavioralProfile source.core.prog) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let stop := fun execution : runtime.messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let stopped := (compilation.supported.resolvingAssignedReplay nullValue window reference
      environment schedule).prefixThrough stop
    ((source.sourceRealization profile).map fun cfg =>
      (compilation.supported.resolvingAssignedReplay nullValue window
        (cfg.1.nodeValues fallback) environment schedule).prefixThrough stop).prob stopped =
      (source.core.prog.decisionPositions.map fun slot =>
        compilation.assignedRegistrationFactor nullValue window environment schedule
          reference profile slot.1 slot.2).prod := by
  intro runtime stop stopped
  rw [compilation.sourceRealization_replay_probability,
    denoteSource_restriction_probability]
  exact (FinDist.expect_congr (compilation.assignedRestriction_weight_eq_product nullValue
    window environment schedule reference profile)).trans (FinDist.expect_const _ _)

end Vegas.SealedCompilation
