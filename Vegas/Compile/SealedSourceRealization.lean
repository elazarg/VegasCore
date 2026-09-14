/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedSourceExtraction
import Vegas.Compile.SealedResolutionCylinder
import Vegas.Compile.SealedSourceInputs
import Vegas.Compile.SourceCorrespondence

/-! # Source execution under the extracted native policy

The law below is the canonical graph realization of the written source, with
only the focal player's policy replaced. Its source marginal is the existing
written-order denotation. At each supported terminal realization, replay of
its honest values recovers every focal source choice. Native marginal equality
still requires the cylinder-mass argument for the unchanged honest kernels.
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
  MessageApplication.EnvironmentObservation
    (compilation.supported.resolvingRuntime nullValue window).messageApplication →
  MessageApplication.EnvironmentPolicyCommand
    (compilation.supported.resolvingRuntime nullValue window).messageApplication)
variable (schedule : List (@Invocation Player)) (fallback : L.Val ty)

/-- The original source execution represented by its compiled graph state,
with the extracted policy replacing only the focal player. Honest kernels are
unchanged and may depend on all their declared public and private inputs. -/
def extractedSourceRun (profile : SourceBehavioralProfile source.core.prog) :
    FinDist (ReachableConfig (compile source.core).graph) :=
  runPolicyNodes (compile source.core).graphWF (compile_guardLive source.core source.legal)
    (Profile.update (sig := ⟨CommitPolicy (compile source.core).graph,
      ReachableConfig (compile source.core).graph⟩)
      (fun who => compileSourcePolicy source.core.prog source.core.fresh
        (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
        rfl who (profile who)) focal
      (compilation.extractedCommitPolicy nullValue window focal deviator environment schedule
        fallback))
    ⟨Config.initial (compile source.core).graph, .initial⟩ (compile source.core).graph.nodeOrder

/-- This is the exact written-source law against unchanged opponents, not a
new source evaluator or a chosen law postulated to match native execution. -/
theorem extractedSourceRun_source (profile : SourceBehavioralProfile source.core.prog) :
    (compilation.extractedSourceRun nullValue window focal deviator environment schedule
      fallback profile).map (observeSourceOutcome source.core) =
      (denoteSource source.core.prog
        (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
          (compilation.extractedSourcePolicy nullValue window focal deviator environment schedule
            fallback)) source.core.env).map some :=
  runPolicyNodes_source_deviation source.core source.legal profile focal _

theorem extractedSourceRun_terminal (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (hcfg : cfg ∈ (compilation.extractedSourceRun nullValue window focal deviator environment
      schedule fallback profile).support) : Terminal (compile source.core).graph cfg.1 := by
  exact runPolicyNodes_terminal (compile source.core).graphWF
    (compile_guardLive source.core source.legal) _
    ⟨Config.initial (compile source.core).graph, .initial⟩ (compile source.core).graph.nodeOrder
    (compile source.core).graph.nodeOrder_readyOrder (fun node => Or.inr (by simp)) cfg hcfg

/-- In every supported complete source realization, all focal choices equal
the first native registrations extracted from replay of that realization's
honest values, or the same legal fallback when registration is absent.
No input-agreement premise remains in this statement. -/
theorem extractedSourceRun_consistent (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (hcfg : cfg ∈ (compilation.extractedSourceRun nullValue window focal deviator environment
      schedule fallback profile).support)
    (decision : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hdecision : ((compile source.core).graph.nodeRow decision).sem = .commit focal guard) :
    cfg.1.nodeValues fallback decision =
      (compilation.supported.resolvingBinding nullValue window (cfg.1.nodeValues fallback) focal
        deviator environment schedule decision).getD fallback := by
  have hterminal := compilation.extractedSourceRun_terminal nullValue window focal
    deviator environment schedule fallback profile cfg hcfg
  have hchoices := runPolicyNodes_support_commitValues (compile source.core).graphWF
    (compile_guardLive source.core source.legal) _ _ (CommitValuesSupported.initial _)
    (compile source.core).graph.nodeOrder cfg hcfg
  obtain ⟨reads, hreads, choice, hchoice, hvalue⟩ :=
    hchoices decision (hterminal decision) focal guard hdecision
  rw [Profile.update_same] at hchoice
  have hinputs := compilation.disclosureInputs_eq_nodeValues focal decision guard hdecision
    cfg hterminal reads hreads fallback
  have hlaw := compilation.extractedCommitPolicy_law nullValue window focal deviator environment
    schedule fallback (cfg.1.nodeValues fallback) decision guard hdecision reads hinputs
  have hselected : cast (congrArg L.Val
      (compilation.supported.commitType decision focal guard hdecision)) choice.1 ∈
      (((compilation.extractedCommitPolicy nullValue window focal deviator environment schedule
        fallback) decision guard hdecision reads).map (fun value => cast (congrArg L.Val
          (compilation.supported.commitType decision focal guard hdecision)) value.1)).support := by
    rw [FinDist.support_map]
    exact ⟨choice, hchoice, rfl⟩
  rw [hlaw, FinDist.mem_support_pure] at hselected
  change cfg.1.store ((compile source.core).graph.nodeTarget decision) =
    some (⟨guard.ty, choice.1⟩ : TypedValue L) at hvalue
  rw [Config.nodeValues, Store.getAs, hvalue]
  simpa only [TypedValue.as?,
    dif_pos (compilation.supported.commitType decision focal guard hdecision), Option.getD_some]
    using hselected

/-- All focal source-owned registrations at the same first-timeout checkpoint
are retained in the complete source realization, including registrations made
speculatively before their source decision becomes ready. -/
theorem extractedSourceRun_locked (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (hcfg : cfg ∈ (compilation.extractedSourceRun nullValue window focal deviator environment
      schedule fallback profile).support)
    (decision : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hdecision : ((compile source.core).graph.nodeRow decision).sem = .commit focal guard)
    (value : L.Val ty)
    (hregistered :
      (compilation.supported.resolvingStop nullValue window (cfg.1.nodeValues fallback) focal
        deviator environment schedule).native.application.service.lookup (focal, decision.val) =
          some value) :
    cfg.1.nodeValues fallback decision = value := by
  have hchoice := compilation.extractedSourceRun_consistent nullValue window focal deviator
    environment schedule fallback profile cfg hcfg decision guard hdecision
  rw [EventGraph.SealedFragment.resolvingBinding_eq_stop_lookup, hregistered,
    Option.getD_some] at hchoice
  exact hchoice

/-- Every source-owned private registration at the common checkpoint agrees
with the complete source realization, for honest players and the deviator alike. -/
theorem extractedSourceRun_registered (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (hcfg : cfg ∈ (compilation.extractedSourceRun nullValue window focal deviator environment
      schedule fallback profile).support)
    (owner : Player) (decision : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hdecision : ((compile source.core).graph.nodeRow decision).sem = .commit owner guard)
    (value : L.Val ty)
    (hregistered :
      (compilation.supported.resolvingStop nullValue window (cfg.1.nodeValues fallback) focal
        deviator environment schedule).native.application.service.lookup (owner, decision.val) =
          some value) : cfg.1.nodeValues fallback decision = value := by
  by_cases howner : owner = focal
  · subst owner
    exact compilation.extractedSourceRun_locked nullValue window focal deviator environment
      schedule fallback profile cfg hcfg decision guard hdecision value hregistered
  · exact (compilation.supported.resolvingStop_honest_lookup nullValue window focal
      deviator environment schedule (cfg.1.nodeValues fallback)
      owner decision value howner hregistered).symm

/-- At every selected checkpoint before the first timeout, included openings
already have their complete source values. Arrival and inclusion order are
unrestricted. The later execution may time out; the comparison stops before
public defaults can replace the registered values. -/
theorem extractedSourceRun_opened (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (hcfg : cfg ∈ (compilation.extractedSourceRun nullValue window focal deviator environment
      schedule fallback profile).support)
    (release :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
        Bool) :
    let stopped := ((compilation.supported.resolvingReplay nullValue window
      (cfg.1.nodeValues fallback) focal deviator environment schedule).prefixThrough
        (fun execution : (compilation.supported.resolvingRuntime
            nullValue window).messageApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)).firstRelease release
    stopped.native.application.visible.timeouts = [] → ∀ node value,
      SealedProgram.Event.opened node value ∈ stopped.native.application.visible.events →
      cfg.1.store ((compile source.core).graph.nodeTarget node) =
        some (⟨ty, value⟩ : TypedValue L) := by
  intro stopped hclear node value hopened
  obtain ⟨before, after, hbefore, hafter⟩ := compilation.supported.resolvingReplay_prefix_support
    nullValue window focal deviator environment schedule release (cfg.1.nodeValues fallback)
  have hbinding := (compilation.supported.resolvingRuntime nullValue
    window).runPolicies_beforeTimeoutBinding _ _ before _ stopped
      SealedResolution.BeforeTimeoutBinding.initial hbefore hclear
  apply compilation.supported.opened_source_value cfg
    (compilation.extractedSourceRun_terminal nullValue window focal deviator environment schedule
      fallback profile cfg hcfg) fallback _ hbinding ?_ node value hopened
  intro owner decision guard hdecision registered hregistered
  exact compilation.extractedSourceRun_registered nullValue window focal deviator environment
    schedule fallback profile cfg hcfg owner decision guard hdecision registered
    ((compilation.supported.resolvingRuntime nullValue window).runPolicies_lookup_of_eq_some
      _ _ after stopped _ (owner, decision.val) registered hregistered hafter)

/-- At every fresh honest registration in a pre-timeout replay, the original
compiled policy draws its unchanged source kernel at the complete source's
declared inputs. Freshness and input agreement follow from actual execution;
neither cache correctness nor successful reads are assumed. -/
theorem extractedSourceRun_registration_kernel
    (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (hcfg : cfg ∈ (compilation.extractedSourceRun nullValue window focal deviator environment
      schedule fallback profile).support)
    (release :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
        Bool) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let stopped := ((compilation.supported.resolvingReplay nullValue window
      (cfg.1.nodeValues fallback) focal deviator environment schedule).prefixThrough
        (fun execution : runtime.messageApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)).firstRelease release
    stopped.native.application.visible.timeouts = [] →
    ∀ who, who ≠ focal → ∀ slot value,
      .privateCommand ⟨(slot, value)⟩ ∈
        (compilation.supported.resolvingValuePlayers nullValue window (cfg.1.nodeValues fallback)
          focal (fun history view => FinDist.pure (deviator history view)) who
          (stopped.principalHistory who)
          (State.observe runtime.messageApplication stopped.native who)).support →
      ∃ (node : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
        (hsem : ((compile source.core).graph.nodeRow node).sem = .commit who guard)
        (reads : ReadEnv L guard.choiceReads),
        slot = node.val ∧ stopped.native.application.service.lookup (who, node.val) = none ∧
        ReadEnv.ofStore? cfg.1.store guard.choiceReads = some reads ∧
        compilation.compileResolvingPolicy nullValue window who (profile who)
          (stopped.principalHistory who) (State.observe runtime.messageApplication stopped.native
            who) =
          ((compileSourcePolicy source.core.prog source.core.fresh
            (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
            rfl who (profile who)) node guard hsem reads).map (fun choice =>
              .privateCommand ⟨(node.val, cast (congrArg L.Val
                (compilation.supported.commitType node who guard hsem)) choice.1)⟩) := by
  intro runtime stopped hclear who hwho slot value hcommand
  rw [EventGraph.SealedFragment.resolvingValuePlayers, Profile.update_of_ne _ _ hwho,
    EventGraph.SealedFragment.resolvingPolicy_no_timeout _ _ _ _ _ _ _ hclear] at hcommand
  obtain ⟨node, guard, hsem, reads, hslot, hcache, hreads, hkernel⟩ :=
    compilation.supported.selected_registration_kernel who [] _ _ _ _ slot value hcommand
  obtain ⟨before, after, hbefore, hafter⟩ := compilation.supported.resolvingReplay_prefix_support
    nullValue window focal deviator environment schedule release (cfg.1.nodeValues fallback)
  have hmemory := SealedResolution.RegistrationMemory.runPolicies _ _ before _ stopped
    SealedResolution.RegistrationMemory.initial hbefore
  have hbinding := runtime.runPolicies_beforeTimeoutBinding _ _ before _ stopped
    SealedResolution.BeforeTimeoutBinding.initial hbefore hclear
  have hregistered : ∀ owner (decision : Fin (compile source.core).graph.nodeCount) guard,
      ((compile source.core).graph.nodeRow decision).sem = .commit owner guard → ∀ registered,
      stopped.native.application.service.lookup (owner, decision.val) = some registered →
        cfg.1.nodeValues fallback decision = registered := by
    intro owner decision guard hdecision registered hregistered
    exact compilation.extractedSourceRun_registered nullValue window focal deviator environment
      schedule fallback profile cfg hcfg owner decision guard hdecision registered
      (runtime.runPolicies_lookup_of_eq_some _ _ after stopped _ (owner, decision.val)
        registered hregistered hafter)
  have hhistory : ∀ index,
      (compilation.supported.compile.registrationEncoding index).cachedValue
        (compilation.supported.compile.messageApplication (Value := L.Val ty))
        (runtime.eventHistory (stopped.principalHistory who)) =
          stopped.native.application.service.lookup (who, index) := by
    intro index
    exact (runtime.eventHistory_cache (runtime.program.registrationEncoding index)
      (stopped.principalHistory who)).trans (hmemory who index).symm
  refine ⟨node, guard, hsem, reads, hslot, (hhistory node.val).symm.trans hcache, ?_, ?_⟩
  · exact compilation.supported.sealedPlayerStore_source_reads cfg
      (compilation.extractedSourceRun_terminal nullValue window focal deviator environment schedule
        fallback profile cfg hcfg) fallback _ hbinding hregistered who _ hhistory _ reads
      (ReadEnv.ofStore?_eq_some_of_ofStoreExec?_eq_some hreads)
  · rw [compileResolvingPolicy, EventGraph.SealedFragment.resolvingPolicy_no_timeout
      _ _ _ _ _ _ _ hclear]
    exact hkernel _

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.extractedSourceRun_source' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedSourceRun_source

/-- info: 'Vegas.SealedCompilation.extractedSourceRun_consistent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedSourceRun_consistent

/-- info: 'Vegas.SealedCompilation.extractedSourceRun_locked' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedSourceRun_locked

/-- info: 'Vegas.SealedCompilation.extractedSourceRun_registered' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedSourceRun_registered

/-- info: 'Vegas.SealedCompilation.extractedSourceRun_opened' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedSourceRun_opened

/-- info: 'Vegas.SealedCompilation.extractedSourceRun_registration_kernel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedSourceRun_registration_kernel
