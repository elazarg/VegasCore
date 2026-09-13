/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedSourceExtraction
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
