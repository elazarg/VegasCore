/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedDisclosurePolicy
import Vegas.Compile.SourceDisclosureReads

/-! # Source policies from earlier disclosed choices

Every source-earlier honest disclosure is a declared read of the compiled
source decision. Any function of those disclosed values therefore produces a
legal graph policy, and the exact policy roundtrip gives a legal written-source
policy. This constructor is independent of the native commitment host.

The local agreement theorem identifies its action with the replay registration
when its disclosure inputs agree with the assigned values. For a complete
reachable source realization, the graph's reveal semantics establish the
disclosure-input equation. The whole-program coupling must still compare the
honest native inputs and identify the joint law of the honest draws.
The fallback totalizes absent registrations; it is not a timeout settlement.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty}
variable (compilation : SealedCompilation source ty)

/-- Source-local disclosed-value functions inhabit the original source
strategy type, not an enlarged strategy space with runtime observations. -/
def sourcePolicyOfDisclosures (focal : Player)
    (choose : (decision : Fin (compile source.core).graph.nodeCount) →
      (compilation.supported.priorHonestCoordinates focal decision → L.Val ty) → L.Val ty) :
    SourceBehavioralPolicy source.core.prog focal :=
  backtranslateCommitPolicy source.core focal
    (compilation.supported.commitPolicyOfDisclosures (compile_publicPrefixReadable source.core)
      focal choose)

theorem compile_sourcePolicyOfDisclosures (focal : Player)
    (choose : (decision : Fin (compile source.core).graph.nodeCount) →
      (compilation.supported.priorHonestCoordinates focal decision → L.Val ty) → L.Val ty) :
    compileSourcePolicy source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      rfl focal (compilation.sourcePolicyOfDisclosures focal choose) =
      compilation.supported.commitPolicyOfDisclosures (compile_publicPrefixReadable source.core)
        focal choose :=
  compile_backtranslateCommitPolicy source.core focal _

variable [DecidableEq (L.Val ty)] (nullValue : L.Val ty) (window : Nat) (focal : Player)
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

/-- A single graph policy extracts all of the focal player's decisions using
the same native response functions. Unrestricted backend guards make the
fallback legal, including at source views not reached by native replay. -/
def extractedCommitPolicy : CommitPolicy (compile source.core).graph focal :=
  compilation.supported.commitPolicyOfDisclosures (compile_publicPrefixReadable source.core)
    focal fun decision visible =>
      compilation.supported.extractedChoice nullValue window focal deviator environment schedule
        decision visible fallback

/-- The extraction inhabits the existing written-source strategy type. -/
def extractedSourcePolicy : SourceBehavioralPolicy source.core.prog focal :=
  compilation.sourcePolicyOfDisclosures focal fun decision visible =>
    compilation.supported.extractedChoice nullValue window focal deviator environment schedule
      decision visible fallback

theorem compile_extractedSourcePolicy :
    compileSourcePolicy source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      rfl focal
      (compilation.extractedSourcePolicy nullValue window focal deviator environment schedule
        fallback) =
      compilation.extractedCommitPolicy nullValue window focal deviator environment schedule
        fallback :=
  compile_backtranslateCommitPolicy source.core focal _

/-- Agreement of the actual declared inputs recovers the native registration
at this decision. The outer option records absence, independently of any
nullable value registered by the player. -/
theorem extractedCommitPolicy_law
    (values : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (decision : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hdecision : ((compile source.core).graph.nodeRow decision).sem = .commit focal guard)
    (reads : ReadEnv L guard.choiceReads)
    (hinputs : compilation.supported.disclosureInputs (compile_publicPrefixReadable source.core)
      focal decision guard hdecision reads =
      fun coordinate => values coordinate.val) :
    ((compilation.extractedCommitPolicy nullValue window focal deviator environment schedule
      fallback) decision guard hdecision reads).map
        (fun value => cast
          (congrArg L.Val (compilation.supported.commitType decision focal guard hdecision))
          value.1) =
      FinDist.pure ((compilation.supported.resolvingBinding nullValue window values focal
        deviator environment schedule decision).getD fallback) := by
  simp only [extractedCommitPolicy, SealedFragment.commitPolicyOfDisclosures, FinDist.map_pure,
    cast_cast, cast_eq, hinputs]
  rw [compilation.supported.extractedChoice_eq_binding nullValue window values focal
    deviator environment schedule decision guard hdecision fallback]

/-- The legal source policy has the extracted native action law after the
compiler's exact source/graph information translation. This is a local kernel
law, not yet the whole-program source/native probability coupling. -/
theorem extractedSourcePolicy_law
    (values : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (decision : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hdecision : ((compile source.core).graph.nodeRow decision).sem = .commit focal guard)
    (reads : ReadEnv L guard.choiceReads)
    (hinputs : compilation.supported.disclosureInputs (compile_publicPrefixReadable source.core)
      focal decision guard hdecision reads =
      fun coordinate => values coordinate.val) :
    (compileSourcePolicy source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      rfl focal
      (compilation.extractedSourcePolicy nullValue window focal deviator environment schedule
        fallback)
      decision guard hdecision reads).map
        (fun value => cast
          (congrArg L.Val (compilation.supported.commitType decision focal guard hdecision))
          value.1) =
      FinDist.pure ((compilation.supported.resolvingBinding nullValue window values focal
        deviator environment schedule decision).getD fallback) := by
  rw [compile_extractedSourcePolicy]
  exact compilation.extractedCommitPolicy_law nullValue window focal deviator environment schedule
    fallback values decision guard hdecision reads hinputs

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.extractedSourcePolicy_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedSourcePolicy_law
