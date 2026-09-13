/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionReplay
import Vegas.Compile.SourceDisclosureReads
import Vegas.EventGraph.KernelRealization

/-! # Source-local extraction of native registrations

For fixed deterministic native responses, replay yields a choice function of
source-earlier honest disclosures. Every such disclosure is a declared read
of the compiled source decision. Reading those fields produces a legal graph
policy, and the existing policy roundtrip gives a legal written-source policy.

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

private def priorOpening (focal : Player)
    (decision : Fin (compile source.core).graph.nodeCount)
    (coordinate : compilation.supported.priorHonestCoordinates focal decision) :
    Fin (compile source.core).graph.nodeCount :=
  Classical.choose (compilation.supported.priorHonestCoordinates_opening focal
    decision coordinate.val coordinate.property)

private theorem priorOpening_spec (focal : Player)
    (decision : Fin (compile source.core).graph.nodeCount)
    (coordinate : compilation.supported.priorHonestCoordinates focal decision) :
    (compilation.priorOpening focal decision coordinate).val < decision.val ∧
      ((compile source.core).graph.nodeRow
        (compilation.priorOpening focal decision coordinate)).sem =
          .reveal ((compile source.core).graph.nodeTarget coordinate.val) :=
  Classical.choose_spec (compilation.supported.priorHonestCoordinates_opening focal
    decision coordinate.val coordinate.property)

private theorem priorOpening_mem_reads (focal : Player)
    (decision : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hdecision : ((compile source.core).graph.nodeRow decision).sem = .commit focal guard)
    (coordinate : compilation.supported.priorHonestCoordinates focal decision) :
    { field := (compile source.core).graph.nodeTarget
        (compilation.priorOpening focal decision coordinate), ty := ty } ∈ guard.choiceReads := by
  let opening := compilation.priorOpening focal decision coordinate
  have hspec := compilation.priorOpening_spec focal decision coordinate
  have hwf := compilation.supported.graphWF opening _
    ((compile source.core).graph.nodes_get?_nodeRow opening)
  simp only [Graph.nodeWFAt, opening, hspec.2] at hwf
  obtain ⟨_, _, _, _, hpublic⟩ := hwf.2
  have hread := compile_commit_prior_public_read source.core focal decision opening guard
    hdecision hspec.1 hpublic
  simpa only [compilation.supported.rowType] using hread

/-- Read one earlier public opening for each honest assignment coordinate
needed by replay. The compiler proves these fields are in the source choice's
declared information; no runtime history is an input to this function. -/
def disclosureInputs (focal : Player)
    (decision : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hdecision : ((compile source.core).graph.nodeRow decision).sem = .commit focal guard)
    (reads : ReadEnv L guard.choiceReads) :
    compilation.supported.priorHonestCoordinates focal decision → L.Val ty :=
  fun coordinate => reads.read _
    (compilation.priorOpening_mem_reads focal decision guard hdecision coordinate)

/-- In a complete reachable source graph, the extracted policy's actual
disclosure inputs are the corresponding commitment values. This follows from
the graph's reveal semantics, not an assumed source/native input equation. -/
theorem disclosureInputs_eq_nodeValues (focal : Player)
    (decision : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hdecision : ((compile source.core).graph.nodeRow decision).sem = .commit focal guard)
    (cfg : ReachableConfig (compile source.core).graph)
    (hterminal : Terminal (compile source.core).graph cfg.1)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? cfg.1.store guard.choiceReads = some reads)
    (fallback : L.Val ty) :
    compilation.disclosureInputs focal decision guard hdecision reads =
      fun coordinate => cfg.1.nodeValues fallback coordinate.val := by
  funext coordinate
  let opening := compilation.priorOpening focal decision coordinate
  have hspec := compilation.priorOpening_spec focal decision coordinate
  have hread := ReadEnv.ofStore?_read hreads
    (compilation.priorOpening_mem_reads focal decision guard hdecision coordinate)
  obtain ⟨row, hrow, hvalid⟩ := reachable_validDoneValues compilation.supported.graphWF
    cfg.2 opening (hterminal opening)
  have hrowEq : row = (compile source.core).graph.nodeRow opening :=
    Option.some.inj (hrow.symm.trans ((compile source.core).graph.nodes_get?_nodeRow opening))
  subst row
  rw [hspec.2] at hvalid
  change ∃ value : L.Val ((compile source.core).graph.nodeRow opening).ty,
    Store.getAs cfg.1.store ((compile source.core).graph.nodeTarget opening)
        ((compile source.core).graph.nodeRow opening).ty = some value ∧
      Store.getAs cfg.1.store ((compile source.core).graph.nodeTarget coordinate.val)
        ((compile source.core).graph.nodeRow opening).ty = some value at hvalid
  rw [compilation.supported.rowType opening] at hvalid
  obtain ⟨value, htarget, hproducer⟩ := hvalid
  have hvalue : reads.read _
      (compilation.priorOpening_mem_reads focal decision guard hdecision coordinate) = value :=
    Option.some.inj (hread.symm.trans htarget)
  change reads.read _
    (compilation.priorOpening_mem_reads focal decision guard hdecision coordinate) =
      (Store.getAs cfg.1.store
        ((compile source.core).graph.nodeTarget coordinate.val) ty).getD fallback
  rw [hproducer, Option.getD_some, hvalue]

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
  fun decision guard hdecision reads => FinDist.pure
    ⟨cast (congrArg L.Val (compilation.supported.commitType decision focal guard hdecision).symm)
      (compilation.supported.extractedChoice nullValue window focal deviator environment schedule
        decision (compilation.disclosureInputs focal decision guard hdecision reads) fallback),
      compilation.supported.commitGuard decision focal guard hdecision _ reads⟩

/-- The extraction inhabits the existing written-source strategy type. -/
def extractedSourcePolicy : SourceBehavioralPolicy source.core.prog focal :=
  backtranslateCommitPolicy source.core focal
    (compilation.extractedCommitPolicy nullValue window focal deviator environment schedule
      fallback)

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
    (hinputs : compilation.disclosureInputs focal decision guard hdecision reads =
      fun coordinate => values coordinate.val) :
    ((compilation.extractedCommitPolicy nullValue window focal deviator environment schedule
      fallback) decision guard hdecision reads).map
        (fun value => cast
          (congrArg L.Val (compilation.supported.commitType decision focal guard hdecision))
          value.1) =
      FinDist.pure ((compilation.supported.resolvingBinding nullValue window values focal
        deviator environment schedule decision).getD fallback) := by
  simp only [extractedCommitPolicy, FinDist.map_pure, cast_cast, cast_eq, hinputs]
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
    (hinputs : compilation.disclosureInputs focal decision guard hdecision reads =
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
