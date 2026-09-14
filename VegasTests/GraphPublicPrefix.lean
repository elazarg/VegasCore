/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.PublicPrefix
import Vegas.Core.ExprSimple
import Vegas.Compile.SealedCandidateHonestGraphRound
import Interaction.SealedResolutionReservations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-! # Public-prefix readability is a separate information condition

A well-formed commit/reveal graph may omit an earlier public output from a
later decision's declared reads. The backend's information premise therefore
cannot be inferred from ordinary graph well-formedness.
-/

namespace VegasTests.GraphPublicPrefix

open Vegas Vegas.EventGraph

private def guard : EventGuard simpleExpr where
  ty := .bool
  code := {
    actionName := 0
    Context := []
    expr := Expr.constBool true
    fieldOf := by intro name ty binding; cases binding }
  choiceReads := ∅
  read_mem := by intro name ty binding; cases binding

private def graph : Graph Bool simpleExpr where
  initialFields := []
  nodes := [⟨.bool, some false, .commit false guard⟩,
    ⟨.bool, none, .reveal 0⟩, ⟨.bool, some true, .commit true guard⟩]

theorem well_formed : graph.WF := by
  intro index event hrow
  have hlt := (List.getElem?_eq_some_iff.mp hrow).1
  change index < 3 at hlt
  interval_cases index <;>
    simp only [graph, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at hrow <;>
    subst event <;>
    simp [graph, Graph.nodeWFAt, NodeSem.reads, guard, FieldRef.fields,
      Graph.fieldAvailableBefore, Graph.field?]

theorem public_prefix_not_readable : ¬graph.PublicPrefixReadable := by
  intro h
  have hread := h true ⟨2, by decide⟩ ⟨1, by decide⟩ guard rfl (by decide) rfl
  exact Finset.notMem_empty _ hread

private theorem supported : SealedFragment graph .bool where
  graphWF := well_formed
  rowType := by intro node; fin_cases node <;> rfl
  noSamples := by intro node dist; fin_cases node <;> simp [graph, Graph.nodeRow]
  commitType := by
    intro node who test hsem
    fin_cases node <;> simp only [graph, Graph.nodeRow, List.getElem_cons_zero,
      List.getElem_cons_succ, NodeSem.commit.injEq] at hsem
    · exact hsem.2.symm ▸ rfl
    · cases hsem
    · exact hsem.2.symm ▸ rfl
  commitGuard := by
    intro node who test hsem value env
    fin_cases node <;> simp only [graph, Graph.nodeRow, List.getElem_cons_zero,
      List.getElem_cons_succ, NodeSem.commit.injEq] at hsem
    · rcases hsem with ⟨_, rfl⟩; rfl
    · cases hsem
    · rcases hsem with ⟨_, rfl⟩; rfl
  revealSource := by
    intro node field hsem
    fin_cases node <;> simp only [graph, Graph.nodeRow, List.getElem_cons_zero,
      List.getElem_cons_succ] at hsem
    · cases hsem
    · cases hsem
      exact ⟨⟨0, by decide⟩, false, guard, rfl, rfl⟩
    · cases hsem

private theorem guards_live : GuardLive graph := by
  intro node row who test hrow hsem env
  have hrowEq : row = graph.nodeRow node :=
    Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow node))
  subst row
  refine ⟨cast (congrArg simpleExpr.Val (supported.commitType node who test hsem).symm) false, ?_⟩
  exact supported.commitGuard node who test hsem _ env

noncomputable section

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

/-- The honest law applies to an independently specified graph that fails the
deviation extraction's information condition. Every graph profile is allowed;
the concrete service parameters ensure normal completion. -/
theorem honest_candidate_law_without_public_prefix
    (profile : CommitPolicyProfile graph)
    (base : (supported.resolvingRuntime false 11).messageApplication.WirePolicy) :
    let runtime := supported.resolvingRuntime false 11
    let wire := runtime.messageApplication.reserveInclusion
      (SealedResolution.periodicFinalReservation 4 2) base
    ∃ coupling : FinDist (ReachableConfig graph × runtime.candidateApplication.PolicyExecution),
      coupling.map Prod.fst = runPolicyNodes supported.graphWF guards_live profile
        ⟨Config.initial graph, .initial⟩ graph.nodeOrder ∧
      coupling.map Prod.snd = runtime.candidateRoundDriver.runRounds [false, true] 4
        (fun who => runtime.candidatePlayerPolicy
          (supported.resolvingPolicy false 11 who (profile who)))
        (runtime.candidateWirePolicy wire) 36
        (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial)) ∧
      ∀ cfg next, (cfg, next) ∈ coupling.support →
        Terminal graph cfg.1 ∧ runtime.complete next.native.application.visible = true ∧
        next.native.application.visible.timeouts = [] ∧
        ∀ ref : FieldRef simpleExpr, graph.fieldRefPublic ref →
          Store.getAs (graph.publicSealedStore .bool next.native.application.visible.events)
            ref.field ref.ty = Store.getAs cfg.1.store ref.field ref.ty := by
  intro runtime wire
  exact supported.exists_honest_candidate_round_graph_coupling guards_live false 11 [false, true]
    4 profile wire (SealedResolution.periodicFinalReservation 4 2)
    (runtime.messageApplication.reserveInclusion_service _ base) 2 (by decide)
    (fun block => SealedResolution.periodicFinalReservation_capacity [false, true] 4 2 block
      (by decide) (by decide))
    (by intro who; cases who <;> simp) (by decide) 36 ⟨18, rfl⟩ (by decide)

end

end VegasTests.GraphPublicPrefix
