/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.KernelSupport
import Vegas.EventGraph.KernelSchedule

/-! # Realized commitment kernels in the current graph store

A completed commitment retains its sampled value and its declared inputs.
Consequently its value remains supported by the same policy kernel when those
inputs are reconstructed from any later reachable store. This concerns actual
policy execution, not just guard validity or unconstrained graph reachability.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} {G : Graph Player L}

/-- A common-domain projection of graph node values. The supplied fallback
totalizes missing or differently typed fields; terminal homogeneous graphs
use their actual stored values at every coordinate. -/
def Config.nodeValues {ty : L.Ty} (cfg : Config G) (fallback : L.Val ty) :
    Fin G.nodeCount → L.Val ty :=
  fun node => (Store.getAs cfg.store (G.nodeTarget node) ty).getD fallback

/-- Every completed commitment has a supported policy choice at the declared
inputs reconstructed from the current store. -/
def CommitValuesSupported (policies : CommitPolicyProfile G) (cfg : Config G) : Prop :=
  ∀ (node : Fin G.nodeCount), node ∈ cfg.done → ∀ who guard
    (hsem : (G.nodeRow node).sem = .commit who guard),
    ∃ reads : ReadEnv L guard.choiceReads,
      ReadEnv.ofStore? cfg.store guard.choiceReads = some reads ∧
      ∃ choice ∈ (policies who node guard hsem reads).support,
        cfg.store (G.nodeTarget node) = some (⟨guard.ty, choice.1⟩ : TypedValue L)

theorem CommitValuesSupported.initial (policies : CommitPolicyProfile G) :
    CommitValuesSupported policies (Config.initial G) := by
  intro node hnode
  simp only [Config.initial, Finset.notMem_empty] at hnode

private theorem supported_commit_preserved (hwf : G.WF)
    (policies : CommitPolicyProfile G) (cfg : ReachableConfig G)
    (hsupported : CommitValuesSupported policies cfg.1)
    (other : Fin G.nodeCount) (hother : other ∉ cfg.1.done) (written : TypedValue L)
    (node : Fin G.nodeCount) (hdone : node ∈ cfg.1.done)
    (who : Player) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard) :
    ∃ reads : ReadEnv L guard.choiceReads,
      ReadEnv.ofStore? (cfg.1.completeNode other written).store guard.choiceReads = some reads ∧
      ∃ choice ∈ (policies who node guard hsem reads).support,
        (cfg.1.completeNode other written).store (G.nodeTarget node) =
          some (⟨guard.ty, choice.1⟩ : TypedValue L) := by
  obtain ⟨reads, hreads, choice, hchoice, hvalue⟩ := hsupported node hdone who guard hsem
  have hnot := DonePrereqs.nodeTarget_not_mem_reads_of_not_done hwf (reachable_donePrereqs cfg.2)
    (G.nodes_get?_nodeRow node) (G.nodes_get?_nodeRow other) hdone hother
  refine ⟨reads, ReadEnv.ofStore?_completeNode_of_not_read hreads ?_, choice, hchoice, ?_⟩
  · intro ref href heq
    apply hnot
    rw [hsem]
    exact Finset.mem_image.mpr ⟨ref, href, heq⟩
  · change (cfg.1.store.set (G.nodeTarget other) written) (G.nodeTarget node) = _
    have hne : node ≠ other := fun heq => hother (heq ▸ hdone)
    rw [Store.set_ne _ (Config.nodeTarget_ne_of_ne (G := G) hne)]
    exact hvalue

variable [Fintype Player]

theorem policyNodeStep_support_commitValues (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (cfg : ReachableConfig G)
    (hsupported : CommitValuesSupported policies cfg.1)
    (node : Fin G.nodeCount) (next : ReachableConfig G)
    (hnext : next ∈ (policyNodeStep hwf hguards policies cfg node).support) :
    CommitValuesSupported policies next.1 := by
  classical
  by_cases hready : Ready G cfg.1 node
  · rw [policyNodeStep, dif_pos hready, FinDist.support_map] at hnext
    obtain ⟨write, hwrite, rfl⟩ := hnext
    intro query hdone who guard hsem
    have hcases : query = node ∨ query ∈ cfg.1.done := by
      simpa only [Config.completeNode, write.event_node, Finset.mem_insert] using hdone
    rcases hcases with hsame | hold
    · subst query
      obtain ⟨reads, hreads⟩ := (reachable_storeCoherent hwf cfg.2).readEnvOfReady hwf
        (G.nodes_get?_nodeRow node) hready
        (fun ref href => by rw [hsem]; exact Finset.mem_image.mpr ⟨ref, href, rfl⟩)
        (fun ref href => by
          have hnode := hwf node (G.nodeRow node) (G.nodes_get?_nodeRow node)
          simp only [Graph.nodeWFAt, hsem] at hnode
          obtain ⟨spec, hfield, hty, _⟩ := hnode.2.2.2 ref href
          exact ⟨spec, hfield, hty⟩)
      have hwritten : write.written ∈
          ((policyValueLaw hwf hguards policies cfg node hready).map
            PolicyWrite.written).support := by
        rw [FinDist.support_map]
        exact ⟨write, hwrite, rfl⟩
      rw [map_written_policyValueLaw_of_commitKernel hwf hguards policies cfg node hready
        who guard hsem reads hreads, FinDist.support_map] at hwritten
      obtain ⟨choice, hchoice, hvalue⟩ := hwritten
      refine ⟨reads, ?_, choice, hchoice, ?_⟩
      · apply ReadEnv.ofStore?_completeNode_of_not_read hreads
        intro ref href heq
        apply G.nodeTarget_not_mem_own_reads hwf (G.nodes_get?_nodeRow node)
        rw [hsem]
        exact Finset.mem_image.mpr ⟨ref, href,
          heq.trans (congrArg (fun index : Fin G.nodeCount => G.nodeTarget index) write.event_node)⟩
      · simp only [Config.completeNode, write.event_node, Store.set_eq, hvalue]
    · simpa only [write.event_node] using supported_commit_preserved hwf policies cfg
        hsupported node hready.1 write.written query hold who guard hsem
  · rw [policyNodeStep_of_not_ready hwf hguards policies cfg node hready,
      FinDist.mem_support_pure] at hnext
    exact hnext ▸ hsupported

/-- The actual graph runner retains all supported choices and their input
environments. The requested order need not be topological: non-ready requests
use the runner's unchanged no-op branch. -/
theorem runPolicyNodes_support_commitValues (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (cfg : ReachableConfig G)
    (hsupported : CommitValuesSupported policies cfg.1)
    (order : List (Fin G.nodeCount)) (next : ReachableConfig G)
    (hnext : next ∈ (runPolicyNodes hwf hguards policies cfg order).support) :
    CommitValuesSupported policies next.1 := by
  induction order generalizing cfg with
  | nil =>
      rw [runPolicyNodes_nil, FinDist.mem_support_pure] at hnext
      exact hnext ▸ hsupported
  | cons node rest ih =>
      simp only [runPolicyNodes_cons, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      exact ih middle (policyNodeStep_support_commitValues hwf hguards policies cfg
        hsupported node middle hmiddle) hnext

end Vegas.EventGraph
