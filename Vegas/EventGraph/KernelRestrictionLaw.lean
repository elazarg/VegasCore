/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.KernelRestriction
import Vegas.EventGraph.Information

/-! # Whole-run likelihood of legal graph choice restrictions

The normalized reference execution runs the ordinary graph executor with a
restricted profile. Previously completed values and declared reads persist,
so the likelihood and the restriction event can both be evaluated on its final
configuration. No source execution or independence assumption is used.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L}

namespace CommitRestriction

/-- The queried configuration satisfies the choices selected at the declared
inputs of the listed graph nodes. -/
def Allows (restriction : CommitRestriction G) (order : List (Fin G.nodeCount))
    (cfg : Config G) : Prop :=
  ∀ node ∈ order, restriction.AllowsStep cfg node cfg

/-- Product of original conditional probabilities of the forced choices. -/
def weight (restriction : CommitRestriction G) (profile : CommitPolicyProfile G)
    (order : List (Fin G.nodeCount)) (cfg : Config G) : ℝ :=
  (order.map (restriction.factor profile cfg)).prod

theorem allows_cons (restriction : CommitRestriction G) (node : Fin G.nodeCount)
    (rest : List (Fin G.nodeCount)) (cfg : Config G) :
    restriction.Allows (node :: rest) cfg ↔
      restriction.AllowsStep cfg node cfg ∧ restriction.Allows rest cfg := by
  simp only [Allows, List.mem_cons, forall_eq_or_imp]

theorem weight_cons (restriction : CommitRestriction G) (profile : CommitPolicyProfile G)
    (node : Fin G.nodeCount) (rest : List (Fin G.nodeCount)) (cfg : Config G) :
    restriction.weight profile (node :: rest) cfg =
      restriction.factor profile cfg node * restriction.weight profile rest cfg := rfl

end CommitRestriction

variable [Fintype Player]

/-- Restricted execution satisfies every listed restriction even when the
original profile gives the event probability zero. Earlier commitments must
already be supported by the reference profile; initialization satisfies this. -/
theorem runPolicyNodes_restriction_support
    (hwf : G.WF) (hguards : GuardLive G) (profile : CommitPolicyProfile G)
    (restriction : CommitRestriction G) (state : ReachableConfig G)
    (hsupported : CommitValuesSupported (restriction.apply profile) state.1)
    (order : List (Fin G.nodeCount)) (horder : G.ReadyOrder state.1.done order)
    (final : ReachableConfig G)
    (hfinal : final ∈
      (runPolicyNodes hwf hguards (restriction.apply profile) state order).support) :
    restriction.Allows order final.1 := by
  classical
  have hchoices := runPolicyNodes_support_commitValues hwf hguards (restriction.apply profile)
    state hsupported order final hfinal
  intro node hnode fixed hfixed
  have hdone : node ∈ final.1.done := by
    rw [runPolicyNodes_support_done hwf hguards (restriction.apply profile) state order
      horder final hfinal]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr hnode)
  cases hsem : (G.nodeRow node).sem with
  | commit who guard =>
      obtain ⟨reads, hreads, choice, hchoice, hvalue⟩ := hchoices node hdone who guard hsem
      rw [restriction.selected_commit final.1 node who guard hsem reads hreads] at hfixed
      cases hselected : restriction who node guard hsem reads with
      | none => simp only [hselected, Option.map_none] at hfixed; cases hfixed
      | some selected =>
          simp only [hselected, Option.map_some, Option.some.injEq] at hfixed
          have heq : choice = selected := by
            simpa only [CommitRestriction.apply, hselected, FinDist.mem_support_pure] using hchoice
          simpa only [heq, hfixed] using hvalue
  | sample dist =>
      rw [restriction.selected_internal _ _ (by simp [hsem, NodeSem.isInternal])] at hfixed
      cases hfixed
  | reveal source =>
      rw [restriction.selected_internal _ _ (by simp [hsem, NodeSem.isInternal])] at hfixed
      cases hfixed

private theorem step_extends (hwf : G.WF) (hguards : GuardLive G)
    (profile : CommitPolicyProfile G) (state : ReachableConfig G)
    (node : Fin G.nodeCount) (next : ReachableConfig G)
    (hnext : next ∈ (policyNodeStep hwf hguards profile state node).support) :
    state.1.Extends next.1 := by
  classical
  by_cases hready : Ready G state.1 node
  · obtain ⟨written, hwrite⟩ :=
      policyNodeStep_support_completeNode hwf hguards profile state node hready next hnext
    rw [hwrite]
    exact (Config.Extends.refl state.1).completeNode node hready.1 written
  · rw [policyNodeStep_of_not_ready hwf hguards profile state node hready,
      FinDist.mem_support_pure] at hnext
    subst next
    exact Config.Extends.refl _

private theorem run_extends (hwf : G.WF) (hguards : GuardLive G)
    (profile : CommitPolicyProfile G) (state : ReachableConfig G)
    (order : List (Fin G.nodeCount)) (next : ReachableConfig G)
    (hnext : next ∈ (runPolicyNodes hwf hguards profile state order).support) :
    state.1.Extends next.1 := by
  induction order generalizing state with
  | nil =>
      rw [runPolicyNodes_nil, FinDist.mem_support_pure] at hnext
      subst next
      exact Config.Extends.refl _
  | cons node rest ih =>
      simp only [runPolicyNodes_cons, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      exact (step_extends hwf hguards profile state node middle hmiddle).trans
        (ih middle hnext)

omit [Fintype Player] in
private theorem data_of_extends (hwf : G.WF)
    (profile : CommitPolicyProfile G) (restriction : CommitRestriction G)
    (state : ReachableConfig G) (next : Config G) (node : Fin G.nodeCount)
    (hready : Ready G state.1 node) (hextends : state.1.Extends next) :
    restriction.selected next node = restriction.selected state.1 node ∧
      restriction.factor profile next node = restriction.factor profile state.1 node := by
  by_cases hinternal : NodeSem.isInternal (G.nodeRow node).sem = true
  · rw [restriction.selected_internal _ _ hinternal,
      restriction.selected_internal _ _ hinternal,
      restriction.factor_internal _ _ _ hinternal,
      restriction.factor_internal _ _ _ hinternal]
    exact ⟨rfl, rfl⟩
  · have hcommit : ∃ who guard, (G.nodeRow node).sem = .commit who guard := by
      cases hsem : (G.nodeRow node).sem with
      | commit who guard => exact ⟨who, guard, rfl⟩
      | sample dist => simp [hsem, NodeSem.isInternal] at hinternal
      | reveal source => simp [hsem, NodeSem.isInternal] at hinternal
    obtain ⟨who, guard, hsem⟩ := hcommit
    obtain ⟨reads, hreads⟩ := (reachable_storeCoherent hwf state.2).readEnvOfReady hwf
      (G.nodes_get?_nodeRow node) hready
      (fun ref href => by rw [hsem]; exact Finset.mem_image.mpr ⟨ref, href, rfl⟩)
      (fun ref href => by
        have hnode := hwf node (G.nodeRow node) (G.nodes_get?_nodeRow node)
        simp only [Graph.nodeWFAt, hsem] at hnode
        obtain ⟨spec, hfield, hty, _⟩ := hnode.2.2.2 ref href
        exact ⟨spec, hfield, hty⟩)
    have hlater : ReadEnv.ofStore? next.store guard.choiceReads = some reads := by
      apply ReadEnv.ofStore?_eq_of_getAs_eq hreads
      intro ref href
      exact (hextends.getAs ref.field ref.ty (hready.fieldSettled_of_read hwf
        (G.nodes_get?_nodeRow node) (by
          rw [hsem]; exact Finset.mem_image.mpr ⟨ref, href, rfl⟩))).symm
    rw [restriction.selected_commit next node who guard hsem reads hlater,
      restriction.selected_commit state.1 node who guard hsem reads hreads,
      restriction.factor_commit profile next node who guard hsem reads hlater,
      restriction.factor_commit profile state.1 node who guard hsem reads hreads]
    exact ⟨rfl, rfl⟩

private theorem restriction_head_retained (hwf : G.WF) (hguards : GuardLive G)
    (profile : CommitPolicyProfile G) (restriction : CommitRestriction G)
    (state : ReachableConfig G) (node : Fin G.nodeCount) (hready : Ready G state.1 node)
    (middle : ReachableConfig G)
    (hmiddle : middle ∈ (policyNodeStep hwf hguards profile state node).support)
    (rest : List (Fin G.nodeCount)) (final : ReachableConfig G)
    (hfinal : final ∈ (runPolicyNodes hwf hguards profile middle rest).support)
    (original : CommitPolicyProfile G) :
    (restriction.AllowsStep final.1 node final.1 ↔
      restriction.AllowsStep state.1 node middle.1) ∧
      restriction.factor original final.1 node = restriction.factor original state.1 node := by
  have hstep := step_extends hwf hguards profile state node middle hmiddle
  have htail := run_extends hwf hguards profile middle rest final hfinal
  have hdata := data_of_extends hwf original restriction state final.1 node hready
    (hstep.trans htail)
  have hdone : node ∈ middle.1.done := by
    rw [policyNodeStep_support_done hwf hguards profile state node middle hmiddle,
      if_pos hready]
    exact Finset.mem_insert_self _ _
  have hstore := htail.store (G.nodeTarget node) (by
    intro other hnot
    apply Config.nodeTarget_ne_of_ne
    intro heq
    subst other
    exact hnot hdone)
  exact ⟨by unfold CommitRestriction.AllowsStep; rw [hdata.1, hstore], hdata.2⟩

open Classical in
/-- Legal forced choices give an exact change-of-law identity for the actual
graph executor. The order is any ready order, not necessarily the canonical one.
The identity holds for arbitrary outcome tests and zero-probability restrictions. -/
theorem runPolicyNodes_restriction_expect
    (hwf : G.WF) (hguards : GuardLive G) (profile : CommitPolicyProfile G)
    (restriction : CommitRestriction G) (state : ReachableConfig G)
    (order : List (Fin G.nodeCount)) (horder : G.ReadyOrder state.1.done order)
    (payoff : Config G → ℝ) :
    (runPolicyNodes hwf hguards profile state order).expect
        (fun final => if restriction.Allows order final.1 then payoff final.1 else 0) =
      (runPolicyNodes hwf hguards (restriction.apply profile) state order).expect
        (fun final => restriction.weight profile order final.1 * payoff final.1) := by
  classical
  induction order generalizing state with
  | nil => simp [CommitRestriction.Allows, CommitRestriction.weight]
  | cons node rest ih =>
      have hready : Ready G state.1 node := ⟨horder.1, horder.2.1⟩
      let continuation : Config G → ℝ := fun cfg =>
        if hreach : Reachable G cfg then
          (runPolicyNodes hwf hguards (restriction.apply profile) ⟨cfg, hreach⟩ rest).expect
            (fun final => restriction.weight profile rest final.1 * payoff final.1)
        else 0
      have hcontinuation (cfg : ReachableConfig G) : continuation cfg.1 =
          (runPolicyNodes hwf hguards (restriction.apply profile) cfg rest).expect
            (fun final => restriction.weight profile rest final.1 * payoff final.1) := by
        simp only [continuation, dif_pos cfg.2]
      rw [runPolicyNodes_cons, FinDist.expect_bind, runPolicyNodes_cons, FinDist.expect_bind]
      calc
        _ = (policyNodeStep hwf hguards profile state node).expect
            (fun middle => if restriction.AllowsStep state.1 node middle.1 then
              continuation middle.1 else 0) := by
          apply FinDist.expect_congr
          intro middle hmiddle
          have htailOrder : G.ReadyOrder middle.1.done rest := by
            rw [policyNodeStep_support_done hwf hguards profile state node middle hmiddle,
              if_pos hready]
            exact horder.2.2
          have htail := ih middle htailOrder
          rw [hcontinuation, ← htail]
          by_cases hallow : restriction.AllowsStep state.1 node middle.1
          · rw [if_pos hallow]
            apply FinDist.expect_congr
            intro final hfinal
            have hhead := (restriction_head_retained hwf hguards profile restriction state
              node hready middle hmiddle rest final hfinal profile).1
            simp only [restriction.allows_cons, hhead, hallow, true_and]
          · rw [if_neg hallow]
            calc
              _ = (runPolicyNodes hwf hguards profile middle rest).expect (fun _ => 0) := by
                apply FinDist.expect_congr
                intro final hfinal
                have hhead := (restriction_head_retained hwf hguards profile restriction state
                  node hready middle hmiddle rest final hfinal profile).1
                simp only [restriction.allows_cons, hhead, hallow, false_and, ↓reduceIte]
              _ = _ := FinDist.expect_const _ _
        _ = restriction.factor profile state.1 node *
            (policyNodeStep hwf hguards (restriction.apply profile) state node).expect
              (fun middle => continuation middle.1) :=
          policyNodeStep_restriction_expect hwf hguards profile restriction state node hready
            continuation
        _ = _ := by
          rw [← FinDist.expect_smul]
          apply FinDist.expect_congr
          intro middle hmiddle
          rw [hcontinuation, ← FinDist.expect_smul]
          apply FinDist.expect_congr
          intro final hfinal
          have hfactor := (restriction_head_retained hwf hguards (restriction.apply profile)
            restriction state node hready middle hmiddle rest final hfinal profile).2
          rw [restriction.weight_cons, hfactor]
          exact (mul_assoc _ _ _).symm

/-- The mass of a graph-choice event is the expected original-choice
likelihood under its normalized restricted graph profile. -/
theorem runPolicyNodes_restriction_probability
    (hwf : G.WF) (hguards : GuardLive G) (profile : CommitPolicyProfile G)
    (restriction : CommitRestriction G) (state : ReachableConfig G)
    (order : List (Fin G.nodeCount)) (horder : G.ReadyOrder state.1.done order) :
    (runPolicyNodes hwf hguards profile state order).probOf
        {final | restriction.Allows order final.1} =
      (runPolicyNodes hwf hguards (restriction.apply profile) state order).expect
        (fun final => restriction.weight profile order final.1) := by
  classical
  rw [← FinDist.expect_indicator_eq_probOf]
  simpa only [mul_one, Set.mem_ofPred_eq] using
    runPolicyNodes_restriction_expect hwf hguards profile restriction state order horder
      (fun _ => 1)

theorem runPolicyNodes_restriction_probability_of_constant
    (hwf : G.WF) (hguards : GuardLive G) (profile : CommitPolicyProfile G)
    (restriction : CommitRestriction G) (state : ReachableConfig G)
    (order : List (Fin G.nodeCount)) (horder : G.ReadyOrder state.1.done order) (mass : ℝ)
    (hconstant : ∀ final ∈
      (runPolicyNodes hwf hguards (restriction.apply profile) state order).support,
        restriction.weight profile order final.1 = mass) :
    (runPolicyNodes hwf hguards profile state order).probOf
      {final | restriction.Allows order final.1} = mass := by
  rw [runPolicyNodes_restriction_probability hwf hguards profile restriction state order horder]
  exact (FinDist.expect_congr hconstant).trans (FinDist.expect_const _ _)

end Vegas.EventGraph

/-- info: 'Vegas.EventGraph.runPolicyNodes_restriction_expect'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.runPolicyNodes_restriction_expect

/-- info: 'Vegas.EventGraph.runPolicyNodes_restriction_probability'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.runPolicyNodes_restriction_probability

/-- info: 'Vegas.EventGraph.runPolicyNodes_restriction_support'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.runPolicyNodes_restriction_support
