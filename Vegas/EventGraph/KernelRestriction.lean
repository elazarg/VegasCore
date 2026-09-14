/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.KernelRealization

/-! # Legal restrictions of declared-read graph policies

A restriction forces selected legal commitment choices and retains all other
kernels. Its inputs are exactly those of a graph policy. The local likelihood
identity is about the actual graph executor, including choices of zero original
probability. It does not use source syntax or a second execution semantics.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} {G : Graph Player L}

/-- Optional legal values at ordinary declared-read policy inputs. Forcing a
nullable value is `some` of that value; the outer `none` leaves the kernel alone. -/
@[reducible] def CommitRestriction (G : Graph Player L) :=
  ∀ (who : Player) (node : Fin G.nodeCount) (guard : EventGuard L),
    (G.nodeRow node).sem = .commit who guard →
      (reads : ReadEnv L guard.choiceReads) →
        Option {value : L.Val guard.ty // guard.eval value reads = true}

namespace CommitRestriction

/-- The reference profile is an ordinary graph profile with legal forced
choices. Unselected decisions keep their entire original kernel. -/
def apply (restriction : CommitRestriction G) (profile : CommitPolicyProfile G) :
    CommitPolicyProfile G :=
  fun who node guard hsem reads =>
    match restriction who node guard hsem reads with
    | none => profile who node guard hsem reads
    | some fixed => FinDist.pure fixed

/-- Query a restriction from a graph store. Missing reads do not manufacture
a choice; at a ready commitment all declared reads exist. -/
def selected (restriction : CommitRestriction G) (cfg : Config G)
    (node : Fin G.nodeCount) : Option (TypedValue L) :=
  match hsem : (G.nodeRow node).sem with
  | .commit who guard =>
      (ReadEnv.ofStore? cfg.store guard.choiceReads).bind fun reads =>
        (restriction who node guard hsem reads).map fun fixed => ⟨guard.ty, fixed.1⟩
  | _ => none

/-- Original conditional mass of a forced choice, or one when no choice is
forced. Unrestricted chance nodes therefore need no likelihood correction. -/
def factor (restriction : CommitRestriction G) (profile : CommitPolicyProfile G)
    (cfg : Config G) (node : Fin G.nodeCount) : ℝ :=
  match hsem : (G.nodeRow node).sem with
  | .commit who guard =>
      match ReadEnv.ofStore? cfg.store guard.choiceReads with
      | none => 1
      | some reads =>
          match restriction who node guard hsem reads with
          | none => 1
          | some fixed => (profile who node guard hsem reads).prob fixed
  | _ => 1

/-- Agreement with the choice selected at the pre-step declared inputs. -/
def AllowsStep (restriction : CommitRestriction G) (cfg : Config G)
    (node : Fin G.nodeCount) (next : Config G) : Prop :=
  ∀ fixed, restriction.selected cfg node = some fixed →
    next.store (G.nodeTarget node) = some fixed

theorem selected_commit (restriction : CommitRestriction G) (cfg : Config G)
    (node : Fin G.nodeCount) (who : Player) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? cfg.store guard.choiceReads = some reads) :
    restriction.selected cfg node =
      (restriction who node guard hsem reads).map fun fixed => ⟨guard.ty, fixed.1⟩ := by
  unfold selected
  split
  next actor test htest =>
    obtain ⟨rfl, rfl⟩ := NodeSem.commit.inj (htest.symm.trans hsem)
    simp only [hreads, Option.bind_some]
  next hnot => exact (hnot who guard hsem).elim

theorem factor_commit (restriction : CommitRestriction G) (profile : CommitPolicyProfile G)
    (cfg : Config G) (node : Fin G.nodeCount) (who : Player) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? cfg.store guard.choiceReads = some reads) :
    restriction.factor profile cfg node =
      match restriction who node guard hsem reads with
      | none => 1
      | some fixed => (profile who node guard hsem reads).prob fixed := by
  unfold factor
  split
  next actor test htest =>
    obtain ⟨rfl, rfl⟩ := NodeSem.commit.inj (htest.symm.trans hsem)
    simp only [hreads]
  next hnot => exact (hnot who guard hsem).elim

theorem selected_internal (restriction : CommitRestriction G) (cfg : Config G)
    (node : Fin G.nodeCount) (hinternal : NodeSem.isInternal (G.nodeRow node).sem = true) :
    restriction.selected cfg node = none := by
  unfold selected
  split
  next who guard hsem => simp [hsem, NodeSem.isInternal] at hinternal
  next => rfl

theorem factor_internal (restriction : CommitRestriction G) (profile : CommitPolicyProfile G)
    (cfg : Config G) (node : Fin G.nodeCount)
    (hinternal : NodeSem.isInternal (G.nodeRow node).sem = true) :
    restriction.factor profile cfg node = 1 := by
  unfold factor
  split
  next who guard hsem => simp [hsem, NodeSem.isInternal] at hinternal
  next => rfl

end CommitRestriction

variable [Fintype Player]

theorem map_val_policyNodeStep_of_commitKernel
    (hwf : G.WF) (hguards : GuardLive G) (profile : CommitPolicyProfile G)
    (state : ReachableConfig G) (node : Fin G.nodeCount) (hready : Ready G state.1 node)
    (who : Player) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? state.1.store guard.choiceReads = some reads) :
    (policyNodeStep hwf hguards profile state node).map Subtype.val =
      (profile who node guard hsem reads).map fun choice =>
        state.1.completeNode node ⟨guard.ty, choice.1⟩ := by
  rw [map_val_policyNodeStep_of_ready hwf hguards profile state node hready]
  simpa only [FinDist.map_comp, Function.comp_def] using
    congrArg (fun law => law.map (state.1.completeNode node))
      (map_written_policyValueLaw_of_commitKernel hwf hguards profile state node hready
        who guard hsem reads hreads)

theorem map_val_policyNodeStep_of_internal
    (hwf : G.WF) (hguards : GuardLive G) (profile : CommitPolicyProfile G)
    (state : ReachableConfig G) (node : Fin G.nodeCount) (hready : Ready G state.1 node)
    (hinternal : NodeSem.isInternal (G.nodeRow node).sem = true) :
    (policyNodeStep hwf hguards profile state node).map Subtype.val =
      (readyEvent hwf hguards state node hready).writeLaw.map (state.1.completeNode node) := by
  rw [map_val_policyNodeStep_of_ready hwf hguards profile state node hready]
  simpa only [FinDist.map_comp, Function.comp_def] using
    congrArg (fun law => law.map (state.1.completeNode node))
      (map_written_policyValueLaw_of_internal hwf hguards profile state node hready hinternal)

open Classical in
/-- Forcing one legal commitment amounts to restricting its actual transition
and multiplying by the original choice mass. This includes zero-mass choices. -/
theorem policyNodeStep_restriction_expect
    (hwf : G.WF) (hguards : GuardLive G) (profile : CommitPolicyProfile G)
    (restriction : CommitRestriction G) (state : ReachableConfig G)
    (node : Fin G.nodeCount) (hready : Ready G state.1 node) (payoff : Config G → ℝ) :
    (policyNodeStep hwf hguards profile state node).expect
        (fun next => if restriction.AllowsStep state.1 node next.1 then payoff next.1 else 0) =
      restriction.factor profile state.1 node *
        (policyNodeStep hwf hguards (restriction.apply profile) state node).expect
          (fun next => payoff next.1) := by
  classical
  rw [← FinDist.expect_map Subtype.val _ (fun cfg : Config G =>
    if restriction.AllowsStep state.1 node cfg then payoff cfg else 0),
    ← FinDist.expect_map Subtype.val _ payoff]
  by_cases hinternal : NodeSem.isInternal (G.nodeRow node).sem = true
  · simp only [CommitRestriction.AllowsStep, restriction.selected_internal _ _ hinternal,
      reduceCtorEq, false_implies, implies_true, ↓reduceIte,
      restriction.factor_internal _ _ _ hinternal, one_mul]
    rw [map_val_policyNodeStep_of_internal hwf hguards profile state node hready hinternal,
      map_val_policyNodeStep_of_internal hwf hguards (restriction.apply profile)
        state node hready hinternal]
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
    rw [map_val_policyNodeStep_of_commitKernel hwf hguards profile state node hready
      who guard hsem reads hreads,
      map_val_policyNodeStep_of_commitKernel hwf hguards (restriction.apply profile)
        state node hready who guard hsem reads hreads,
      restriction.factor_commit profile state.1 node who guard hsem reads hreads]
    simp only [FinDist.expect_map, CommitRestriction.AllowsStep,
      restriction.selected_commit state.1 node who guard hsem reads hreads,
      CommitRestriction.apply]
    cases hfixed : restriction who node guard hsem reads with
    | none => simp
    | some fixed =>
        simp only [Option.map_some, Option.some.injEq, forall_eq',
          FinDist.expect_pure]
        have hselect : ∀ choice : {value : L.Val guard.ty // guard.eval value reads = true},
            (state.1.completeNode node ⟨guard.ty, choice.1⟩).store (G.nodeTarget node) =
              some (⟨guard.ty, fixed.1⟩ : TypedValue L) ↔ fixed = choice := by
          intro choice
          simp only [Config.completeNode, Store.set_eq, Option.some.injEq]
          constructor
          · intro heq
            apply Subtype.ext
            have hval := congrArg (fun v : TypedValue L => v.as? guard.ty) heq
            simpa [TypedValue.as?] using hval.symm
          · rintro rfl
            rfl
        simp only [hselect]
        calc
          _ = (profile who node guard hsem reads).expect
              (fun choice => if fixed = choice then
                payoff (state.1.completeNode node ⟨guard.ty, fixed.1⟩) else 0) := by
            apply FinDist.expect_congr
            intro choice _
            split_ifs with heq
            · subst choice; rfl
            · rfl
          _ = _ := FinDist.expect_ite_eq _ _ _

end Vegas.EventGraph
