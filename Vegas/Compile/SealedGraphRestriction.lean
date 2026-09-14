/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedMessages
import Vegas.EventGraph.KernelRestrictionLaw

/-! # Graph restrictions from recorded commitment choices

The backend constrains only selected owners' actual graph commitment sites.
Extra handles do not become graph choices. This construction consumes a graph
fragment certificate, not a source program or a source strategy translation.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} (supported : SealedFragment G ty)

/-- Fix recorded legal graph choices of selected owners. Missing records and
unselected owners retain their original kernels. -/
def recordedChoiceRestriction (selected : Player → Bool)
    (recorded : Player × Nat → Option (L.Val ty)) : CommitRestriction G :=
  fun who node guard hsem reads =>
    if selected who then
      (recorded (who, node.val)).map fun value =>
        ⟨cast (congrArg L.Val (supported.commitType node who guard hsem).symm) value,
          supported.commitGuard node who guard hsem _ reads⟩
    else none

theorem recordedChoiceRestriction_apply_update (selected : Player → Bool) (focal : Player)
    (hunselected : selected focal = false)
    (recorded : Player × Nat → Option (L.Val ty)) (profile : CommitPolicyProfile G)
    (replacement : CommitPolicy G focal) :
    (supported.recordedChoiceRestriction selected recorded).apply
        (Profile.update (sig := ⟨CommitPolicy G, ReachableConfig G⟩) profile focal replacement) =
      Profile.update (sig := ⟨CommitPolicy G, ReachableConfig G⟩)
        ((supported.recordedChoiceRestriction selected recorded).apply profile) focal
        replacement := by
  funext who node guard hsem reads
  by_cases hwho : who = focal
  · subst who
    simp only [CommitRestriction.apply, recordedChoiceRestriction, hunselected,
      Bool.false_eq_true, ↓reduceIte, Profile.update_same]
  · simp only [CommitRestriction.apply, recordedChoiceRestriction,
      Profile.update_of_ne _ _ hwho]

private theorem typed_cast (left right : L.Ty) (hty : left = right) (value : L.Val right) :
    (⟨left, cast (congrArg L.Val hty.symm) value⟩ : TypedValue L) = ⟨right, value⟩ := by
  cases hty
  rfl

private theorem selected_commit (selected : Player → Bool)
    (recorded : Player × Nat → Option (L.Val ty)) (cfg : Config G)
    (who : Player) (node : Fin G.nodeCount) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? cfg.store guard.choiceReads = some reads) :
    (supported.recordedChoiceRestriction selected recorded).selected cfg node =
      (if selected who then recorded (who, node.val) else none).map
        (fun value => (⟨ty, value⟩ : TypedValue L)) := by
  rw [CommitRestriction.selected_commit _ cfg node who guard hsem reads hreads]
  simp only [recordedChoiceRestriction]
  split
  · rw [Option.map_map]
    apply congrArg (fun f => (recorded (who, node.val)).map f)
    funext value
    exact typed_cast _ _ (supported.commitType node who guard hsem) value
  · rfl

include supported in
private theorem terminal_reads (cfg : ReachableConfig G) (hterminal : Terminal G cfg.1)
    (who : Player) (node : Fin G.nodeCount) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard) :
    ∃ reads : ReadEnv L guard.choiceReads,
      ReadEnv.ofStore? cfg.1.store guard.choiceReads = some reads := by
  obtain ⟨row, hrow, hvalid⟩ := reachable_validDoneValues supported.graphWF cfg.2 node
    (hterminal node)
  have hrowEq : row = G.nodeRow node :=
    Option.some.inj (hrow.symm.trans (G.nodes_get?_nodeRow node))
  subst row
  rw [hsem] at hvalid
  obtain ⟨_, _, reads, hreads, _⟩ := hvalid
  exact ⟨reads, hreads⟩

/-- In a complete reachable graph the restriction event is exactly agreement
with recorded values at selected commitment sites. Records at other sites do
not constrain this event. -/
theorem recordedChoiceRestriction_allows_iff_nodeValues
    (selected : Player → Bool) (recorded : Player × Nat → Option (L.Val ty))
    (cfg : ReachableConfig G) (hterminal : Terminal G cfg.1) (fallback : L.Val ty) :
    (supported.recordedChoiceRestriction selected recorded).Allows G.nodeOrder cfg.1 ↔
      ∀ who (node : Fin G.nodeCount) guard,
        (G.nodeRow node).sem = .commit who guard → selected who = true →
        ∀ value, recorded (who, node.val) = some value →
          cfg.1.nodeValues fallback node = value := by
  classical
  constructor
  · intro h who node guard hsem hselected value hlookup
    obtain ⟨reads, hreads⟩ := supported.terminal_reads cfg hterminal who node guard hsem
    have hchoice := h node (by simp) ⟨ty, value⟩ (by
      rw [supported.selected_commit selected recorded cfg.1 who node guard hsem reads hreads]
      simp only [hselected, ↓reduceIte, hlookup, Option.map_some])
    rw [Config.nodeValues, Store.getAs, hchoice]
    simp [TypedValue.as?]
  · intro h node _ fixed hfixed
    cases hsem : (G.nodeRow node).sem with
    | commit who guard =>
        obtain ⟨reads, hreads⟩ := supported.terminal_reads cfg hterminal who node guard hsem
        rw [supported.selected_commit selected recorded cfg.1 who node guard hsem reads hreads]
          at hfixed
        cases hselected : selected who with
        | false => simp [hselected] at hfixed
        | true =>
            cases hlookup : recorded (who, node.val) with
            | none => simp [hselected, hlookup] at hfixed
            | some value =>
                simp only [hselected, ↓reduceIte, hlookup, Option.map_some, Option.some.injEq]
                  at hfixed
                subst fixed
                rw [← h who node guard hsem hselected value hlookup]
                exact cfg.1.store_nodeValues (reachable_storeCoherent supported.graphWF cfg.2)
                  fallback node (supported.rowType node) (hterminal node)
    | sample dist => exact (supported.noSamples node dist hsem).elim
    | reveal source =>
        rw [CommitRestriction.selected_internal _ _ _
          (by simp [hsem, NodeSem.isInternal])] at hfixed
        cases hfixed

end Vegas.EventGraph.SealedFragment
