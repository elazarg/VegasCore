/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMixtureAtoms

/-! # An unread original plan coordinate with arbitrary extra private memory -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

/-- An original independent plan coordinate unread by actual response atoms
retains its weight independently of all other coordinates and arbitrary extra
private memory. The extra memory is not reset during the posterior update. -/
theorem policyMixture_posterior_coordinate_extra {Pool Other : Type}
    [Fintype Pool] [DecidableEq Pool] {Part : Pool → Type}
    (weights : (pool : Pool) → PMF (Part pool)) (otherLaw : PMF Other)
    (members : ((pool : Pool) → Part pool) × Other → app.Policy) (selected : Pool)
    (past : List app.PlayerEntry)
    (unread : ∀ (before : List app.PlayerEntry) (entry : app.PlayerEntry),
      before ++ [entry] <+: past → ∀ plan other part,
        members (Function.update plan selected part, other) before entry.beforeView entry.action =
          members (plan, other) before entry.beforeView entry.action) :
    let original := (independentProduct weights).bind fun plan => otherLaw.map (Prod.mk plan)
    ∃ remainder : PMF (((pool : {pool // pool ≠ selected}) → Part pool.val) × Other),
      ((app.policyMixture original members).posterior past).map
          (fun memory => (memory.1 selected,
            (fun pool : {pool // pool ≠ selected} => memory.1 pool.val, memory.2))) =
        (weights selected).bind (fun part => remainder.map (Prod.mk part)) := by
  classical
  intro original
  let split := Equiv.piSplitAt selected Part
  let read := fun memory : ((pool : Pool) → Part pool) × Other =>
    ((split memory.1).1, ((split memory.1).2, memory.2))
  let restore := fun pair : Part selected ×
      (((pool : {pool // pool ≠ selected}) → Part pool.val) × Other) =>
    (split.symm (pair.1, pair.2.1), pair.2.2)
  let restPlans := independentProduct (fun pool : {pool // pool ≠ selected} => weights pool.val)
  let restLaw := restPlans.bind fun rest => otherLaw.map (Prod.mk rest)
  let reference := (weights selected).support_nonempty.choose
  let pairMembers := fun pair => members (restore pair)
  let remaining := fun rest => pairMembers (reference, rest)
  have splitLaw : original.map read =
      (weights selected).bind (fun part => restLaw.map (Prod.mk part)) := by
    change ((independentProduct weights).bind fun plan => otherLaw.map (Prod.mk plan)).map read = _
    rw [independentProduct_splitAt weights selected]
    simp only [PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
      read, split, Equiv.apply_symm_apply, restLaw, restPlans]
  have restored (memory : ((pool : Pool) → Part pool) × Other) :
      restore (read memory) = memory := by
    apply Prod.ext
    · change split.symm (split memory.1) = memory.1
      exact split.symm_apply_apply _
    · rfl
  have familyEq : (fun memory => pairMembers (read memory)) = members := by
    funext memory
    exact congrArg members (restored memory)
  have transported := app.policyMixture_posterior_map original read pairMembers past
  rw [familyEq, splitLaw] at transported
  refine ⟨(app.policyMixture restLaw remaining).posterior past, ?_⟩
  change ((app.policyMixture original members).posterior past).map read = _
  apply transported.trans
  apply app.policyMixture_posterior_independent_left_atoms (weights selected) restLaw pairMembers
    remaining past
  intro before entry recorded part rest
  have updated : split.symm (part, rest.1) =
      Function.update (split.symm (reference, rest.1)) selected part := by
    funext pool
    by_cases equal : pool = selected
    · subst pool
      simp [split, Equiv.piSplitAt]
    · simp [split, Equiv.piSplitAt, equal]
  change members (split.symm (part, rest.1), rest.2) before entry.beforeView entry.action =
    members (split.symm (reference, rest.1), rest.2) before entry.beforeView entry.action
  rw [updated]
  exact unread before entry recorded _ _ part

end Interaction.ReactiveApplication
