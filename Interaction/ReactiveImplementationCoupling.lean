/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveImplementation
import GameTheoryExtensions.Math.Probability.Support

/-! # Finite coupling of the actual round and private joint evaluators

An indexed relation and an actual one-round coupling compose through the
existing evaluators. Each step receives real prefix support on both marginals;
no additional runner or implementation state is introduced.
-/

noncomputable section

namespace Interaction.ReactiveApplication.Implementation

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal]
  {app : ReactiveApplication Principal} {Memory : Type}

/-- Actual one-round couplings compose into exact full evaluator marginals.
The indexed support relation can retain a real checkpoint and its subsequent
actual tail rather than assuming that the paths stay related after an exit. -/
theorem runJoint_coupling
    (implementation : app.Implementation Memory) (who : Principal)
    (players : Principal → app.Policy) (scheduler : app.Scheduler)
    (original repaired : app.Execution) (memory : Memory)
    (relation : Nat → app.Execution × app.Execution × Memory → Prop)
    (seed : relation 0 (original, repaired, memory)) (count : Nat)
    (step : ∀ index < count, ∀ next : app.Execution × app.Execution × Memory,
      next.1 ∈ (app.runRounds scheduler players index original).support →
      next.2 ∈ (implementation.runJoint who players scheduler index repaired memory).support →
      relation index next →
      ∃ coupling : PMF (app.Execution × app.Execution × Memory),
        coupling.map Prod.fst = app.round scheduler players next.1 ∧
        coupling.map Prod.snd = implementation.round who players scheduler next.2.1 next.2.2 ∧
        ∀ after ∈ coupling.support, relation (index + 1) after) :
    ∃ coupling : PMF (app.Execution × app.Execution × Memory),
      coupling.map Prod.fst = app.runRounds scheduler players count original ∧
      coupling.map Prod.snd = implementation.runJoint who players scheduler count repaired
        memory ∧
      ∀ next ∈ coupling.support, relation count next := by
  classical
  induction count with
  | zero =>
      refine ⟨PMF.pure (original, repaired, memory), PMF.pure_map .., PMF.pure_map .., ?_⟩
      intro next supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact seed
  | succ count ih =>
      obtain ⟨joint, first, second, related⟩ :=
        ih (fun index before => step index (Nat.lt_succ_of_lt before))
      have leftSupport next (member : next ∈ joint.support) :
          next.1 ∈ (app.runRounds scheduler players count original).support := by
        rw [← first, PMF.support_map]
        exact ⟨next, member, rfl⟩
      have rightSupport next (member : next ∈ joint.support) :
          next.2 ∈ (implementation.runJoint who players scheduler count repaired memory).support :=
        by rw [← second, PMF.support_map]; exact ⟨next, member, rfl⟩
      have existsStep next (member : next ∈ joint.support) :=
        step count (Nat.lt_succ_self _) next (leftSupport next member)
          (rightSupport next member) (related next member)
      let advance := fun next member => (existsStep next member).choose
      refine ⟨joint.bindOnSupport advance, ?_, ?_, ?_⟩
      · rw [map_bindOnSupport]
        calc
          _ = joint.bind (fun next => app.round scheduler players next.1) := by
            apply bindOnSupport_eq_bind_of_eq_on_support _
            intro next member
            exact (existsStep next member).choose_spec.1
          _ = (joint.map Prod.fst).bind (app.round scheduler players) := by
            rw [PMF.bind_map]; rfl
          _ = _ := by
            rw [first, app.runRounds_add]
            simp only [ReactiveApplication.runRounds, PMF.bind_pure]
      · rw [map_bindOnSupport]
        calc
          _ = joint.bind (fun next => implementation.round who players scheduler next.2.1
              next.2.2) := by
            apply bindOnSupport_eq_bind_of_eq_on_support _
            intro next member
            exact (existsStep next member).choose_spec.2.1
          _ = (joint.map Prod.snd).bind (fun next => implementation.round who players scheduler
              next.1 next.2) := by rw [PMF.bind_map]; rfl
          _ = _ := by
            rw [second, Implementation.runJoint_add]
            simp only [Implementation.runJoint, Prod.mk.eta, PMF.bind_pure]
      · intro final member
        obtain ⟨next, chosen, reached⟩ :=
          Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ member)
        exact (existsStep next chosen).choose_spec.2.2 final reached

end Interaction.ReactiveApplication.Implementation
