/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveOccupationValue

/-! # Bellman identity for actual active-control occupation -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)
  (scheduler : app.Scheduler) (players : Principal → app.Policy)
  (reward : app.ProtocolState → ℝ)

/-- Actual environment and response transitions give the additive occupation
identity, without assigning a reward to idle controls or initialization. -/
theorem controlOccupation_bellman (initial : PMF app.State) (horizon : Nat)
    {bound : ℝ} (nonnegative : 0 ≤ bound) (bounded : ∀ state, |reward state| ≤ bound)
    (idle : ∀ remaining execution, reward (some ⟨remaining, none, execution⟩) = 0)
    (unstarted : reward none = 0) (state : app.ProtocolState) :
    app.controlOccupation scheduler players reward initial horizon state = reward state +
      expect (app.controlStep initial horizon scheduler players state)
        (app.controlOccupation scheduler players reward initial horizon) := by
  cases state with
  | none =>
      change expect initial (fun state => app.roundOccupation scheduler players reward horizon
        (Execution.initial app state)) = reward none +
          expect (initial.map fun state => some ⟨horizon, none, Execution.initial app state⟩)
            (app.controlOccupation scheduler players reward initial horizon)
      rw [unstarted, zero_add, expect_map]
      apply expect_congr_on_support
      intro state _
      exact (app.controlOccupation_idle scheduler players reward initial horizon horizon
        (Execution.initial app state) idle).symm
  | some current =>
      rcases current with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          have stepLaw : app.controlStep initial horizon scheduler players
              (some ⟨remaining, some who, execution⟩) =
              (players who (execution.recall who) (execution.observe app who)).map
                fun response => some ⟨remaining, none, execution.respond app who response⟩ := by
            simp only [controlStep, actor, Option.bind_some, transition, ↓reduceIte,
              Option.getD_some]
            exact PMF.bind_pure_comp _ _
          rw [stepLaw]
          simp only [controlOccupation, resume, invoke, expect_map, Function.comp_def, idle,
            expect_pure, zero_add]
      | none =>
          rw [app.controlOccupation_idle scheduler players reward initial horizon remaining
            execution idle, idle, zero_add]
          cases remaining with
          | zero =>
              simp only [controlStep, actor, Option.bind_some, transition, expect_pure,
                controlOccupation, idle, resume, roundOccupation, zero_add]
          | succ remaining =>
              change app.roundOccupation scheduler players reward (remaining + 1) execution =
                expect ((scheduler execution.environmentRecall
                  (execution.observeEnvironment app)).bind fun command =>
                    (execution.environmentStep app command).map fun active =>
                      some ⟨remaining, command.actor? app, active⟩)
                  (app.controlOccupation scheduler players reward initial horizon)
              have integrable : PayoffIntegrable
                  ((scheduler execution.environmentRecall
                    (execution.observeEnvironment app)).bind fun command =>
                      (execution.environmentStep app command).map fun active =>
                        some ⟨remaining, command.actor? app, active⟩)
                  (app.controlOccupation scheduler players reward initial horizon) := by
                apply payoffIntegrable_of_bounded_on_support _ _
                  (C := ((remaining : ℝ) + 1) * bound)
                intro next member
                obtain ⟨command, _, moved⟩ :=
                  Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ member)
                obtain ⟨active, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp moved
                exact app.controlOccupation_abs_le scheduler players reward nonnegative bounded
                  initial horizon ⟨remaining, command.actor? app, active⟩
              rw [expect_bind_tower _ _ _ integrable]
              simp only [expect_map, Function.comp_def, controlOccupation, roundOccupation]

end Interaction.ReactiveApplication
