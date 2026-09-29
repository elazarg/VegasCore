/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ParameterOutcomes
import Vegas.Expr.Simple

/-! # Public marginals do not determine private-type utilities

A player copies or negates a persistent private bit into a public report.
The input has no reveal site. The public laws agree, while the joint laws yield
guessing utility one and zero. This checks the need for the joint observation
and that its initial component is the actual retained input.
-/

noncomputable section

namespace Vegas.Examples.ParameterOutcomes

open Vegas Vegas.SourceProgram GameTheory GameTheory.Math.Probability

private abbrev initialCtx : SourceCtx Unit simpleExpr := [(0, .privateInput () .bool)]

private def guard : SourceGuard simpleExpr initialCtx () 1 .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by decide
  code := .constBool true
  reads := fun h => nomatch h

private def program : SourceProgram Unit simpleExpr initialCtx ∅ :=
  .commit 1 () (by decide) guard <|
  .reveal 2 () 1 (by decide) .here (by decide) <|
  .ret []

private def initial (bit : Bool) : State simpleExpr initialCtx :=
  Env.cons bit (Env.empty (CellVal simpleExpr))

private def setup : Setup (Player := Unit) (L := simpleExpr) where
  context := initialCtx
  namesNodup := by decide
  initialLaw := mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure (initial false)) (PMF.pure (initial true))
  obligations := ∅
  program := program
  accounts := rfl

private def parameter (state : State simpleExpr setup.context) : Bool :=
  state.get .here

private def policy (invert : Bool) : BehavioralPolicy () program :=
  (fun _ view =>
    let bit := match view.1.cells.get .here with
      | some bit => bit
      | _ => false
    PMF.pure (.success (if invert then !bit else bit)),
    (fun _ _ => PMF.pure true, PUnit.unit))

private def profile (invert : Bool) : BehavioralProfile program := fun _ => policy invert

private def result (bit : Bool) : PublicOutcome program :=
  Env.cons (.success bit) (Env.empty simpleExpr.Val)

private theorem publicRun_initial (invert bit : Bool) :
    (program.run (profile invert) (initial bit)).map (publicOutcome program) =
      PMF.pure (result (if invert then !bit else bit)) := by
  cases invert <;> cases bit <;>
    simp only [SourceProgram.run, program, profile, policy, initial, runWith,
      commitKernel, revealKernel, afterCommit, PMF.pure_bind,
      PMF.pure_map] <;> rfl

private theorem parameterRun_law (invert : Bool) :
    setup.parameterRun parameter (profile invert) =
      mix (1 / 2) (by norm_num) (by norm_num)
        (PMF.pure (false, result (if invert then true else false)))
        (PMF.pure (true, result (if invert then false else true))) := by
  unfold Setup.parameterRun
  rw [show setup.initialLaw = mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure (initial false)) (PMF.pure (initial true)) from rfl]
  rw [mix_bind, PMF.pure_bind, PMF.pure_bind]
  have mapped (bit : Bool) := congrArg (PMF.map fun outcome => (bit, outcome))
    (publicRun_initial invert bit)
  simp only [PMF.map_comp, Function.comp_def, PMF.pure_map] at mapped
  change mix _ _ _ _ _ = _
  dsimp only [setup]
  rw [show parameter (initial false) = false from rfl,
    show parameter (initial true) = true from rfl, mapped false, mapped true]
  rfl

private def guessingUtility (outcome : Bool × PublicOutcome program) : ℝ :=
  match (outcome.2.get .here : PublicationResult Bool) with
  | .failure => 0
  | .success bit => if bit = outcome.1 then 1 else 0

/-- Copying and negating have the same public marginal. -/
theorem public_marginals_equal : setup.publicRun (profile false) =
    setup.publicRun (profile true) := by
  rw [← setup.parameterRun_map_snd parameter, ← setup.parameterRun_map_snd parameter]
  simp only [parameterRun_law, ← PMF.bind_pure_comp, Function.comp_def, mix_bind,
    PMF.pure_bind, Bool.false_eq_true, ↓reduceIte]
  ext outcome
  rw [mix_apply, mix_apply]
  norm_num
  ring

/-- The correct joint interpretation assigns payoff one to copying. -/
theorem copying_utility :
    expect (setup.parameterRun parameter (profile false)) guessingUtility = 1 := by
  rw [parameterRun_law, expect_mix _ _ _ _ _ _ (payoffIntegrable_pure _ _)
    (payoffIntegrable_pure _ _), expect_pure, expect_pure]
  norm_num [guessingUtility, result, Env.get, Env.cons]

/-- The same public marginal can give payoff zero when correlation is reversed. -/
theorem negating_utility :
    expect (setup.parameterRun parameter (profile true)) guessingUtility = 0 := by
  rw [parameterRun_law, expect_mix _ _ _ _ _ _ (payoffIntegrable_pure _ _)
    (payoffIntegrable_pure _ _), expect_pure, expect_pure]
  norm_num [guessingUtility, result, Env.get, Env.cons]

/-- In particular, the terminal-store readout recovers the joint law, not the
product of its marginals. -/
example :
    expect ((setup.run (profile false)).map (setup.parameterOutcome parameter))
      guessingUtility = 1 := by
  rw [setup.run_map_parameterOutcome, copying_utility]

end Vegas.Examples.ParameterOutcomes
