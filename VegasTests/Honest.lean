/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Honest
import Vegas.Expr.Simple

/-! # Regression for honest completion

`GuardsAccept` is a premise, so the result is worth nothing unless the premise
can hold. Here it does: one commitment, one reveal, and a guard that accepts,
and the conclusion is that nothing in the terminal state records a failure.
-/

namespace VegasTests.Honest

open Vegas Vegas.SourceProgram GameTheory.Math.Probability

noncomputable section

private abbrev bid : VarId := 0
private abbrev bidOut : VarId := 1

/-- A guard that accepts every opening. -/
private def openGuard : SourceGuard (Player := Unit) simpleExpr [] () bid .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by decide
  code := .constBool true
  reads := fun h => nomatch h

private def program : SourceProgram Unit simpleExpr [] ∅ :=
  .commit bid () (by decide) openGuard <|
  .reveal bidOut () bid (by decide) .here (by decide) <|
  .ret [((), .ite (.isFailure (.var bidOut .here)) (.constInt 0) (.constInt 1))]

/-- Bind a value and open it. -/
private def honestPolicy : BehavioralPolicy (who := ()) program :=
  (fun _ _ => FinDist.pure (.success false), fun _ _ => FinDist.pure true, PUnit.unit)

example : Honest program honestPolicy :=
  ⟨⟨fun _ _ => by simp [honestPolicy], trivial⟩,
    ⟨fun _ _ => by simp [honestPolicy], trivial⟩⟩


/-- The premise is satisfiable: this program's only retained guard accepts. -/
private theorem guardsAccept : GuardsAccept program [] (Revelations.initial []) := by
  refine ⟨fun state _ value _ => ?_, trivial⟩
  refine List.all_eq_true.mpr fun obligation member => ?_
  obtain ⟨original, hfilter, rfl⟩ := List.mem_map.mp member
  obtain ⟨hmem, _⟩ := List.mem_filter.mp hfilter
  rcases List.mem_cons.mp hmem with rfl | hnil
  · refine Obligation.accepts_of_compatible _ _ _ value
      (fun _ _ h _ => match h with | .here => value) (fun _ => rfl) ?_ (fun h => nomatch h) rfl
    intro published hpublished
    simpa [Obligation.weaken, Revelation.result] using hpublished.symm
  · simp [Registry.weaken] at hnil

/-- So nothing in the terminal state records a failure. -/
example : ∀ terminal ∈ (program.run (fun _ => honestPolicy)
    (Env.empty (CellVal simpleExpr))).support, Successful terminal :=
  run_successful program (fun _ => honestPolicy)
    (fun _ => ⟨⟨fun _ _ => by simp [honestPolicy], trivial⟩,
      ⟨fun _ _ => by simp [honestPolicy], trivial⟩⟩) guardsAccept
    (Env.empty (CellVal simpleExpr)) successful_empty

/-- And the publication carries the value, so the program pays. -/
example :
    (program.run (fun _ => honestPolicy) (Env.empty (CellVal simpleExpr))).map
      program.evaluatePayoffs = FinDist.pure [((), 1)] := by
  simp only [SourceProgram.run, program, honestPolicy, SourceProgram.runWith,
    SourceProgram.commitKernel, SourceProgram.revealKernel, SourceProgram.afterCommit,
    FinDist.pure_bind, FinDist.map_pure]
  rfl

end

end VegasTests.Honest
