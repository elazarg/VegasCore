/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Honest
import Vegas.Expr.Simple

/-! # Regression for honest completion

The guard here checks something: it accepts only a `true` opening. That is the
case a premise quantified over every failure-free state would get wrong, since
the state binding `false` is failure-free and no honest profile below produces
it. Both directions are checked — the premise holds for the profile that binds
`true`, and fails for the one that binds `false`.
-/

namespace VegasTests.Honest

open Vegas Vegas.SourceProgram GameTheory.Math.Probability

noncomputable section

private abbrev bid : VarId := 0
private abbrev bidOut : VarId := 1

/-- A guard that accepts only a `true` opening. -/
private def trueGuard : SourceGuard (Player := Unit) simpleExpr [] () bid .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by decide
  code := .var bid .here
  reads := fun h => nomatch h

private def program : SourceProgram Unit simpleExpr [] ∅ :=
  .commit bid () (by decide) trueGuard <|
  .reveal bidOut () bid (by decide) .here (by decide) <|
  .ret [((), .ite (.isFailure (.var bidOut .here)) (.constInt 0) (.constInt 1))]

/-- Bind the value the guard accepts, and open it. -/
private def honestPolicy : BehavioralPolicy (who := ()) program :=
  (fun _ _ => FinDist.pure (.success true), fun _ _ => FinDist.pure true, PUnit.unit)

/-- Bind the value the guard rejects, and open it. Still honest: honesty is
about binding a value and opening it, not about what the guard says. -/
private def rejectedPolicy : BehavioralPolicy (who := ()) program :=
  (fun _ _ => FinDist.pure (.success false), fun _ _ => FinDist.pure true, PUnit.unit)

private def start : Config Unit simpleExpr [] :=
  ⟨Env.empty (CellVal simpleExpr), [], Revelations.initial [], fun _ => []⟩

example : Honest program honestPolicy :=
  ⟨⟨fun _ _ => by simp [honestPolicy], trivial⟩,
    ⟨fun _ _ => by simp [honestPolicy], trivial⟩⟩

example : Honest program rejectedPolicy :=
  ⟨⟨fun _ _ => by simp [rejectedPolicy], trivial⟩,
    ⟨fun _ _ => by simp [rejectedPolicy], trivial⟩⟩

/-- The premise holds for the profile that binds what the guard accepts. -/
private theorem guardsAccept :
    GuardsAcceptFrom program (fun _ => honestPolicy) start := by
  intro choice choiceMember
  simp only [GuardsAcceptFrom, SourceProgram.commitKernel, honestPolicy,
    FinDist.mem_support_pure] at choiceMember ⊢
  subst choiceMember
  refine ⟨fun value bound => ?_, fun disclose _ => trivial⟩
  simp only [commitSuccessor, Env.cons_get_here] at bound
  obtain rfl : true = value := by injection bound
  refine List.all_eq_true.mpr fun obligation member => ?_
  obtain ⟨original, filtered, rfl⟩ := List.mem_map.mp member
  obtain ⟨inList, _⟩ := List.mem_filter.mp filtered
  rcases List.mem_cons.mp inList with rfl | empty
  · refine Obligation.accepts_of_compatible _ _ _ true
      (fun _ _ h _ => match h with | .here => true) (fun _ => rfl) ?_ (fun h => nomatch h) rfl
    intro published publishedEq
    simpa [Obligation.weaken, Revelation.result] using publishedEq.symm
  · simp [start, Registry.weaken] at empty

/-- So the honest run records no failure anywhere. -/
example : ∀ terminal ∈ (program.run (fun _ => honestPolicy)
    (Env.empty (CellVal simpleExpr))).support, Successful terminal :=
  run_successful program (fun _ => honestPolicy)
    (fun _ => ⟨⟨fun _ _ => by simp [honestPolicy], trivial⟩,
      ⟨fun _ _ => by simp [honestPolicy], trivial⟩⟩)
    (Env.empty (CellVal simpleExpr)) successful_empty guardsAccept

/-- And it pays, because the publication carries the value. -/
example :
    (program.run (fun _ => honestPolicy) (Env.empty (CellVal simpleExpr))).map
      program.evaluatePayoffs = FinDist.pure [((), 1)] := by
  simp only [SourceProgram.run, program, honestPolicy, SourceProgram.runWith,
    SourceProgram.commitKernel, SourceProgram.revealKernel, SourceProgram.afterCommit,
    FinDist.pure_bind, FinDist.map_pure]
  rfl

/-- The premise has content: it fails for the equally honest profile that binds
what the guard rejects, whose publication does fail. -/
example : ¬ GuardsAcceptFrom program (fun _ => rejectedPolicy) start := by
  intro guards
  have applied := (guards (.success false) (by
    simp [SourceProgram.commitKernel, rejectedPolicy])).1 false rfl
  simp +decide at applied

example :
    (program.run (fun _ => rejectedPolicy) (Env.empty (CellVal simpleExpr))).map
      program.evaluatePayoffs = FinDist.pure [((), 0)] := by
  simp only [SourceProgram.run, program, rejectedPolicy, SourceProgram.runWith,
    SourceProgram.commitKernel, SourceProgram.revealKernel, SourceProgram.afterCommit,
    FinDist.pure_bind, FinDist.map_pure]
  rfl

end

end VegasTests.Honest
