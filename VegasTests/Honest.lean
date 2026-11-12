module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Source.Honest
public import Vegas.Expr.Simple

@[expose] public section

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

abbrev bid : VarId := 0
abbrev bidOut : VarId := 1

/-- A guard that accepts only a `true` opening. -/
def trueGuard : SourceGuard (Player := Unit) simpleExpr [] () bid .bool where
  schema := []
  schemaNames := by decide
  subjectFresh := by decide
  code := .var bid .here
  reads := fun h => nomatch h

def program : SourceProgram Unit simpleExpr [] ∅ :=
  .commit bid () (by decide) trueGuard <|
  .reveal bidOut () bid (by decide) .here (by decide) <|
  .ret [((), .ite (.isFailure (.var bidOut .here)) (.constInt 0) (.constInt 1))]

/-- Bind the value the guard accepts, and open it. -/
def honestPolicy : BehavioralPolicy (who := ()) program :=
  (fun _ _ _ => PMF.pure (some (.success true)), fun _ _ _ => PMF.pure true, PUnit.unit)

/-- Bind the value the guard rejects, and open it. Still honest: honesty is
about binding a value and opening it, not about what the guard says. -/
def rejectedPolicy : BehavioralPolicy (who := ()) program :=
  (fun _ _ _ => PMF.pure (some (.success false)), fun _ _ _ => PMF.pure true, PUnit.unit)

def start : Config Unit simpleExpr [] :=
  Config.initial (Env.empty (CellVal simpleExpr))

private theorem honestPolicy_honest : Honest program honestPolicy := by
  refine ⟨?_, ?_, trivial⟩
  · intro _ _ _ choice supported
    exact ⟨true, (PMF.mem_support_pure_iff _ _).mp supported⟩
  · intro _ _ _
    simp [honestPolicy]

private theorem rejectedPolicy_honest : Honest program rejectedPolicy := by
  refine ⟨?_, ?_, trivial⟩
  · intro _ _ _ choice supported
    exact ⟨false, (PMF.mem_support_pure_iff _ _).mp supported⟩
  · intro _ _ _
    simp [rejectedPolicy]

example : Honest program honestPolicy := honestPolicy_honest

example : Honest program rejectedPolicy := rejectedPolicy_honest

/-- The premise holds for the profile that binds what the guard accepts. -/
private theorem guardsAccept :
    GuardsAcceptFrom program (fun _ => honestPolicy) start := by
  intro choice choiceMember
  have chosen : choice = some (.success true) := by
    simpa [SourceProgram.commitKernel, honestPolicy, start, Config.initial,
      Config.defaulted, DefaultHistory.defaulted] using choiceMember
  subst choice
  refine ⟨fun value bound => ?_, fun disclose _ => trivial⟩
  simp only [commitSuccessor, start, Config.initial, Config.defaulted,
    DefaultHistory.defaulted, List.filterMap_nil, List.toFinset_nil, Finset.notMem_empty,
    ite_false, Option.getD_some, Env.cons_get_here] at bound
  obtain rfl : true = value := by injection bound
  refine List.all_eq_true.mpr fun obligation member => ?_
  obtain ⟨original, filtered, rfl⟩ := List.mem_map.mp member
  obtain ⟨inList, _⟩ := List.mem_filter.mp filtered
  rcases List.mem_cons.mp inList with rfl | empty
  · refine Obligation.accepts_of_compatible _ _ _ true
      (fun _ _ h _ => match h with | .here => true) (fun _ => rfl) ?_ (fun h => nomatch h) rfl
    intro published publishedEq
    simpa [Obligation.weaken, Revelation.result] using publishedEq.symm
  · simp [start, Config.initial, Registry.weaken] at empty

/-- So the honest run records no failure anywhere. -/
example : ∀ terminal ∈ (program.run (fun _ => honestPolicy)
    (Env.empty (CellVal simpleExpr))).support, Successful terminal.state ∧ terminal.defaulted = ∅ :=
  run_successful program (fun _ => honestPolicy)
    (fun _ => honestPolicy_honest)
    (Env.empty (CellVal simpleExpr)) successful_empty guardsAccept

/-- And it pays, because the publication carries the value. -/
example :
    (program.run (fun _ => honestPolicy) (Env.empty (CellVal simpleExpr))).map
      (fun terminal => program.evaluatePayoffs terminal.state) = PMF.pure [((), 1)] := by
  simp [SourceProgram.run, program, honestPolicy, SourceProgram.runFrom,
    SourceProgram.commitKernel, SourceProgram.revealKernel, SourceProgram.afterCommit,
    Config.initial, Config.defaulted, DefaultHistory.defaulted, DefaultHistory.record,
    commitSuccessor, PMF.pure_map]
  rfl

/-- The premise has content: it fails for the equally honest profile that binds
what the guard rejects, whose publication does fail. -/
example : ¬ GuardsAcceptFrom program (fun _ => rejectedPolicy) start := by
  intro guards
  have applied := (guards (some (.success false)) (by
    simp [SourceProgram.commitKernel, rejectedPolicy, start, Config.initial,
      Config.defaulted, DefaultHistory.defaulted])).1 false rfl
  simp +decide at applied

example :
    (program.run (fun _ => rejectedPolicy) (Env.empty (CellVal simpleExpr))).map
      (fun terminal => program.evaluatePayoffs terminal.state) = PMF.pure [((), 0)] := by
  simp [SourceProgram.run, program, rejectedPolicy, SourceProgram.runFrom,
    SourceProgram.commitKernel, SourceProgram.revealKernel, SourceProgram.afterCommit,
    Config.initial, Config.defaulted, DefaultHistory.defaulted, DefaultHistory.record,
    commitSuccessor, PMF.pure_map]
  rfl

end

end VegasTests.Honest
