/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitRevealAuction
import Vegas.Game.ParameterOutcomes

/-! # An auction with persistent private valuations

The prior supplies two ordinary integer valuations. The only protocol events
bind and reveal bids. Reporting strategies can depend on the owner's valuation;
utilities read the retained true valuations jointly with the public result.
-/

noncomputable section

namespace Vegas.Examples.PrivateValueAuction

open SourceProgram GameTheory GameTheory.Math.Probability
open CommitRevealAuction (Player)

def context : SourceCtx Player simpleExpr :=
  [(4, .privateInput .alice .int), (5, .privateInput .bob .int)]

private def acceptGuard {Γ : SourceCtx Player simpleExpr} (who : Player) (name : VarId) :
    SourceGuard simpleExpr Γ who name .int where
  schema := []
  schemaNames := by decide
  subjectFresh := by simp
  code := .constBool true
  reads := fun h => nomatch h

/-- Only bids are committed and revealed; valuations have no publication sites. -/
def program : SourceProgram Player simpleExpr context ∅ :=
  .commit 0 .alice (by decide) (acceptGuard .alice 0) <|
  .commit 1 .bob (by decide) (acceptGuard .bob 1) <|
  .reveal 2 .alice 0 (by decide) (.there .here) (by decide) <|
  .reveal 3 .bob 1 (by decide) (.there .here) (by decide) <|
  .ret []

def initial (values : Player → Int) : State simpleExpr context :=
  Env.cons (values .alice) (Env.cons (values .bob) (Env.empty (CellVal simpleExpr)))

/-- A joint prior over valuations, with no independence assumption. -/
def setup (prior : FinDist (Player → Int)) : Setup (Player := Player) (L := simpleExpr) where
  context := context
  namesNodup := by decide
  initialLaw := prior.map initial
  obligations := ∅
  program := program
  accounts := rfl

def values (state : State simpleExpr context) : Player → Int
  | .alice => state.get .here
  | .bob => state.get (.there .here)

def alicePolicy (report : Int → Int) : BehavioralPolicy Player.alice program :=
  (fun _ view => FinDist.pure (.success (report ((view.1.cells.get .here).getD 0))),
    ((fun h => nomatch h),
      (fun _ _ => FinDist.pure true, ((fun h => nomatch h), PUnit.unit))))

def bobPolicy (report : Int → Int) : BehavioralPolicy Player.bob program :=
  ((fun h => nomatch h),
    (fun _ view => FinDist.pure
      (.success (report ((view.1.cells.get (.there (.there .here))).getD 0))),
      ((fun h => nomatch h),
        (fun _ _ => FinDist.pure true, PUnit.unit))))

/-- Reports may be arbitrary functions of the reporting player's own type. -/
def profile (report : Player → Int → Int) : BehavioralProfile program
  | .alice => alicePolicy (report .alice)
  | .bob => bobPolicy (report .bob)

def truthful : BehavioralProfile program := profile fun _ => id

def result (alice bob : Int) : PublicOutcome program :=
  Env.cons (.success bob) (Env.cons (.success alice) (Env.empty simpleExpr.Val))

/-- Every report family binds ordinary values. -/
theorem profile_valueBinding (report : Player → Int → Int) (who : Player) :
    ValueBinding program (profile report who) := by
  cases who <;> simp [profile, alicePolicy, bobPolicy, ValueBinding, program]

/-- The public bids are precisely the owners' chosen functions of their inputs. -/
theorem publicRun_initial (report : Player → Int → Int) (types : Player → Int) :
    (program.run (profile report) (initial types)).map (publicOutcome program) =
      FinDist.pure (result (report .alice (types .alice)) (report .bob (types .bob))) := by
  simp only [SourceProgram.run, program, profile, alicePolicy, bobPolicy, initial,
    runWith, commitKernel, revealKernel, afterCommit, afterReveal, FinDist.pure_bind,
    FinDist.map_pure]
  rfl

/-- Truthful reports preserve their correlation with the actual private types. -/
theorem truthful_parameterRun (prior : FinDist (Player → Int)) :
    (setup prior).parameterRun values truthful =
      prior.map (fun types => (types, result (types .alice) (types .bob))) := by
  unfold Setup.parameterRun
  dsimp only [setup]
  rw [FinDist.bind_map, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro types _
  have law := congrArg (FinDist.map fun outcome => (types, outcome))
    (publicRun_initial (fun _ => id) types)
  have retained : values (initial types) = types := by
    funext who
    cases who <;> rfl
  simpa only [truthful, retained, FinDist.map_comp, Function.comp_def,
    FinDist.map_pure, id_eq] using law

/-- Type-dependent utility reuses the same public second-price settlement. -/
def utility (forfeiture : ℝ) (outcome : (Player → Int) × PublicOutcome program) : Player → ℝ :=
  CommitRevealAuction.utility (fun who => outcome.1 who) forfeiture outcome.2

/-- Two bindings and two disclosures, independently of the private values. -/
theorem eventCount : EventLowering.eventCount program = 4 := rfl

end Vegas.Examples.PrivateValueAuction
