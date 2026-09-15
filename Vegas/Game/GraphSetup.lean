/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.GraphSetup
import GameTheoryExtensions.Core.MixtureSimulation

/-! # Strategic correctness with distributed private setup

The initial state is sampled before execution, but policies and the
backtranslation of a graph deviation are independent of the realized state.
-/

noncomputable section
namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]

private theorem compiledProfile_update
    (setup : Setup (Player := Player) (L := L))
    (profile : Profile (SourceProgram.gameSignature setup.program)) (who : Player)
    (alternative : (SourceProgram.gameSignature setup.program).Strategy who) :
    setup.compileGraphProfile
        (Profile.update (sig := SourceProgram.gameSignature setup.program)
          profile who alternative) =
      Profile.update (sig := setup.graphGameForm.sig)
        (setup.compileGraphProfile profile) who
        (compileGraphPolicy setup.program setup.namesNodup initialMap [] who alternative) := by
  funext actor
  by_cases same : actor = who
  · subst actor
    simp [compileGraphProfile]
  · simp [compileGraphProfile, Profile.update_of_ne, same]

/-- Every unilateral graph deviation has exactly the distributed source law
of one state-independent source deviation. -/
theorem graph_deviation_law (setup : Setup (Player := Player) (L := L))
    (profile : Profile (SourceProgram.gameSignature setup.program)) (who : Player)
    (replacement : setup.graphGameForm.sig.Strategy who) :
    (setup.graphGameForm.play
      (Profile.update (sig := setup.graphGameForm.sig)
        (setup.compileGraphProfile profile) who replacement)).map setup.decodeGraph =
    setup.run (Profile.update (sig := SourceProgram.gameSignature setup.program) profile who
      (backtranslateGraphPolicy setup.program setup.namesNodup
        initialMap [] who replacement)) := by
  have compiled := compiledProfile_update setup profile who
    (backtranslateGraphPolicy setup.program setup.namesNodup initialMap [] who replacement)
  rw [compileGraphPolicy_backtranslate] at compiled
  rw [← compiled]
  exact setup.graph_honest_law _

/-- Strategic simulation for a finite initial law of private/public states. -/
def graphSimulation (setup : Setup (Player := Player) (L := L)) :
    GameForm.MixtureSimulationOn setup.gameForm setup.graphGameForm id setup.decodeGraph
      (fun _ _ => True) where
  compileStrategy := compileGraphPolicy setup.program setup.namesNodup initialMap []
  honest_law profile := by
    have law := setup.graph_honest_law profile
    unfold compileGraphProfile at law
    rw [FinDist.map_id]
    exact law
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    refine ⟨FinDist.pure (backtranslateGraphPolicy setup.program setup.namesNodup
      initialMap [] who replacement), ?_⟩
    have law := setup.graph_deviation_law profile who replacement
    unfold compileGraphProfile at law
    have rhs :
        (FinDist.pure (backtranslateGraphPolicy setup.program setup.namesNodup
          initialMap [] who replacement)).bind (fun alternative =>
            (setup.gameForm.play (Profile.update profile who alternative)).map id) =
          setup.run (Profile.update profile who
            (backtranslateGraphPolicy setup.program setup.namesNodup
              initialMap [] who replacement)) := by
      rw [FinDist.pure_bind]
      exact FinDist.map_id _
    exact law.trans rhs.symm

/-- Same-error Nash correspondence for arbitrary utilities of terminal source
states under the distributed setup. -/
theorem graph_approximate_nash_iff
    (setup : Setup (Player := Player) (L := L))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (ε : ℝ) (profile : Profile (SourceProgram.gameSignature setup.program)) :
    IsεNash setup.graphGameForm
        (fun outcome who => utility (setup.decodeGraph outcome) who) ε
        (setup.compileGraphProfile profile) ↔
      IsεNash setup.gameForm utility ε profile :=
  setup.graphSimulation.isεNash_compileProfile_iff utility ε profile (fun _ _ => trivial)

theorem graph_nash_iff (setup : Setup (Player := Player) (L := L))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (profile : Profile (SourceProgram.gameSignature setup.program)) :
    IsNash setup.graphGameForm
        (euPreference fun outcome who => utility (setup.decodeGraph outcome) who)
        (setup.compileGraphProfile profile) ↔
      IsNash setup.gameForm (euPreference utility) profile :=
  setup.graphSimulation.isNash_compileProfile_iff utility profile (fun _ _ => trivial)

end Vegas.SourceProgram.Setup
