/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.GraphLaw
import GameTheoryExtensions.Core.MixtureSimulation

/-! # Strategic correctness of complete source-to-graph compilation

Arbitrary graph policies have exact source preimages. Together with the
execution law, this gives unilateral-deviation correspondence, worst-case
guarantee transfer, and same-error Nash preservation and reflection at
compiled profiles. No assumption on failure incentives is needed at this edge.
-/

noncomputable section
namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]

private theorem compiledProfile_update
    (source : Initial (Player := Player) (L := L))
    (profile : BehavioralProfile source.program) (who : Player)
    (alternative : BehavioralPolicy who source.program) :
    source.compileGraphProfile
        (Profile.update (sig := gameSignature source.program) profile who alternative) =
      Profile.update (sig := Graph.gameSignature source.graph)
        (source.compileGraphProfile profile) who
        (compileGraphPolicy source.program source.namesNodup initialMap [] who alternative) := by
  funext actor
  by_cases same : actor = who
  · subst actor
    simp [Initial.compileGraphProfile]
  · simp [Initial.compileGraphProfile, Profile.update_of_ne, same]

/-- Every unilateral graph deviation has exactly the law of a single source
deviation, against the unchanged source opponents. -/
theorem Initial.graph_deviation_law (source : Initial (Player := Player) (L := L))
    (profile : BehavioralProfile source.program) (who : Player)
    (replacement : Graph.BehavioralPolicy who source.graph) :
    (Graph.run source.graph
      (Profile.update (sig := Graph.gameSignature source.graph)
        (source.compileGraphProfile profile) who replacement) source.graphInputs).map
      source.decodeGraph =
    source.run (Profile.update (sig := gameSignature source.program) profile who
      (backtranslateGraphPolicy source.program source.namesNodup
        initialMap [] who replacement)) := by
  have compiled := compiledProfile_update source profile who
    (backtranslateGraphPolicy source.program source.namesNodup initialMap [] who replacement)
  rw [compileGraphPolicy_backtranslate] at compiled
  rw [← compiled]
  exact source.graph_honest_law _

/-- The reusable strategic certificate for the full source language. The
generic mixture interface is instantiated by a singleton source deviation. -/
def Initial.graphSimulation (source : Initial (Player := Player) (L := L)) :
    GameForm.MixtureSimulationOn (gameForm source.program source.state)
      (Graph.gameForm source.graph source.graphInputs) id source.decodeGraph
      (fun _ _ => True) where
  compileStrategy := compileGraphPolicy source.program source.namesNodup initialMap []
  honest_law profile := by
    have law := source.graph_honest_law profile
    unfold Initial.compileGraphProfile at law
    simpa only [FinDist.map_id, gameForm, Graph.gameForm, Initial.run,
      gameSignature] using law
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    refine ⟨FinDist.pure (backtranslateGraphPolicy source.program source.namesNodup
      initialMap [] who replacement), ?_⟩
    have law := source.graph_deviation_law profile who replacement
    unfold Initial.compileGraphProfile at law
    simpa only [FinDist.pure_bind, FinDist.map_id, gameForm, Graph.gameForm,
      Initial.run, gameSignature] using law

/-- Same-error Nash correspondence for arbitrary utilities of source outcomes,
including utilities that differ from the program's payout projection. -/
theorem Initial.graph_approximate_nash_iff
    (source : Initial (Player := Player) (L := L))
    (utility : State L source.program.terminalCtx → Player → ℝ)
    (ε : ℝ) (profile : BehavioralProfile source.program) :
    IsεNash (Graph.gameForm source.graph source.graphInputs)
        (fun outcome who => utility (source.decodeGraph outcome) who) ε
        (source.compileGraphProfile profile) ↔
      IsεNash (gameForm source.program source.state) utility ε profile :=
  source.graphSimulation.isεNash_compileProfile_iff utility ε profile (fun _ _ => trivial)

theorem Initial.graph_nash_iff (source : Initial (Player := Player) (L := L))
    (utility : State L source.program.terminalCtx → Player → ℝ)
    (profile : BehavioralProfile source.program) :
    IsNash (Graph.gameForm source.graph source.graphInputs)
        (euPreference fun outcome who => utility (source.decodeGraph outcome) who)
        (source.compileGraphProfile profile) ↔
      IsNash (gameForm source.program source.state) (euPreference utility) profile :=
  source.graphSimulation.isNash_compileProfile_iff utility profile (fun _ _ => trivial)

end Vegas.SourceProgram
