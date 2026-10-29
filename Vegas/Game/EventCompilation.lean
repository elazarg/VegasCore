/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphDeviation
import Vegas.Game.EventScheduling
import GameTheory.Core.MixtureSimulationComposition

/-! # Strategic correctness of source-to-graph compilation

Generated dependencies preserve source order under every public scheduler.
Compilation preserves complete public outcomes, and each graph deviation is
represented by one source policy fixed before private setup is sampled.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- The public source result of a completed play. -/
def eventPublicOutcome (setup : Setup (Player := Player) (L := L))
    (outcome : setup.eventGraph.gameSignature.Outcome) : PublicOutcome setup.program :=
  publicOutcome setup.program (terminalConfig setup.program outcome)

/-- The compiler as an edge to the canonical graph. Its deviation certificate is
a point mass: a canonical graph deviation *is* one backtranslated source policy,
so nothing the compiler does needs a mixture. -/
def canonicalEventSimulation (setup : Setup (Player := Player) (L := L)) :
    GameForm.MixtureSimulationOn setup.gameForm setup.canonicalEventGame id
      setup.eventPublicOutcome (fun _ _ => True) where
  compileStrategy := compileEventPolicy setup.program
  honest_law profile := by
    have base := congrArg (PMF.map (publicOutcome setup.program))
      (canonical_setup_law setup profile)
    rw [PMF.map_comp] at base
    exact base.trans (PMF.map_id _).symm
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    refine ⟨PMF.pure (backtranslateEventPolicy setup.program who replacement), ?_⟩
    have base := congrArg (PMF.map (publicOutcome setup.program))
      (canonical_setup_deviation_law setup profile who replacement)
    rw [PMF.map_comp] at base
    rw [PMF.pure_bind]
    exact base.trans (PMF.map_id _).symm

/-- Every public scheduler has the same exact compiler edge. Its deviation
certificate is a point mass, with no finite-alphabet or initial-law premise. -/
def eventSimulation (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler) :
    GameForm.MixtureSimulationOn setup.gameForm (setup.eventGame scheduler) id
      setup.eventPublicOutcome (fun _ _ => True) :=
  setup.canonicalEventSimulation.trans
    (setup.eventSchedulingSimulationOn scheduler setup.eventPublicOutcome)
    (fun _ _ => trivial)

/-- Every compiled event game has finitely supported outcome laws under finite
fresh-binding alphabets and a finitely supported initial law. -/
theorem eventGame_play_support_finite (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (scheduler : setup.eventGraph.PublicScheduler) (profile : setup.eventGraph.BehavioralProfile) :
    ((setup.eventGame scheduler).play profile).support.Finite :=
  setup.eventGraph.gameForm_play_support_finite _
    (by rw [PMF.support_map]; exact setup.initialLaw_support_finite.image _) scheduler _
    ((toEventGraph_finiteActions setup.program finite).profileFiniteSupport _)

/-- Same-error Nash preservation and reflection at compiled source profiles
for every real-valued utility of the public source result. -/
theorem eventGame_approximate_nash_iff
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (scheduler : setup.eventGraph.PublicScheduler)
    (utility : PublicOutcome setup.program → Player → ℝ)
    (ε : ℝ) (profile : BehavioralProfile setup.program) :
    IsεNash (setup.eventGame scheduler)
        (fun outcome who => utility (setup.eventPublicOutcome outcome) who)
        ε (compileEventProfile setup.program profile) ↔
      IsεNash setup.gameForm utility ε profile :=
  ((setup.eventSimulation scheduler).isεNash_compileProfile_iff utility ε
    profile (fun _ _ => trivial)).trans (and_iff_left fun _ _ =>
      hasExpectation_of_payoffIntegrable (payoffIntegrable_of_finite_support _ _
        (setup.eventGame_play_support_finite finite scheduler _)))

end Vegas.SourceProgram.Setup
