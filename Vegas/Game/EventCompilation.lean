/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphDeviation
import Vegas.Game.EventScheduling
import GameTheoryExtensions.Core.MixtureSimulationComposition

/-! # Strategic correctness of full-source asynchronous graph compilation

The game executes the compiler's dependency-driven graph under an adaptive
public scheduler. Its strategy compiler and outcome readout are the actual
source compiler's policy translation and total terminal-state decoder.

It factors, and the factoring is worth seeing. The compiler's own edge goes to
the *canonical* graph, where a deviation is one backtranslated source policy and
no mixture is needed at all. The scheduler is a separate edge above it, and the
mixture in the composite is entirely the scheduler's doing.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability EventLowering

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- The operational game of the compiled event graph, with private setup
sampled inside execution and one public scheduling policy fixed for the game. -/
def eventGame (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler) : GameForm Player :=
  setup.eventGraph.gameForm
    (setup.initialLaw.map fun initial => setup.eventInputs initial) scheduler

/-- The same graph executed by its own canonical scheduler. -/
def canonicalEventGame (setup : Setup (Player := Player) (L := L)) : GameForm Player :=
  setup.eventGraph.canonicalGame (setup.initialLaw.map fun initial => setup.eventInputs initial)

/-- The public source result of a completed play. -/
def eventPublicOutcome (setup : Setup (Player := Player) (L := L))
    (outcome : setup.eventGraph.gameSignature.Outcome) : PublicOutcome setup.program :=
  publicOutcome setup.program (terminalState setup.program outcome)

/-- The same reading recovered from a terminal store alone, which is what the
scheduler edge above needs. It is total on stores and succeeds on every play, so
it introduces no payload default. -/
def eventPublicDecode (setup : Setup (Player := Player) (L := L))
    (store : Vegas.EventGraph.Store setup.eventGraph.layout) :
    Option (PublicOutcome setup.program) :=
  (decodeState? (terminalRefs setup.program) store).map (publicOutcome setup.program)

theorem eventPublicDecode_terminalStore (setup : Setup (Player := Player) (L := L))
    (outcome : setup.eventGraph.gameSignature.Outcome) :
    setup.eventPublicDecode (setup.eventGraph.terminalStore outcome) =
      some (setup.eventPublicOutcome outcome) := by
  have hdecode : decodeState? (terminalRefs setup.program)
      (setup.eventGraph.terminalStore outcome) =
        some (terminalState setup.program outcome) := (Option.some_get _).symm
  rw [eventPublicDecode, hdecode]
  rfl

/-- The compiler as an edge to the canonical graph. Its deviation certificate is
a point mass: a canonical graph deviation *is* one backtranslated source policy,
so nothing the compiler does needs a mixture. -/
def canonicalEventSimulation (setup : Setup (Player := Player) (L := L)) :
    GameForm.MixtureSimulationOn setup.gameForm setup.canonicalEventGame id
      setup.eventPublicOutcome (fun _ _ => True) where
  compileStrategy := compileEventPolicy setup.program
  honest_law profile := by
    have base := congrArg (FinDist.map (publicOutcome setup.program))
      (canonical_setup_law setup profile)
    rw [FinDist.map_comp] at base
    exact base.trans (FinDist.map_id _).symm
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    refine ⟨FinDist.pure (backtranslateEventPolicy setup.program who replacement), ?_⟩
    have base := congrArg (FinDist.map (publicOutcome setup.program))
      (canonical_setup_deviation_law setup profile who replacement)
    rw [FinDist.map_comp] at base
    rw [FinDist.pure_bind]
    exact base.trans (FinDist.map_id _).symm

/-- The full-source compiler simulates every unilateral asynchronous graph
deviation by a finite mixture of source policies: the compiler's edge to the
canonical graph composed with the scheduler's edge above it. The mixture is the
scheduler's contribution. -/
def eventSimulation (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler) :
    GameForm.MixtureSimulationOn setup.gameForm (setup.eventGame scheduler) id
      setup.eventPublicOutcome (fun _ _ => True) :=
  setup.canonicalEventSimulation.trans
    (setup.eventGraph.eventSchedulingSimulationOn
      (toEventGraph_barrierOrdered setup.program)
      (setup.initialLaw.map fun initial => setup.eventInputs initial) scheduler
      setup.eventPublicOutcome setup.eventPublicDecode setup.eventPublicDecode_terminalStore)
    (fun _ _ => trivial)

/-- Same-error Nash preservation and reflection at compiled source profiles
for every real-valued utility of the public source result. -/
theorem eventGame_approximate_nash_iff
    (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler)
    (utility : PublicOutcome setup.program → Player → ℝ)
    (ε : ℝ) (profile : BehavioralProfile setup.program) :
    IsεNash (setup.eventGame scheduler)
        (fun outcome who => utility (setup.eventPublicOutcome outcome) who)
        ε (compileEventProfile setup.program profile) ↔
      IsεNash setup.gameForm utility ε profile :=
  (setup.eventSimulation scheduler).isεNash_compileProfile_iff utility ε profile
    (fun _ _ => trivial)

/-- Every source lower bound against unilateral deviations holds against
arbitrary asynchronous graph replacements as well. -/
theorem eventGame_deviation_guarantee
    (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler)
    (profile : BehavioralProfile setup.program) (who : Player)
    (value : PublicOutcome setup.program → ℝ) (bound : ℝ)
    (sourceBound : ∀ alternative : BehavioralPolicy who setup.program,
      bound ≤ (setup.publicRun (Profile.update (sig := SourceProgram.gameSignature setup.program)
        profile who alternative)).expect value)
    (replacement : setup.eventGraph.BehavioralPolicy who) :
    bound ≤ ((setup.eventGame scheduler).play
      (Profile.update (sig := setup.eventGraph.gameSignature)
        (compileEventProfile setup.program profile) who replacement)).expect
          (fun outcome => value (setup.eventPublicOutcome outcome)) :=
  (setup.eventSimulation scheduler).guarantee profile who value bound sourceBound replacement
    trivial

end Vegas.SourceProgram.Setup
