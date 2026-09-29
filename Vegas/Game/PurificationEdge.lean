/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Purification
import Vegas.Source.FiniteSupport
import GameTheory.Core.MixtureUtilitySimulation

/-! # The edge from the pure-strategy game to the source game

Randomizing buys a source player nothing that a mixture of pure policies does
not already buy, and the mixture may be drawn before the private setup law. So
the game whose strategies never randomize simulates the full source game, with
the identity on outcomes and every deviation considered.

The reading is the Kuhn-style one: to check a pure profile for equilibrium it is
enough to consider pure deviations. Note where purity is needed and where it is
not — the profile being checked must be pure, while the deviations it is checked
against need not be.

What this does not say is that the pure game has an equilibrium, or that mixed
strategies can be dispensed with. Restricting which profiles are considered is a
different question from restricting which deviations they face, and matching
pennies separates them.

Fresh binding alphabets are finite and the initial law is finitely supported.
Then every deviation branches finitely, so it is a finite mixture of pure ones
and every outcome law is finitely supported.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The pure-strategy game simulates the source game, under any reading of the
outcome and with no restriction on the deviations considered. -/
def pureSimulationOn {Observation : Type} (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (observe : SourceProgram.PublicOutcome setup.program → Observation) :
    GameForm.MixtureSimulationOn setup.pureGame setup.gameForm observe observe
      (fun _ _ => True) where
  compileStrategy _ policy := PurePolicy.toBehavioral setup.program policy
  honest_law _ := rfl
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    obtain ⟨mixture, _, hmixture⟩ :=
      exists_pureMixture_publicRun setup finite (pureProfile profile) replacement
    refine ⟨mixture, ?_⟩
    change (setup.publicRun (Function.update (pureProfile profile) who replacement)).map
      observe = _
    rw [hmixture, PMF.map_bind]
    refine bind_congr_on_support _ fun choice _ => ?_
    rw [pureGame_play, pureProfile_update]

/-- The edge read on the source outcome itself. -/
def pureSimulation (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] :
    GameForm.MixtureSimulationOn setup.pureGame setup.gameForm id id (fun _ _ => True) :=
  setup.pureSimulationOn finite id

/-- Every source deviation from a compiled pure profile has integrable utility,
because its outcome law is finitely supported. -/
theorem pureSimulation_deviation_integrable (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (utility : SourceProgram.PublicOutcome setup.program → Player → ℝ)
    (profile : Profile setup.pureGame.sig) (who : Player)
    (replacement : setup.gameForm.sig.Strategy who) :
    UtilityIntegrable (fun outcome player => utility (id outcome) player) who
      (setup.gameForm.play (Profile.update
        ((setup.pureSimulation finite ).compileProfile profile) who replacement)) :=
  payoffIntegrable_of_finite_support _ _
    (setup.gameForm_play_support_finite finite _)

/-- Randomizing buys a deviator nothing: a pure profile is ε-Nash in the full
source game exactly when it is ε-Nash among pure policies. This is a statement
about one profile, not about the restricted game: it does not say a pure
equilibrium exists. -/
theorem isεNash_pureGame_iff (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (value : SourceProgram.PublicOutcome setup.program → Player → ℝ) (ε : ℝ)
    (profile : Profile setup.pureGame.sig) :
    IsεNash setup.gameForm value ε (pureProfile profile) ↔
      IsεNash setup.pureGame value ε profile :=
  ((setup.pureSimulation finite ).isεNash_compileProfile_iff value ε profile
    fun _ _ => trivial).trans (and_iff_left fun who replacement =>
      (setup.pureSimulation_deviation_integrable finite value profile who
        replacement).hasExpectation)

/-- The same at ε zero. -/
theorem isNash_pureGame_iff (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (value : SourceProgram.PublicOutcome setup.program → Player → ℝ)
    (profile : Profile setup.pureGame.sig) :
    IsNash setup.gameForm (euPreference value) (pureProfile profile) ↔
      IsNash setup.pureGame (euPreference value) profile :=
  ((setup.pureSimulation finite ).isNash_compileProfile_iff value profile
    fun _ _ => trivial).trans (and_iff_left fun who replacement =>
      (setup.pureSimulation_deviation_integrable finite value profile who
        replacement).hasExpectation)

/-- The edge in the composable interface, at one-player coalitions. -/
def pureUtilitySimulation (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (utility : SourceProgram.PublicOutcome setup.program → Player → ℝ) :
    GameForm.UtilitySimulation setup.pureGame setup.gameForm utility utility
      (GameTheory.singletonGroups Player) :=
  (setup.pureSimulation finite ).toUtilitySimulation utility (fun _ _ => trivial)
    (setup.pureSimulation_deviation_integrable finite utility)

end Vegas.SourceProgram.Setup
