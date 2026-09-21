/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Purification
import GameTheoryExtensions.Core.UtilitySimulation

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
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The pure-strategy game simulates the source game, under any reading of the
outcome and with no restriction on the deviations considered. -/
def pureSimulationOn {Observation : Type} (setup : Setup (Player := Player) (L := L))
    (observe : SourceProgram.PublicOutcome setup.program → Observation) :
    GameForm.MixtureSimulationOn setup.pureGame setup.gameForm observe observe
      (fun _ _ => True) where
  compileStrategy _ policy := PurePolicy.toBehavioral setup.program policy
  honest_law _ := rfl
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    obtain ⟨mixture, hmixture⟩ :=
      exists_pureMixture_publicRun setup (pureProfile profile) replacement
    refine ⟨mixture, ?_⟩
    change (setup.publicRun (Function.update (pureProfile profile) who replacement)).map
      observe = _
    rw [hmixture, FinDist.map_bind]
    refine FinDist.bind_congr fun choice _ => ?_
    rw [pureGame_play, pureProfile_update]

/-- The edge read on the source outcome itself. -/
def pureSimulation (setup : Setup (Player := Player) (L := L)) :
    GameForm.MixtureSimulationOn setup.pureGame setup.gameForm id id (fun _ _ => True) :=
  setup.pureSimulationOn id

/-- Randomizing buys a deviator nothing: a pure profile is ε-Nash in the full
source game exactly when it is ε-Nash among pure policies. This is a statement
about one profile, not about the restricted game: it does not say a pure
equilibrium exists. -/
theorem isεNash_pureGame_iff (setup : Setup (Player := Player) (L := L))
    (value : SourceProgram.PublicOutcome setup.program → Player → ℝ) (ε : ℝ)
    (profile : Profile setup.pureGame.sig) :
    IsεNash setup.gameForm value ε (pureProfile profile) ↔
      IsεNash setup.pureGame value ε profile :=
  setup.pureSimulation.isεNash_compileProfile_iff value ε profile fun _ _ => trivial

/-- The same at ε zero. -/
theorem isNash_pureGame_iff (setup : Setup (Player := Player) (L := L))
    (value : SourceProgram.PublicOutcome setup.program → Player → ℝ)
    (profile : Profile setup.pureGame.sig) :
    IsNash setup.gameForm (euPreference value) (pureProfile profile) ↔
      IsNash setup.pureGame (euPreference value) profile :=
  setup.pureSimulation.isNash_compileProfile_iff value profile fun _ _ => trivial

/-- The edge in the composable interface, at one-player coalitions. -/
def pureUtilitySimulation (setup : Setup (Player := Player) (L := L))
    (utility : SourceProgram.PublicOutcome setup.program → Player → ℝ) :
    GameForm.UtilitySimulation setup.pureGame setup.gameForm utility utility
      (GameForm.singletonGroups Player) :=
  setup.pureSimulation.toUtilitySimulation utility fun _ _ => trivial

end Vegas.SourceProgram.Setup
