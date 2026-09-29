/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Purification
import Vegas.Source.FiniteSupport
import Vegas.Source.ValueBinding
import GameTheory.Core.MixtureUtilitySimulation

/-! # The edge from the value-binding game to the source game

The source language lets a policy bind an unopenable candidate. Publicly that
action carries no content of its own — a cell bound to failure publishes failure
whatever its owner later decides, exactly as a bound value that is never
disclosed does — so the game whose strategies always bind a value should lose
nothing.

This module states that as an edge: the identity on outcomes, the inclusion on
strategies, and a deviation certificate covering *every* policy of the full
source game. The certificate composes two steps. A behavioral deviation is
first a mixture of pure policies, drawn before the private setup law
(`exists_pureMixture_publicRun`); each pure policy then has a value-binding one
with the same public result law (`bindValues_publicRun_eq`). The first step
needs finite fresh-binding alphabets and a finitely supported initial law, which
also make every outcome law finitely supported.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The value-binding game simulates the source game, under any reading of the
outcome and with no restriction on the deviations considered. Both games have
the same outcome, and the certificate equates laws rather than expectations, so
the reading is a parameter: at `id` it is the edge itself, and at whatever map a
later edge observes it is the left half of a composition. -/
def valueBindingSimulationOn {Observation : Type}
    (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (observe : SourceProgram.PublicOutcome setup.program → Observation) :
    GameForm.MixtureSimulationOn setup.valueBindingGame setup.gameForm observe observe
      (fun _ _ => True) where
  compileStrategy _ strategy := strategy.val
  honest_law _ := rfl
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    obtain ⟨mixture, _, hmixture⟩ := exists_pureMixture_publicRun setup finite
      (valueBindingProfile profile) replacement
    refine ⟨mixture.map fun choice =>
      ⟨PurePolicy.toBehavioral setup.program (PurePolicy.bindValues setup.program choice),
        valueBinding_bindValues setup.program choice⟩, ?_⟩
    change (setup.publicRun
      (Function.update (valueBindingProfile profile) who replacement)).map observe = _
    rw [hmixture, PMF.map_bind, PMF.bind_map, Function.comp_def]
    refine bind_congr_on_support _ fun choice _ => ?_
    rw [valueBindingGame_play, valueBindingProfile_update]
    exact congrArg _
      (bindValues_publicRun_eq setup (valueBindingProfile profile) choice).symm

/-- The edge read on the source outcome itself. -/
def valueBindingSimulation (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] :
    GameForm.MixtureSimulationOn setup.valueBindingGame setup.gameForm id id
      (fun _ _ => True) :=
  setup.valueBindingSimulationOn finite id

/-- Every source deviation from a value-binding profile has integrable utility,
because its outcome law is finitely supported. -/
theorem valueBindingSimulation_deviation_integrable (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (utility : SourceProgram.PublicOutcome setup.program → Player → ℝ)
    (profile : Profile setup.valueBindingGame.sig) (who : Player)
    (replacement : setup.gameForm.sig.Strategy who) :
    UtilityIntegrable (fun outcome player => utility (id outcome) player) who
      (setup.gameForm.play (Profile.update
        ((setup.valueBindingSimulation finite ).compileProfile profile) who
          replacement)) :=
  payoffIntegrable_of_finite_support _ _
    (setup.gameForm_play_support_finite finite _)

/-- Binding an unopenable candidate is worth nothing: a value-binding profile is
ε-Nash in the full source game exactly when it is ε-Nash among policies that
always bind a value. -/
theorem isεNash_valueBindingGame_iff (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (value : SourceProgram.PublicOutcome setup.program → Player → ℝ) (ε : ℝ)
    (profile : Profile setup.valueBindingGame.sig) :
    IsεNash setup.gameForm value ε (valueBindingProfile profile) ↔
      IsεNash setup.valueBindingGame value ε profile :=
  ((setup.valueBindingSimulation finite ).isεNash_compileProfile_iff value ε profile
    fun _ _ => trivial).trans (and_iff_left fun who replacement =>
      (setup.valueBindingSimulation_deviation_integrable finite value profile who
        replacement).hasExpectation)

/-- The same at ε zero. -/
theorem isNash_valueBindingGame_iff (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (value : SourceProgram.PublicOutcome setup.program → Player → ℝ)
    (profile : Profile setup.valueBindingGame.sig) :
    IsNash setup.gameForm (euPreference value) (valueBindingProfile profile) ↔
      IsNash setup.valueBindingGame (euPreference value) profile :=
  ((setup.valueBindingSimulation finite ).isNash_compileProfile_iff value profile
    fun _ _ => trivial).trans (and_iff_left fun who replacement =>
      (setup.valueBindingSimulation_deviation_integrable finite value profile who
        replacement).hasExpectation)

/-- The edge in the composable interface, at one-player coalitions. -/
def valueBindingUtilitySimulation (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (utility : SourceProgram.PublicOutcome setup.program → Player → ℝ) :
    GameForm.UtilitySimulation setup.valueBindingGame setup.gameForm utility utility
      (GameTheory.singletonGroups Player) :=
  (setup.valueBindingSimulation finite ).toUtilitySimulation utility
    (fun _ _ => trivial)
    (setup.valueBindingSimulation_deviation_integrable finite utility)

end Vegas.SourceProgram.Setup
