/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Purification
import Vegas.Source.ValueBinding
import GameTheoryExtensions.Core.UtilitySimulation

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
with the same public result law (`bindValues_publicRun_eq`).
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
    (observe : SourceProgram.PublicOutcome setup.program → Observation) :
    GameForm.MixtureSimulationOn setup.valueBindingGame setup.gameForm observe observe
      (fun _ _ => True) where
  compileStrategy _ strategy := strategy.val
  honest_law _ := rfl
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    obtain ⟨mixture, hmixture⟩ :=
      exists_pureMixture_publicRun setup (valueBindingProfile profile) replacement
    refine ⟨mixture.map fun choice =>
      ⟨PurePolicy.toBehavioral setup.program (PurePolicy.bindValues setup.program choice),
        valueBinding_bindValues setup.program choice⟩, ?_⟩
    change (setup.publicRun
      (Function.update (valueBindingProfile profile) who replacement)).map observe = _
    rw [hmixture, FinDist.map_bind, FinDist.bind_map]
    refine FinDist.bind_congr fun choice _ => ?_
    rw [valueBindingGame_play, valueBindingProfile_update]
    exact congrArg _
      (bindValues_publicRun_eq setup (valueBindingProfile profile) choice).symm

/-- The edge read on the source outcome itself. -/
def valueBindingSimulation (setup : Setup (Player := Player) (L := L)) :
    GameForm.MixtureSimulationOn setup.valueBindingGame setup.gameForm id id
      (fun _ _ => True) :=
  setup.valueBindingSimulationOn id

/-- Binding an unopenable candidate is worth nothing: a value-binding profile is
ε-Nash in the full source game exactly when it is ε-Nash among policies that
always bind a value. -/
theorem isεNash_valueBindingGame_iff (setup : Setup (Player := Player) (L := L))
    (value : SourceProgram.PublicOutcome setup.program → Player → ℝ) (ε : ℝ)
    (profile : Profile setup.valueBindingGame.sig) :
    IsεNash setup.gameForm value ε (valueBindingProfile profile) ↔
      IsεNash setup.valueBindingGame value ε profile :=
  setup.valueBindingSimulation.isεNash_compileProfile_iff value ε profile fun _ _ => trivial

/-- The same at ε zero. -/
theorem isNash_valueBindingGame_iff (setup : Setup (Player := Player) (L := L))
    (value : SourceProgram.PublicOutcome setup.program → Player → ℝ)
    (profile : Profile setup.valueBindingGame.sig) :
    IsNash setup.gameForm (euPreference value) (valueBindingProfile profile) ↔
      IsNash setup.valueBindingGame (euPreference value) profile :=
  setup.valueBindingSimulation.isNash_compileProfile_iff value profile fun _ _ => trivial

/-- The edge in the composable interface, at one-player coalitions. -/
def valueBindingUtilitySimulation (setup : Setup (Player := Player) (L := L))
    (utility : SourceProgram.PublicOutcome setup.program → Player → ℝ) :
    GameForm.UtilitySimulation setup.valueBindingGame setup.gameForm utility utility
      (GameForm.singletonGroups Player) :=
  setup.valueBindingSimulation.toUtilitySimulation utility fun _ _ => trivial

end Vegas.SourceProgram.Setup
