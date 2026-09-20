/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ValueBinding
import GameTheoryExtensions.Core.MixtureSimulation

/-! # The edge from the value-binding game to the source game

The source language lets a policy bind an unopenable candidate. Publicly that
action carries no content of its own, so the game whose strategies always bind a
value should lose nothing. This module states that as an edge: the identity on
outcomes, the inclusion on strategies, and a deviation certificate covering
every value-binding deviation and every pure one.

The pure deviations are the interesting half, and `bindValues_publicRun_eq`
supplies them. What is missing is a behavioral deviation that randomizes over
bindings: translating one needs a predraw, which draws a pure policy before the
private setup law, so this edge's deviation class is stated explicitly rather
than as every strategy.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The deviations the edge covers: every policy that binds a value, and every
pure policy. Neither class contains the other, and their union is not every
policy: a policy that randomizes between binding failure and binding a value is
in neither. -/
def BindingConsidered (setup : Setup (Player := Player) (L := L)) (who : Player)
    (strategy : BehavioralPolicy who setup.program) : Prop :=
  ValueBinding setup.program strategy ∨
    ∃ policy : PurePolicy who setup.program,
      strategy = PurePolicy.toBehavioral setup.program policy

/-- The value-binding game simulates the source game on those deviations, with
the identity on outcomes: each one is matched by a single value-binding policy,
not merely by a mixture. -/
def valueBindingSimulation (setup : Setup (Player := Player) (L := L)) :
    GameForm.MixtureSimulationOn setup.valueBindingGame setup.gameForm id id
      setup.BindingConsidered where
  compileStrategy _ strategy := strategy.val
  honest_law _ := rfl
  compiled_considered _ strategy := Or.inl strategy.2
  deviation_mixture profile who replacement hconsidered := by
    rcases hconsidered with hbinding | ⟨policy, rfl⟩
    · refine ⟨FinDist.pure ⟨replacement, hbinding⟩, ?_⟩
      rw [FinDist.pure_bind, valueBindingGame_play, valueBindingProfile_update]
      rfl
    · refine ⟨FinDist.pure
        ⟨PurePolicy.toBehavioral setup.program (PurePolicy.bindValues setup.program policy),
          valueBinding_bindValues setup.program policy⟩, ?_⟩
      rw [FinDist.pure_bind, valueBindingGame_play, valueBindingProfile_update]
      exact congrArg _
        (bindValues_publicRun_eq setup (valueBindingProfile profile) policy).symm

/-- A value-binding profile is ε-Nash in the value-binding game exactly when no
covered deviation in the full source game beats it by more than ε. Binding an
unopenable candidate is therefore worth nothing against such a profile. -/
theorem isεNash_valueBindingGame_iff (setup : Setup (Player := Player) (L := L))
    (value : SourceProgram.PublicOutcome setup.program → Player → ℝ) (ε : ℝ)
    (profile : Profile setup.valueBindingGame.sig) :
    (∀ who replacement, setup.BindingConsidered who replacement →
      (setup.publicRun (Function.update (valueBindingProfile profile) who replacement)).expect
          (fun outcome => value outcome who) ≤
        (setup.publicRun (valueBindingProfile profile)).expect
          (fun outcome => value outcome who) + ε) ↔
      IsεNash setup.valueBindingGame value ε profile :=
  (setup.valueBindingSimulation).considered_deviations_iff_isεNash value ε profile

end Vegas.SourceProgram.Setup
