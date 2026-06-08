/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.SourceFrontier.Strategic

/-!
# Raw source/frontier Nash-deviation bridge

The raw bridge is the strategic road map for the full source-local to frontier
behavioral theorem.  It states the two profile translations, the base observed
law equality, and the two unilateral-deviation lifting laws that together
induce a `KernelGame.NashDeviationBisimulation`.
-/

namespace Vegas

open GameTheory

namespace WFProgram

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Raw source/frontier strategy-translation bridge.

This is the exact data needed to compare the source-local strategic game with
the canonical behavioral frontier game without replacing the source strategy
surface by checkpoint-local strategies.  The bridge is phrased as profile
translations plus two unilateral-deviation lifting laws: those are the
strategic facts needed for a standard Nash-deviation bisimulation. -/
structure RawSourceFrontierNashDeviationBridge
    (program : WFProgram P L) [FiniteDomains program]
    (horizon : Nat) (cutoff : Payoff P) where
  sourceToFrontier :
    (program.sourceStrategicGame horizon cutoff).Profile →
      program.behavioralFrontierGame.Profile
  frontierToSource :
    program.behavioralFrontierGame.Profile →
      (program.sourceStrategicGame horizon cutoff).Profile
  sourceToFrontier_frontierToSource :
    ∀ frontierProfile,
      sourceToFrontier (frontierToSource frontierProfile) = frontierProfile
  sourceToFrontier_law :
    ∀ sourceProfile,
      (program.sourceStrategicOptionOutcomeView horizon cutoff).law
          sourceProfile =
        (program.behavioralFrontierOptionOutcomeView).law
          (sourceToFrontier sourceProfile)
  liftFrontierDeviation :
    ∀ sourceProfile who
      (frontierDeviation : program.behavioralFrontierGame.Strategy who),
      ∃ sourceDeviation :
          (program.sourceStrategicGame horizon cutoff).Strategy who,
        (program.sourceStrategicOptionOutcomeView horizon cutoff).law
            (Function.update sourceProfile who sourceDeviation) =
          (program.behavioralFrontierOptionOutcomeView).law
            (Function.update (sourceToFrontier sourceProfile)
              who frontierDeviation)
  liftSourceDeviation :
    ∀ sourceProfile who
      (sourceDeviation :
        (program.sourceStrategicGame horizon cutoff).Strategy who),
      ∃ frontierDeviation : program.behavioralFrontierGame.Strategy who,
        (program.sourceStrategicOptionOutcomeView horizon cutoff).law
            (Function.update sourceProfile who sourceDeviation) =
          (program.behavioralFrontierOptionOutcomeView).law
            (Function.update (sourceToFrontier sourceProfile)
              who frontierDeviation)

namespace RawSourceFrontierNashDeviationBridge

variable {program : WFProgram P L} [FiniteDomains program]
variable {horizon : Nat} {cutoff : Payoff P}

/-- Every frontier profile has a source representative with the same observed
optional payoff law. -/
theorem frontierToSource_law
    (bridge :
      RawSourceFrontierNashDeviationBridge program horizon cutoff)
    (frontierProfile : program.behavioralFrontierGame.Profile) :
    (program.sourceStrategicOptionOutcomeView horizon cutoff).law
        (bridge.frontierToSource frontierProfile) =
      (program.behavioralFrontierOptionOutcomeView).law frontierProfile := by
  simpa [bridge.sourceToFrontier_frontierToSource frontierProfile] using
    bridge.sourceToFrontier_law (bridge.frontierToSource frontierProfile)

/-- The raw source/frontier bridge induces the standard two-way
Nash-deviation bisimulation over optional source payoff outcomes. -/
noncomputable def toNashDeviationBisimulation
    (bridge :
      RawSourceFrontierNashDeviationBridge program horizon cutoff) :
    KernelGame.NashDeviationBisimulation
      (program.sourceStrategicGame horizon cutoff) program.behavioralFrontierGame
      (Option (Outcome P)) where
  viewG := program.sourceStrategicOptionOutcomeView horizon cutoff
  viewH := program.behavioralFrontierOptionOutcomeView
  rel := fun sourceProfile frontierProfile =>
    frontierProfile = bridge.sourceToFrontier sourceProfile
  law_eq := by
    intro sourceProfile frontierProfile hrel
    subst frontierProfile
    exact bridge.sourceToFrontier_law sourceProfile
  simulate_target_deviation := by
    intro sourceProfile frontierProfile hrel who frontierDeviation
    subst frontierProfile
    exact bridge.liftFrontierDeviation sourceProfile who frontierDeviation
  simulate_source_deviation := by
    intro sourceProfile frontierProfile hrel who sourceDeviation
    subst frontierProfile
    exact bridge.liftSourceDeviation sourceProfile who sourceDeviation

/-- A source profile is related to its translated frontier profile. -/
theorem sourceToFrontier_related
    (bridge :
      RawSourceFrontierNashDeviationBridge program horizon cutoff)
    (sourceProfile :
      (program.sourceStrategicGame horizon cutoff).Profile) :
    bridge.toNashDeviationBisimulation.rel
      sourceProfile (bridge.sourceToFrontier sourceProfile) := rfl

/-- A frontier profile is related to its chosen source representative. -/
theorem frontierToSource_related
    (bridge :
      RawSourceFrontierNashDeviationBridge program horizon cutoff)
    (frontierProfile : program.behavioralFrontierGame.Profile) :
    bridge.toNashDeviationBisimulation.rel
      (bridge.frontierToSource frontierProfile) frontierProfile :=
  (bridge.sourceToFrontier_frontierToSource frontierProfile).symm

/-- The induced bisimulation gives Nash equivalence for any common observed
preference on optional source payoff outcomes. -/
theorem nash_iff
    (bridge :
      RawSourceFrontierNashDeviationBridge program horizon cutoff)
    {sourceProfile :
      (program.sourceStrategicGame horizon cutoff).Profile}
    {frontierProfile : program.behavioralFrontierGame.Profile}
    (hrel :
      bridge.toNashDeviationBisimulation.rel
        sourceProfile frontierProfile)
    {pref :
      P → PMF (Option (Outcome P)) → PMF (Option (Outcome P)) → Prop} :
    (program.sourceStrategicGame horizon cutoff).IsNashFor
        (GameForm.observedPref
          (program.sourceStrategicOptionOutcomeView horizon cutoff) pref)
        sourceProfile ↔
      program.behavioralFrontierGame.IsNashFor
        (GameForm.observedPref
          program.behavioralFrontierOptionOutcomeView pref)
        frontierProfile :=
  bridge.toNashDeviationBisimulation.nash_iff hrel

/-- Source-to-frontier Nash equivalence at the canonical related profile. -/
theorem sourceToFrontier_nash_iff
    (bridge :
      RawSourceFrontierNashDeviationBridge program horizon cutoff)
    (sourceProfile :
      (program.sourceStrategicGame horizon cutoff).Profile)
    {pref :
      P → PMF (Option (Outcome P)) → PMF (Option (Outcome P)) → Prop} :
    (program.sourceStrategicGame horizon cutoff).IsNashFor
        (GameForm.observedPref
          (program.sourceStrategicOptionOutcomeView horizon cutoff) pref)
        sourceProfile ↔
      program.behavioralFrontierGame.IsNashFor
        (GameForm.observedPref
          program.behavioralFrontierOptionOutcomeView pref)
        (bridge.sourceToFrontier sourceProfile) :=
  bridge.nash_iff (bridge.sourceToFrontier_related sourceProfile)

/-- Frontier-to-source Nash equivalence at the chosen source representative. -/
theorem frontierToSource_nash_iff
    (bridge :
      RawSourceFrontierNashDeviationBridge program horizon cutoff)
    (frontierProfile : program.behavioralFrontierGame.Profile)
    {pref :
      P → PMF (Option (Outcome P)) → PMF (Option (Outcome P)) → Prop} :
    (program.sourceStrategicGame horizon cutoff).IsNashFor
        (GameForm.observedPref
          (program.sourceStrategicOptionOutcomeView horizon cutoff) pref)
        (bridge.frontierToSource frontierProfile) ↔
      program.behavioralFrontierGame.IsNashFor
        (GameForm.observedPref
          program.behavioralFrontierOptionOutcomeView pref)
        frontierProfile :=
  bridge.nash_iff (bridge.frontierToSource_related frontierProfile)

end RawSourceFrontierNashDeviationBridge

end WFProgram

end Vegas
