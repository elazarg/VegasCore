/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveProtocol
import GameTheoryExtensions.Analysis.Protocol.Sequential

/-! # Finite-support trembles and reactive response menus

Every decision permits every auxiliary memory value. A fully mixed assessment
therefore requires a finite memory carrier, regardless of the execution horizon.
This diagnoses application of the finite-support assessment interface, not
nonexistence of sequential equilibria in a model with other probability laws.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)
  [Inhabited app.Memory]

theorem finite_memory_of_fullyMixed
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (assessment : (app.information initial horizon scheduler).BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (who : Principal)
    (site : (app.information initial horizon scheduler).InformationSite who) :
    Finite app.Memory := by
  obtain ⟨history, running, action, legal⟩ := site.2
  have active : true = site.1.isSome := legal
  let embed : app.Memory → (app.information initial horizon scheduler).Choice who site.1 :=
    fun memory => ⟨some ⟨memory, none⟩, active⟩
  let := mixed.finite_choice who site
  apply Finite.of_injective embed
  intro first second same
  have actions := Option.some.inj (congrArg Subtype.val same)
  exact congrArg Action.memory actions

theorem not_fullyMixed_of_infinite_memory [Infinite app.Memory]
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (assessment : (app.information initial horizon scheduler).BehavioralAssessment)
    (who : Principal)
    (site : (app.information initial horizon scheduler).InformationSite who) :
    ¬ assessment.IsFullyMixed := by
  intro mixed
  let := app.finite_memory_of_fullyMixed initial horizon scheduler assessment mixed who site
  exact not_finite app.Memory

end Interaction.ReactiveApplication
