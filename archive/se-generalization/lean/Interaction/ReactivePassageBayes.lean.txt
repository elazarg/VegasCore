/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveBayes
import GameTheoryExtensions.Analysis.Protocol.PassageBayes

/-! # Native state beliefs from variable-depth information passage

The actual native terminal history retains the unique earlier control at an
information antichain. Conditioning its presence gives the standard state
belief without a common decision depth. The final control is not substituted
for the control where the owner actually observed its input.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- The real native history passage law gives the current state posterior at
every positive-mass decision site, even when hidden histories have different
depths. The extra `some` records passage; it is distinct from the native
control's own optional state. No stopped-history likelihood is supplied. -/
theorem stateBelief_eq_conditional_passage
    (assessment : (menu.information initial horizon scheduler).BehavioralAssessment)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (menu.information initial horizon scheduler) assessment
      (menu.decisionInformationAntichain initial horizon scheduler))
    (who : Principal)
    (site : (menu.information initial horizon scheduler).InformationSite who)
    (positive : 0 < (menu.information initial horizon scheduler).informationMass
      assessment.strategy who site) :
    let model := menu.information initial horizon scheduler
    let certificate := (menu.bounded initial horizon scheduler).wellFoundedHistories
    (assessment.stateBelief who site).map some =
      fiberPosterior ((model.runBehavioralTerminalFrom certificate assessment.strategy
        (menu.protocol initial horizon scheduler).initHistory).map fun final =>
          (site.ancestor? model final).map fun before => before.1.state) Option.isSome true := by
  classical
  intro model certificate
  let antichain := menu.decisionInformationAntichain initial horizon scheduler who site
  let encountered := (model.runBehavioralTerminalFrom certificate assessment.strategy
    (menu.protocol initial horizon scheduler).initHistory).map (site.ancestor? model)
  let read : Option (model.InformationHistory who site.1) → Option _ :=
    Option.map fun before => before.1.state
  have belief : assessment.belief who site =
      model.bayesBelief assessment.strategy who site antichain positive := by
    ext before
    rw [model.bayesBelief_apply]
    exact bayes who site positive before
  have projected := congrArg (PMF.map read)
    (site.bayesBelief_eq_conditional_ancestor model antichain certificate
      assessment.strategy positive)
  rw [← belief] at projected
  have present : true ∈ (encountered.map Option.isSome).support := by
    rw [PMF.mem_support_iff,
      site.terminal_ancestor_passage model antichain certificate assessment.strategy]
    exact positive.ne'
  have transported : (fiberPosterior encountered Option.isSome true).map read =
      fiberPosterior (encountered.map read) Option.isSome true := by
    simpa only [read, Function.comp_def, Option.isSome_map] using
      map_fiberPosterior_readout encountered read Option.isSome true (by
        simpa only [read, Function.comp_def, Option.isSome_map] using present)
  change ((assessment.belief who site).map some).map read =
    (fiberPosterior encountered Option.isSome true).map read at projected
  rw [transported] at projected
  simpa only [encountered, read, PMF.map_comp, Function.comp_def, Option.map_some,
    InformationModel.BehavioralAssessment.stateBelief] using projected

end Interaction.ReactiveApplication.ResponseMenu
