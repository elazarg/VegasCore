/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveFiniteAssessment
import GameTheoryExtensions.Analysis.Protocol.FixedDepthBayes
import GameTheoryExtensions.Math.Probability.ObservationRetraction
import GameTheoryExtensions.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.Support

/-! # Native Bayes beliefs are conditional execution laws

At a common decision depth, the standard assessment's state belief is the
actual protocol state law conditioned on the existing private observation.
The observation still contains all response recall and passive samples.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

theorem stateBelief_eq_conditional_prefix
    (assessment : (menu.information initial horizon scheduler).BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (menu.information initial horizon scheduler) assessment
      (menu.decisionInformationAntichain initial horizon scheduler))
    (who : Principal)
    (site : (menu.information initial horizon scheduler).InformationSite who)
    (depth : Nat)
    (clock : ∀ history : (menu.information initial horizon scheduler).InformationHistory
      who site.1, history.1.trace.length = depth) :
    assessment.stateBelief who site =
      fiberConditional (((menu.information initial horizon scheduler).runBehavioral assessment.strategy depth).map
        History.state) (app.observe who) site.1 := by
  classical
  let M := menu.information initial horizon scheduler
  let prefixLaw := M.runBehavioral assessment.strategy depth
  have positive := mixed.informationMass_pos who site
  have belief : assessment.belief who site =
      M.bayesBelief assessment.strategy who site
        (menu.decisionInformationAntichain initial horizon scheduler who site) positive := by
    apply pmf_ext_toReal
    intro history
    rw [M.bayesBelief_apply]
    exact bayes who site positive history
  obtain ⟨history, _running, _active⟩ := site.2
  have supported : history.1 ∈ prefixLaw.support := by
    have support := mixed.history_supported history.1.trace
    rwa [clock history] at support
  have meets : ∃ h ∈ {h | M.infoOf who h.trace = site.1}, h ∈ prefixLaw.support :=
    ⟨history.1, history.2, supported⟩
  have present : site.1 ∈ (prefixLaw.map (app.observe who ∘ History.state)).support := by
    rw [PMF.support_map]
    refine ⟨history.1, supported, ?_⟩
    exact (menu.info initial horizon scheduler who history.1.trace).symm.trans history.2
  have conditioned := M.bayesBelief_map_eq_condOn assessment.strategy who site depth clock
    (menu.decisionInformationAntichain initial horizon scheduler who site) positive meets
  rw [← belief] at conditioned
  have fiber : prefixLaw.filter {h | M.infoOf who h.trace = site.1} meets =
      fiberConditional prefixLaw (app.observe who ∘ History.state) site.1 := by
    have same : {h : (menu.protocol initial horizon scheduler).History |
        M.infoOf who h.trace = site.1} =
        (app.observe who ∘ History.state) ⁻¹' {site.1} := by
      ext h
      change M.infoOf who h.trace = site.1 ↔ app.observe who h.state = site.1
      rw [show M.infoOf who h.trace = app.observe who h.state from
        menu.info initial horizon scheduler who h.trace]
    rw [fiberConditional, dite_eq_left (same ▸ meets)]
    congr 1
  calc
    assessment.stateBelief who site =
        ((assessment.belief who site).map Subtype.val).map History.state :=
      (PMF.map_comp _ _ _).symm
    _ = (fiberConditional prefixLaw (app.observe who ∘ History.state) site.1).map
        History.state := by rw [conditioned, fiber]
    _ = _ := PMF.map_conditional_readout prefixLaw History.state
      (app.observe who) site.1 present

end Interaction.ReactiveApplication.ResponseMenu
