/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseMenu
import GameTheoryExtensions.Analysis.Protocol.Perturbation

/-! # Finite assessments for explicitly bounded response menus

Finite local response menus and a scheduler horizon suffice for finite legal
histories. The application state, observations and scheduler command carriers
need not be finite: nature uses finite-support laws, and the transition bound
limits their iterations. The Bayes beliefs use the same native histories,
private observations and remaining clock as the unrestricted runtime.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  [Inhabited app.Memory] (menu : app.ResponseMenu)
  (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)

instance finite_choice (who : Principal) (info : app.Info) :
    Finite ((menu.information initial horizon scheduler).Choice who info) := by
  classical
  change Finite {choice // choice ∈ (menu.information initial horizon scheduler).menu who info}
  cases info with
  | none => exact Set.finite_singleton none
  | some data =>
      have finite := ((menu.actions who data.1 data.2).finite_toSet).image Option.some
      exact finite.subset (by rintro choice ⟨action, member, rfl⟩; exact ⟨action, member, rfl⟩)

instance nonempty_choice (who : Principal) (info : app.Info) :
    Nonempty ((menu.information initial horizon scheduler).Choice who info) := by
  cases info with
  | none => exact ⟨⟨none, rfl⟩⟩
  | some data =>
      obtain ⟨action, member⟩ := menu.nonempty who data.1 data.2
      exact ⟨⟨some action, action, member, rfl⟩⟩

def uniformPolicy (who : Principal) :
    (menu.information initial horizon scheduler).BehavioralPolicy who := fun info => by
  let := Fintype.ofFinite ((menu.information initial horizon scheduler).Choice who info)
  exact FinDist.uniformOfFintype

def uniformAssessment : (menu.information initial horizon scheduler).BehavioralAssessment :=
  InformationModel.BehavioralAssessment.ofStrategy (menu.uniformPolicy initial horizon scheduler)

theorem uniform_fullyMixed : (menu.uniformAssessment initial horizon scheduler).IsFullyMixed := by
  intro who site choice
  let := Fintype.ofFinite ((menu.information initial horizon scheduler).Choice who site.1)
  exact FinDist.mem_support_uniformOfFintype choice

instance finite_history [Finite Principal] :
    Finite (menu.protocol initial horizon scheduler).History :=
  (menu.uniform_fullyMixed initial horizon scheduler).finite_history
    (menu.bounded initial horizon scheduler)

instance historyFintype [Finite Principal] :
    Fintype (menu.protocol initial horizon scheduler).History := Fintype.ofFinite _

instance informationHistoryFintype [Finite Principal] (who : Principal)
    (site : (menu.information initial horizon scheduler).InformationSite who) :
    Fintype ((menu.information initial horizon scheduler).InformationHistory who site.1) := by
  classical
  infer_instance

variable [Fintype Principal]

/-- Canonical Bayes beliefs for a fully mixed profile of this finite instance. -/
def bayesAssessment : (menu.information initial horizon scheduler).BehavioralAssessment :=
  (menu.uniformAssessment initial horizon scheduler).bayes
    (menu.uniform_fullyMixed initial horizon scheduler)
    (menu.decisionInformationAntichain initial horizon scheduler)

theorem bayesAssessment_consistent :
    (menu.bayesAssessment initial horizon scheduler).IsSequentiallyConsistent
      (menu.decisionInformationAntichain initial horizon scheduler) := by
  apply InformationModel.BehavioralAssessment.IsSequentiallyConsistent.of_fullyMixed_bayes
  · exact menu.uniform_fullyMixed initial horizon scheduler
  · exact InformationModel.BehavioralAssessment.bayes_isBayesConsistent _ _ _

/-- One perturbation uses the same positive weight at every player and site.
The resulting beliefs are computed from the native execution probabilities. -/
def perturbedAssessment
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1) :
    (menu.information initial horizon scheduler).BehavioralAssessment :=
  ((menu.uniformAssessment initial horizon scheduler).perturb profile weight
    positive.le atMostOne).bayes
      ((menu.uniformAssessment initial horizon scheduler).perturb_fullyMixed
        (menu.uniform_fullyMixed initial horizon scheduler) profile weight
        positive.le atMostOne positive)
      (menu.decisionInformationAntichain initial horizon scheduler)

theorem perturbedAssessment_fullyMixed
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1) :
    InformationModel.BehavioralAssessment.IsFullyMixed
      (menu.perturbedAssessment initial horizon scheduler profile weight positive atMostOne) :=
  (menu.uniformAssessment initial horizon scheduler).perturb_fullyMixed
    (menu.uniform_fullyMixed initial horizon scheduler) profile weight
    positive.le atMostOne positive

theorem perturbedAssessment_bayes
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1) :
    InformationModel.BehavioralAssessment.IsBayesConsistent
      (menu.information initial horizon scheduler)
      (menu.perturbedAssessment initial horizon scheduler profile weight positive atMostOne)
      (menu.decisionInformationAntichain initial horizon scheduler) :=
  InformationModel.BehavioralAssessment.bayes_isBayesConsistent _ _ _

theorem perturbedAssessment_strategy_converges
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (weight : Nat → ℝ) (positive : ∀ n, 0 < weight n) (atMostOne : ∀ n, weight n ≤ 1)
    (vanishes : Filter.Tendsto weight Filter.atTop (nhds 0)) (who : Principal) (info : app.Info) :
    FinDistConvergesPointwise
      (fun n => (menu.perturbedAssessment initial horizon scheduler profile (weight n)
        (positive n) (atMostOne n)).strategy who info) (profile who info) :=
  (menu.uniformAssessment initial horizon scheduler).perturb_strategy_converges profile weight
    (fun n => (positive n).le) atMostOne vanishes who info

end Interaction.ReactiveApplication.ResponseMenu
