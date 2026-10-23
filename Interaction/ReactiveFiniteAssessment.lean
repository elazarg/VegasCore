/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveResponseMenu
import GameTheoryExtensions.Analysis.Protocol.Perturbation
import GameTheoryExtensions.Math.Probability.Uniform

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
  (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

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
  exact (PMF.uniformOfFintype _)

def uniformAssessment : (menu.information initial horizon scheduler).BehavioralAssessment :=
  InformationModel.BehavioralAssessment.ofStrategy (menu.uniformPolicy initial horizon scheduler)

theorem uniform_fullyMixed : (menu.uniformAssessment initial horizon scheduler).IsFullyMixed := by
  intro who site choice
  let := Fintype.ofFinite ((menu.information initial horizon scheduler).Choice who site.1)
  exact PMF.mem_support_uniformOfFintype choice

instance finite_history [Finite Principal] [app.FiniteNature initial scheduler] :
    Finite (menu.protocol initial horizon scheduler).History :=
  (menu.uniform_fullyMixed initial horizon scheduler).finite_history
    (menu.bounded initial horizon scheduler) (fun _ _ => Set.toFinite _)
    (fun draw => app.transition_support_finite initial horizon scheduler _ draw.1)

instance historyFintype [Finite Principal] [app.FiniteNature initial scheduler] :
    Fintype (menu.protocol initial horizon scheduler).History := Fintype.ofFinite _

instance informationHistoryFintype [Finite Principal] [app.FiniteNature initial scheduler]
    (who : Principal)
    (site : (menu.information initial horizon scheduler).InformationSite who) :
    Fintype ((menu.information initial horizon scheduler).InformationHistory who site.1) := by
  classical
  infer_instance

variable [Fintype Principal]

/-- Canonical Bayes beliefs for a fully mixed profile of this finite instance. -/
def bayesAssessment : (menu.information initial horizon scheduler).BehavioralAssessment :=
  InformationModel.bayesAssessment _ (menu.uniformAssessment initial horizon scheduler).strategy
    (menu.uniform_fullyMixed initial horizon scheduler)
    (menu.decisionInformationAntichain initial horizon scheduler)

end Interaction.ReactiveApplication.ResponseMenu
