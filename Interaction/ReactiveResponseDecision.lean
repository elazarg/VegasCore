/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseBelief

/-! # Positive raw information events under finite response menus -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- Positive probability of a genuine raw decision under an embedded finite
policy supplies a genuine finite-menu decision with the same complete input. -/
theorem isDecisionInfo_of_raw_mass_pos
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Principal) (site : (app.information initial horizon scheduler).InformationSite who)
    (positive : 0 < (app.information initial horizon scheduler).informationMass
      (fun player => menu.embedPolicy initial horizon scheduler player (profile player)) who site) :
    (menu.information initial horizon scheduler).IsDecisionInfo who site.1 := by
  classical
  obtain ⟨history, reached⟩ :=
    (app.information initial horizon scheduler).informationMass_pos_iff _ who site |>.mp positive
  have supported : history.1 ∈ ((app.information initial horizon scheduler).runBehavioral
      (fun player => menu.embedPolicy initial horizon scheduler player (profile player))
      history.1.trace.length).support := (PMF.apply_pos_iff _ _).mp reached
  rw [← menu.runBehavioral_embed initial horizon scheduler profile history.1.trace.length,
    PMF.mem_support_map_iff] at supported
  obtain ⟨finiteHistory, _supported, same⟩ := supported
  have observed : (menu.information initial horizon scheduler).infoOf who finiteHistory.trace =
      site.1 := by
    rw [← menu.info_toRawTrace initial horizon scheduler who finiteHistory.trace]
    exact (congrArg (fun original : (app.protocol initial horizon scheduler).History =>
      (app.information initial horizon scheduler).infoOf who original.trace) same).trans history.2
  have running : ¬ (menu.protocol initial horizon scheduler).terminal finiteHistory.state := by
    have rawRunning := app.informationSite_allNonterminal initial horizon scheduler who site history
    have states := congrArg History.state same
    exact fun ended => rawRunning (states ▸ ended)
  have someInfo : site.1.isSome = true := by
    obtain ⟨witness, _running, response, permitted⟩ := site.2
    change (some response).isSome = site.1.isSome at permitted
    exact permitted.symm
  cases inputEq : site.1 with
  | none => simp only [inputEq, Option.isSome_none, Bool.false_eq_true] at someInfo
  | some data =>
      obtain ⟨response, permitted⟩ := menu.nonempty who data.1 data.2
      refine ⟨⟨finiteHistory, observed.trans inputEq⟩, running, response, ?_⟩
      change ∃ action ∈ menu.actions who data.1 data.2, some response = some action
      exact ⟨response, permitted, rfl⟩

end Interaction.ReactiveApplication.ResponseMenu
