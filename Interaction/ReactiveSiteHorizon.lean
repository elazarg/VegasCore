/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRoundReachability

/-! # Positive environmental horizon at genuine owner decisions -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol

variable {Principal : Type} [DecidableEq Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- A genuine owner decision requires an actual environment command, so the
scheduler horizon is positive without any fixed-calendar assumption. -/
theorem informationSite_horizon_pos (who : Principal)
    (site : (menu.information initial horizon scheduler).InformationSite who) : 0 < horizon := by
  obtain ⟨history, _, response, legal⟩ := site.2
  have raw := (menu.rawChoice initial horizon scheduler who site.1 ⟨some response, legal⟩).2
  have infoSome : site.1.isSome = true := by
    change (some response).isSome = site.1.isSome at raw
    exact raw.symm
  have observed := menu.info initial horizon scheduler who history.1.trace
  have seen : (app.observe who history.1.state).isSome := by
    change (menu.information initial horizon scheduler).infoOf who history.1.trace =
      app.observe who history.1.state at observed
    exact (congrArg Option.isSome (observed.symm.trans history.2)).trans infoSome
  have acting := (app.observe_isSome who history.1.state).mp seen
  cases stateEq : history.1.state with
  | none => simp only [stateEq, ReactiveApplication.actor, Option.bind_none, reduceCtorEq] at acting
  | some control =>
      have trace : (menu.protocol initial horizon scheduler).Trace (some control) :=
        stateEq ▸ history.1.trace
      have supported := menu.roundSupported_uniform initial horizon scheduler trace
      rw [stateEq] at acting
      change control.actor = some who at acting
      dsimp only [ReactiveApplication.RoundSupported] at supported
      rw [acting] at supported
      obtain ⟨accounted, count, prior, command, clock, _⟩ := supported
      omega

end Interaction.ReactiveApplication.ResponseMenu
