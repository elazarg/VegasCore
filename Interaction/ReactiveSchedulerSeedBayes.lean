/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveSchedulerSeedOccupation
import Interaction.ReactiveOccupationPosterior

/-! # Original scheduler-seed laws at actual finite information sites -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  {Seed : Type} (prior : PMF Seed) (family : Seed → app.Scheduler)
  (initial : PMF app.State) (horizon : Nat) [NeZero horizon]

local notation "mixture" => ReactiveApplication.schedulerMixture app prior family
local notation "model" => ReactiveApplication.ResponseMenu.information menu initial horizon
  (ReactiveApplication.SchedulerImplementation.scheduler mixture)
local notation "players" profile =>
  ReactiveApplication.ResponseMenu.decodeProfile menu initial horizon
    (ReactiveApplication.SchedulerImplementation.scheduler mixture) profile

variable [Finite (GameTheory.Protocol.ExecutionProtocol.History
  (ReactiveApplication.ResponseMenu.protocol menu initial horizon
    (ReactiveApplication.SchedulerImplementation.scheduler
      (ReactiveApplication.schedulerMixture app prior family))))]

/-- Standard finite-site Bayes beliefs tagged by the actual scheduler posterior
are exactly the conditional original persistent-seed occupation law. -/
theorem bayesBelief_seededOccupation
    (profile : ∀ who, (model).BehavioralPolicy who)
    (who : Principal) (site : (model).InformationSite who)
    (positive : 0 < (model).informationMass profile who site) :
    fiberPosterior
      (prior.bind fun seed =>
        (app.occupationControlLaw (family seed) (players profile) initial horizon).map
          fun state => (state, seed))
      (fun outcome => app.observe who outcome.1) site.1 =
      ((((model).bayesBelief profile who site
        (menu.decisionInformationAntichain initial horizon (mixture).scheduler who site)
        positive).map (β := app.ProtocolState) (fun history => history.1.state)).bind fun state =>
          (match state with
          | none => prior
          | some current => (mixture).posterior current.execution.environmentRecall).map
            (Prod.mk state)) := by
  classical
  let law := app.occupationControlLaw (mixture).scheduler (players profile) initial horizon
  let draws := fun state : app.ProtocolState => match state with
    | none => prior
    | some current => (mixture).posterior current.execution.environmentRecall
  have antichain := menu.decisionInformationAntichain initial horizon
    (mixture).scheduler who site
  have massPositive : 0 < ((model).informationMass profile who site).toReal :=
    ENNReal.toReal_pos (ne_of_gt positive)
      (ne_of_lt (lt_of_le_of_lt
        ((model).informationMass_le_one profile who site antichain) ENNReal.one_lt_top))
  have marginal := menu.occupation_information_mass initial horizon (mixture).scheduler
    profile who site
  have marginalPositive : 0 < ((law.map (app.observe who)) site.1).toReal := by
    rw [marginal]
    exact div_pos massPositive (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne horizon)))
  have present : site.1 ∈ (law.map (app.observe who)).support :=
    (PMF.apply_pos_iff _ _).mp (ENNReal.toReal_pos_iff.mp marginalPositive).1
  have conditioned := fiberPosterior_bind_of_observation law
    (fun state => (draws state).map (Prod.mk state)) (app.observe who)
    (fun outcome => app.observe who outcome.1)
    (by
      intro state _ outcome supported
      obtain ⟨seed, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      rw [← equal]) site.1 present
  have bayes := menu.bayesBelief_state_eq_occupationPosterior initial horizon
    (mixture).scheduler profile who site antichain positive
  rw [app.schedulerMixture_occupation_joint]
  have tagged := congrArg (fun distribution : PMF app.ProtocolState =>
    distribution.bind fun state => (draws state).map (Prod.mk state)) bayes.symm
  dsimp only [law, draws] at conditioned tagged
  convert conditioned.trans tagged using 1

end Interaction.ReactiveApplication.ResponseMenu
