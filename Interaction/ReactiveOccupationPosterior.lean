/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveOccupationBayes

/-! # Actual information-site control posteriors across command counts -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) [NeZero horizon] (scheduler : app.Scheduler)
  [Finite (menu.protocol initial horizon scheduler).History]

local notation "model" => menu.information initial horizon scheduler

/-- Standard Bayes beliefs pushed to the complete actual control equal
conditioning the genuine bounded command-occupation law on full owner information. -/
theorem bayesBelief_state_eq_occupationPosterior
    (profile : ∀ who, (model).BehavioralPolicy who)
    (who : Principal) (site : (model).InformationSite who)
    (antichain : site.IsHistoryAntichain)
    (positive : 0 < (model).informationMass profile who site) :
    ((model).bayesBelief profile who site antichain positive).map
        (fun history => history.1.state) =
      fiberPosterior (app.occupationControlLaw scheduler
        (menu.decodeProfile initial horizon scheduler profile) initial horizon)
        (app.observe who) site.1 := by
  classical
  let first : PMF app.ProtocolState :=
    ((model).bayesBelief profile who site antichain positive).map
      (fun history => history.1.state)
  let second : PMF app.ProtocolState := fiberPosterior (app.occupationControlLaw scheduler
    (menu.decodeProfile initial horizon scheduler profile) initial horizon) (app.observe who) site.1
  change first = second
  ext state
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  let atom := fun current : app.ProtocolState => if state = current then (1 : ℝ) else 0
  have compared := menu.occupation_posterior_expect initial horizon scheduler profile who site
    antichain positive atom (by norm_num : 0 ≤ (1 : ℝ)) (fun current => by
      dsimp only [atom]
      split_ifs <;> norm_num)
  have mapped := (expect_map (fun history => history.1.state)
    ((model).bayesBelief profile who site antichain positive) atom).symm
  change expect ((model).bayesBelief profile who site antichain positive)
      (fun history => atom history.1.state) = _ at mapped
  rw [mapped] at compared
  have atomMean (law : PMF app.ProtocolState) : expect law atom = (law state).toReal := by
    unfold expect
    rw [tsum_eq_single state (fun other different => by simp [atom, Ne.symm different])]
    simp [atom]
  have firstAtom := atomMean first
  have secondAtom := atomMean second
  change expect second atom = expect first atom at compared
  change (first state).toReal = (second state).toReal
  exact firstAtom.symm.trans (compared.symm.trans secondAtom)

end Interaction.ReactiveApplication.ResponseMenu
