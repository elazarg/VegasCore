/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveResponseEmbedding
import GameTheory.Analysis.Protocol.BeliefTransport

/-! # Reach and Bayes laws under finite response-menu embedding

The existing complete-history embedding law supplies exact reach fibers and
Bayes transport. Histories outside the finite menu image have zero reach under
the embedded profile.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

theorem runBehavioral_embed
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (fuel : Nat) :
    ((menu.information initial horizon scheduler).runBehavioral profile fuel).map
        (menu.toRawHistory initial horizon scheduler) =
      (app.information initial horizon scheduler).runBehavioral
        (fun who => menu.embedPolicy initial horizon scheduler who (profile who)) fuel := by
  exact menu.run_embed initial horizon scheduler profile fuel
    (menu.protocol initial horizon scheduler).initHistory

/-- Embedding a finite-menu history preserves its actual reach weight. -/
theorem historyReachWeight_toRawHistory
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol initial horizon scheduler).History) :
    (app.information initial horizon scheduler).historyReachWeight
        (fun who => menu.embedPolicy initial horizon scheduler who (profile who))
        (menu.toRawHistory initial horizon scheduler history) =
      (menu.information initial horizon scheduler).historyReachWeight profile history := by
  classical
  change (app.information initial horizon scheduler).runBehavioral
      (fun who => menu.embedPolicy initial horizon scheduler who (profile who))
      (menu.toRawTrace initial horizon scheduler history.trace).length
      (menu.toRawHistory initial horizon scheduler history) =
    (menu.information initial horizon scheduler).runBehavioral profile history.trace.length history
  rw [menu.toRawTrace_length,
    ← menu.runBehavioral_embed initial horizon scheduler profile history.trace.length]
  exact pmf_map_apply_of_injective _ (menu.toRawHistory_injective initial horizon scheduler) history

/-- The entire finite information event has the same mass in its raw image. -/
theorem informationMass_rawSite
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Principal) (site : (menu.information initial horizon scheduler).InformationSite who) :
    (menu.information initial horizon scheduler).informationMass profile who site =
      (app.information initial horizon scheduler).informationMass
        (fun player => menu.embedPolicy initial horizon scheduler player (profile player)) who
        (menu.rawSite initial horizon scheduler who site) := by
  classical
  apply InformationModel.informationMass_projection
    (menu.information initial horizon scheduler) (app.information initial horizon scheduler)
    profile (fun player => menu.embedPolicy initial horizon scheduler player (profile player))
    (menu.toRawHistory initial horizon scheduler)
    (fun history => menu.toRawTrace_length initial horizon scheduler history.trace)
    (menu.runBehavioral_embed initial horizon scheduler profile) who site
    (menu.rawSite initial horizon scheduler who site)
  · intro history observed
    exact (menu.info_toRawTrace initial horizon scheduler who history.trace).trans observed
  · intro history _positive observed
    exact (menu.info_toRawTrace initial horizon scheduler who history.trace).symm.trans observed

/-- The actual Bayes belief of a bounded-menu decision embeds into the raw
belief exactly. The generic reach transport supplies all zero-weight fibers. -/
theorem bayesBelief_rawSite
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Principal) (site : (menu.information initial horizon scheduler).InformationSite who)
    (positive : 0 < (menu.information initial horizon scheduler).informationMass profile who site) :
    ((menu.information initial horizon scheduler).bayesBelief profile who site
      (menu.decisionInformationAntichain initial horizon scheduler who site) positive).map
        (menu.rawInformationHistory initial horizon scheduler who site) =
      (app.information initial horizon scheduler).bayesBelief
        (fun player => menu.embedPolicy initial horizon scheduler player (profile player)) who
        (menu.rawSite initial horizon scheduler who site)
        (app.decisionInformationAntichain initial horizon scheduler who
          (menu.rawSite initial horizon scheduler who site)) (by
          rw [← menu.informationMass_rawSite initial horizon scheduler profile who site]
          exact positive) := by
  classical
  exact InformationModel.bayesBelief_projection
    (menu.information initial horizon scheduler) (app.information initial horizon scheduler)
    profile (fun player => menu.embedPolicy initial horizon scheduler player (profile player))
    (menu.toRawHistory initial horizon scheduler)
    (fun history => menu.toRawTrace_length initial horizon scheduler history.trace)
    (menu.runBehavioral_embed initial horizon scheduler profile) who site
    (menu.rawSite initial horizon scheduler who site)
    (fun history observed =>
      (menu.info_toRawTrace initial horizon scheduler who history.trace).trans observed)
    (fun history _positive observed =>
      (menu.info_toRawTrace initial horizon scheduler who history.trace).symm.trans observed)
    (menu.decisionInformationAntichain initial horizon scheduler who site)
    (app.decisionInformationAntichain initial horizon scheduler who
      (menu.rawSite initial horizon scheduler who site)) positive (by
      rw [← menu.informationMass_rawSite initial horizon scheduler profile who site]
      exact positive)

end Interaction.ReactiveApplication.ResponseMenu
