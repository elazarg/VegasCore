/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory.Languages.FOSG.Kuhn
import Vegas.Game
import Vegas.Runtime.DeviationAdequacy

/-!
# Kuhn correspondence for Vegas games

The GameTheory protocol layer proves unilateral, opponent-preserving Kuhn
laws directly on `InformationModel`.  This module packages those laws as exact
deviation-adequacy certificates between a Vegas game's behavioral form and the
mixed extension of its pure-policy form.

Perfect recall is an explicit hypothesis.  VegasCore has not yet proved it for
the event-graph observation model, so these certificates cannot be instantiated
for every compiled program merely from `WFProgram`.
-/

noncomputable section

namespace Vegas.Game

open GameTheory
open GameTheory.Protocol

universe uPlayer uState uAction uPublic uPrivate uInfo

variable {Player : Type uPlayer} [Fintype Player] [DecidableEq Player]
variable
  (G : Game.{uPlayer, uState, uAction, uPublic, uPrivate, uInfo} Player)

/-- Compile behavioral policies to independently predrawn pure policies.
Under perfect recall, every unilateral mixed deviation is realized by its
behavioral reading while all opponents remain fixed. -/
def behavioralToMixedPureAdequacy
    [∀ who, Fintype (G.arena.information.InfoState who)]
    [∀ who, DecidableEq (G.arena.information.InfoState who)]
    (recall : G.arena.information.PerfectRecall) :
    Runtime.DeviationAdequacy G.behavioral G.mixedPure where
  compileStrategy := fun _who strategy => strategy.toMixed
  backtranslateStrategy := fun _who strategy =>
    InformationModel.MixedPolicy.toBehavioral
      (M := G.arena.information) strategy
  decodeOutcome := fun history : G.arena.History => history
  utility_eq := rfl
  honest_law := by
    intro profile
    change
      GameTheory.Math.Probability.FinDist.map
          (id : G.arena.History → G.arena.History)
          (G.arena.information.runMixed
            (fun who => (profile who).toMixed) G.horizon) =
        G.arena.information.runBehavioral profile G.horizon
    rw [GameTheory.Math.Probability.FinDist.map_id]
    exact
      G.arena.information.runMixed_toMixed
        (G.arena.information.actsOnceWhereItMatters_of_perfectRecall recall)
        profile G.horizon
  deviation_law := by
    intro profile who replacement
    change
      GameTheory.Math.Probability.FinDist.map
          (id : G.arena.History → G.arena.History)
          (G.arena.information.runMixed
            (Profile.update (fun player => (profile player).toMixed)
              who replacement) G.horizon) =
        G.arena.information.runBehavioral
          (Profile.update profile who
            (InformationModel.MixedPolicy.toBehavioral
              (M := G.arena.information) replacement)) G.horizon
    rw [GameTheory.Math.Probability.FinDist.map_id]
    exact
      G.arena.information.kuhn_behavioral_update_toMixed
        recall profile who replacement G.horizon

/-- Read a mixed pure-policy profile behaviorally. Under perfect recall, every
unilateral behavioral deviation is realized by predrawing that deviator's
local policy while all opponents remain fixed. -/
def mixedPureToBehavioralAdequacy
    [∀ who, Fintype (G.arena.information.InfoState who)]
    [∀ who, DecidableEq (G.arena.information.InfoState who)]
    (recall : G.arena.information.PerfectRecall) :
    Runtime.DeviationAdequacy G.mixedPure G.behavioral where
  compileStrategy := fun _who strategy =>
    InformationModel.MixedPolicy.toBehavioral
      (M := G.arena.information) strategy
  backtranslateStrategy := fun _who strategy => strategy.toMixed
  decodeOutcome := fun history : G.arena.History => history
  utility_eq := rfl
  honest_law := by
    intro profile
    change
      GameTheory.Math.Probability.FinDist.map
          (id : G.arena.History → G.arena.History)
          (G.arena.information.runBehavioral
            (fun who => InformationModel.MixedPolicy.toBehavioral
              (M := G.arena.information) (profile who)) G.horizon) =
        G.arena.information.runMixed profile G.horizon
    rw [GameTheory.Math.Probability.FinDist.map_id]
    exact
      (G.arena.information.runMixed_toBehavioral
        (InformationModel.constrainsAlike_of_perfectRecall recall)
        G.horizon profile).symm
  deviation_law := by
    intro profile who replacement
    change
      GameTheory.Math.Probability.FinDist.map
          (id : G.arena.History → G.arena.History)
          (G.arena.information.runBehavioral
            (Profile.update
              (fun player => InformationModel.MixedPolicy.toBehavioral
                (M := G.arena.information) (profile player))
              who replacement) G.horizon) =
        G.arena.information.runMixed
          (Profile.update profile who replacement.toMixed) G.horizon
    rw [GameTheory.Math.Probability.FinDist.map_id]
    exact
      G.arena.information.kuhn_mixed_update_toBehavioral
        recall profile who replacement G.horizon

end Vegas.Game
