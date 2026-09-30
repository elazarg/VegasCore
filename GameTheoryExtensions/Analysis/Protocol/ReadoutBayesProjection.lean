/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.BeliefTransport

/-! # Bayes projection of a readout through a focal selector

A focal selector resolves one player's private aliases for a prefix law. Its
own reach cancels from that player's Bayes belief, so the original native
profile has the same posterior over the readout as the selected profile.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

variable {Player : Type} [Fintype Player] {E T : ExecutionProtocol Player}
  (M : InformationModel E) (N : InformationModel T) {X : Type}

/-- A focal selector resolves one player's private aliases for the prefix
law. Its own reach cancels, so the original native profile has the same
posterior over source state, including along fully mixed approximants. -/
theorem bayesBelief_readout_at_depth_of_focal_selector
    (strategy : ∀ who, M.BehavioralPolicy who) (who : Player) (site : M.InformationSite who)
    (depth : Nat) (sameDepth : InformationSite.CommonDepth M site depth)
    (source : ∀ who, N.BehavioralPolicy who) (sourceSite : N.InformationSite who)
    (sourceDepth : Nat) (sourceClock : InformationSite.CommonDepth N sourceSite sourceDepth)
    (readout : E.History → X) (sourceReadout : T.History → X)
    (law : (M.runBehavioral strategy depth).map (M.informationReadout who site readout) =
      (N.runBehavioral source sourceDepth).map
        (N.informationReadout who sourceSite sourceReadout))
    (native : ∀ who, M.BehavioralPolicy who)
    (agree : ∀ other, other ≠ who → native other = strategy other)
    (nativeCommon : M.CommonPlayerReachAt native who site)
    (selectedCommon : M.CommonPlayerReachAt strategy who site)
    (rawAntichain : site.IsHistoryAntichain)
    (sourceAntichain : sourceSite.IsHistoryAntichain)
    (nativePositive : 0 < M.informationMass native who site)
    (sourcePositive : 0 < N.informationMass source who sourceSite) :
    (M.bayesBelief native who site rawAntichain nativePositive).map
        (fun history => readout history.1) =
      (N.bayesBelief source who sourceSite sourceAntichain sourcePositive).map
        (fun history => sourceReadout history.1) := by
  classical
  have mass := M.informationMass_readout_at_depth N strategy who site sourceSite readout
    sourceReadout depth sameDepth source sourceDepth sourceClock law
  have selectedPositive : 0 < M.informationMass strategy who site := by
    rw [mass]
    exact sourcePositive
  rw [M.bayesBelief_eq_of_eq_off native strategy who site rawAntichain agree nativeCommon
    selectedCommon nativePositive selectedPositive]
  exact M.bayesBelief_readout_at_depth N strategy who site sourceSite readout sourceReadout
    depth sameDepth source sourceDepth sourceClock law rawAntichain sourceAntichain
    selectedPositive sourcePositive

end GameTheory.Protocol.InformationModel
