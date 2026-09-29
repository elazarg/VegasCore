/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.FixedDepthBayes
import GameTheoryExtensions.Analysis.Protocol.CounterfactualBeliefs
import Mathlib.Algebra.BigOperators.Field
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Support

/-! # Bayes projection to a common state or readout

Corresponding checkpoint laws need only agree on the state relevant to future
play. Transporting the conditional state law does not require reconstructing
the complete source history. A marked readout records both that state and
membership in the information event being conditioned on.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] {E T : ExecutionProtocol Player}
  (M : InformationModel E) (N : InformationModel T) {X : Type}

open Classical in
/-- Retain a readout on one information event, and mark all other histories
as outside that event. This is a proof readout, not an added observation. -/
def informationReadout (who : Player) (site : M.InformationSite who)
    (readout : E.History → X) (history : E.History) : Option X :=
  if M.infoOf who history.trace = site.1 then some (readout history) else none

variable [Finite E.History]
  (strategy : ∀ who, M.BehavioralPolicy who) (who : Player)
  (site : M.InformationSite who) [Fintype (M.InformationHistory who site.1)]
  (depth : Nat) (sameDepth : ∀ history : M.InformationHistory who site.1,
    history.1.trace.length = depth)

include sameDepth in
theorem informationReadout_mass (readout : E.History → X) :
    (((M.runBehavioral strategy depth).map
      (M.informationReadout who site readout)).toOuterMeasure {value | value.isSome}).toReal =
      M.informationMass strategy who site := by
  classical
  rw [M.informationMass_eq_fixedDepth_toOuterMeasure strategy who site depth sameDepth,
    FinDist.probOf_map]
  congr 1
  ext history
  by_cases observed : M.infoOf who history.trace = site.1 <;>
    simp [informationReadout, observed]

include sameDepth in
open Classical in
private theorem informationReadout_prob (readout : E.History → X) (value : X) :
    (((M.runBehavioral strategy depth).map
      (M.informationReadout who site readout)) (some value)).toReal =
      ∑ history : M.InformationHistory who site.1,
        (M.historyReachWeight strategy history.1).toReal *
          (if value = readout history.1 then 1 else 0) := by
  classical
  let := Fintype.ofFinite E.History
  rw [toReal_map_apply, expect_eq_sum]
  have terms (history : E.History) :
      ((M.runBehavioral strategy depth) history).toReal *
          (if some value = M.informationReadout who site readout history then 1 else 0) =
        if M.infoOf who history.trace = site.1 then
          ((M.runBehavioral strategy depth) history).toReal *
            (if value = readout history then 1 else 0) else 0 := by
    by_cases observed : M.infoOf who history.trace = site.1 <;>
      simp [informationReadout, observed]
  simp_rw [terms]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype _ (p := fun history => M.infoOf who history.trace = site.1)
    (by intro history; simp) _]
  apply Finset.sum_congr rfl
  intro history _
  rw [historyReachWeight, sameDepth history]

include sameDepth in
/-- The posterior probability of a state is its joint probability with the
information event, divided by the information event's mass. -/
theorem bayesBelief_readout_prob (readout : E.History → X)
    (antichain : site.IsHistoryAntichain)
    (positive : 0 < M.informationMass strategy who site) (value : X) :
    (((M.bayesBelief strategy who site antichain positive).map
      (fun history => readout history.1)) value).toReal =
      (((M.runBehavioral strategy depth).map
        (M.informationReadout who site readout)) (some value)).toReal /
          M.informationMass strategy who site := by
  classical
  rw [toReal_map_apply, expect_eq_sum,
    M.informationReadout_prob strategy who site depth sameDepth readout value,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro history _
  rw [M.bayesBelief_apply]
  ring

variable [Finite T.History]
  (source : ∀ who, N.BehavioralPolicy who)
  (sourceSite : N.InformationSite who)
  [Fintype (N.InformationHistory who sourceSite.1)]
  (sourceDepth : Nat)
  (sourceClock : ∀ history : N.InformationHistory who sourceSite.1,
    history.1.trace.length = sourceDepth)
  (readout : E.History → X) (sourceReadout : T.History → X)
  (law : (M.runBehavioral strategy depth).map (M.informationReadout who site readout) =
    (N.runBehavioral source sourceDepth).map
      (N.informationReadout who sourceSite sourceReadout))

include sameDepth sourceClock law in
theorem informationMass_readout_at_depth :
    M.informationMass strategy who site = N.informationMass source who sourceSite := by
  classical
  have mass := congrArg (fun distribution => (distribution.toOuterMeasure {value | value.isSome}).toReal) law
  rw [M.informationReadout_mass strategy who site depth sameDepth readout,
    N.informationReadout_mass source who sourceSite sourceDepth sourceClock sourceReadout] at mass
  exact mass

include sameDepth sourceClock law in
/-- Matching state-and-information-event laws at the actual decision depths
transport the Bayes posterior over that state. Complete histories may differ. -/
theorem bayesBelief_readout_at_depth
    (rawAntichain : site.IsHistoryAntichain)
    (sourceAntichain : sourceSite.IsHistoryAntichain)
    (rawPositive : 0 < M.informationMass strategy who site)
    (sourcePositive : 0 < N.informationMass source who sourceSite) :
    (M.bayesBelief strategy who site rawAntichain rawPositive).map
        (fun history => readout history.1) =
      (N.bayesBelief source who sourceSite sourceAntichain sourcePositive).map
        (fun history => sourceReadout history.1) := by
  classical
  apply pmf_ext_toReal
  intro value
  rw [M.bayesBelief_readout_prob strategy who site depth sameDepth readout,
    N.bayesBelief_readout_prob source who sourceSite sourceDepth sourceClock sourceReadout,
    law, M.informationMass_readout_at_depth N strategy who site depth sameDepth source
      sourceSite sourceDepth sourceClock readout sourceReadout law]

omit [Finite E.History] [Finite T.History]
  [Fintype (M.InformationHistory who site.1)]
  [Fintype (N.InformationHistory who sourceSite.1)] in
/-- An ordinary readout law suffices when one predicate on that readout
characterizes the two information events on their actual prefix supports. -/
theorem informationReadout_law_of_fiber
    (predicate : X → Prop)
    (unmarked : (M.runBehavioral strategy depth).map readout =
      (N.runBehavioral source sourceDepth).map sourceReadout)
    (rawFiber : ∀ history ∈ (M.runBehavioral strategy depth).support,
      M.infoOf who history.trace = site.1 ↔ predicate (readout history))
    (sourceFiber : ∀ history ∈ (N.runBehavioral source sourceDepth).support,
      N.infoOf who history.trace = sourceSite.1 ↔ predicate (sourceReadout history)) :
    (M.runBehavioral strategy depth).map (M.informationReadout who site readout) =
      (N.runBehavioral source sourceDepth).map
        (N.informationReadout who sourceSite sourceReadout) := by
  classical
  let mark (value : X) := if predicate value then some value else none
  calc
    _ = ((M.runBehavioral strategy depth).map readout).map mark := by
      rw [PMF.map_comp]
      apply map_congr_on_support _
      intro history supported
      simp only [informationReadout, Function.comp_apply, mark, rawFiber history supported]
    _ = ((N.runBehavioral source sourceDepth).map sourceReadout).map mark :=
      congrArg (fun distribution => distribution.map mark) unmarked
    _ = _ := by
      rw [PMF.map_comp]
      apply map_congr_on_support _
      intro history supported
      simp only [informationReadout, Function.comp_apply, mark, sourceFiber history supported]

include sameDepth sourceClock law in
/-- A focal selector resolves one player's private aliases for the prefix
law. Its own reach cancels, so the original native profile has the same
posterior over source state, including along fully mixed approximants. -/
theorem bayesBelief_readout_at_depth_of_focal_selector
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
  have mass := M.informationMass_readout_at_depth N strategy who site depth sameDepth source
    sourceSite sourceDepth sourceClock readout sourceReadout law
  have selectedPositive : 0 < M.informationMass strategy who site := by
    rw [mass]
    exact sourcePositive
  rw [M.bayesBelief_eq_of_eq_off native strategy who site rawAntichain agree nativeCommon
    selectedCommon nativePositive selectedPositive]
  exact M.bayesBelief_readout_at_depth N strategy who site depth sameDepth source sourceSite
    sourceDepth sourceClock readout sourceReadout law rawAntichain sourceAntichain
    selectedPositive sourcePositive

end GameTheory.Protocol.InformationModel
