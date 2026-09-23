/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Core.IncentiveCone
import GameTheoryExtensions.Protocol.BehavioralContinuation

/-! # A necessary and sufficient SPE preservation criterion

For a finite observed outcome space and fixed source and target profiles,
preservation for every utility is equivalent to inclusion of every target
continuation incentive difference in the cone of source differences for the
same player. Roots and deviations use the canonical behavioral SPE definition.

This is a semantic criterion, not an operational service contract. It permits
combining source incentive inequalities without matching continuation laws.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

universe uι us ua up uq uk us' ua' up' uq' uk' uv

variable {ι : Type uι} [DecidableEq ι]
  {E : ExecutionProtocol.{uι, us, ua} ι}
  (M : InformationModel.{uι, us, ua, up, uq, uk} E)
  (single : ∀ (state : E.State) {first second : ι},
    E.active state first → E.active state second → first = second)

/-- A whole replacement policy at an actual proper subgame root. -/
abbrev ContinuationDeviation (who : ι) :=
  {root : E.History // M.IsSubgameRoot root} × M.BehavioralPolicy who

def continuationComparison {Observation : Type uv} (observe : E.History → Observation)
    (bound : Nat) (profile : Profile M.behavioralSignature) (who : ι)
    (deviation : M.ContinuationDeviation who) : IncentiveComparison Observation where
  prescribed := (M.runSingleMoverBehavioralFrom single profile bound deviation.1.val).map observe
  alternative := (M.runSingleMoverBehavioralFrom single (Profile.update profile who deviation.2)
    bound deviation.1.val).map observe

theorem isBehavioralSubgamePerfect_iff_comparisons
    {Observation : Type uv} (observe : E.History → Observation)
    {bound : Nat} (bounded : E.BoundedHorizon bound)
    (profile : Profile M.behavioralSignature) (utility : Observation → ι → ℝ) :
    M.IsBehavioralSubgamePerfect single bounded profile
        (fun history who => utility (observe history) who) ↔
      ∀ who deviation,
        (M.continuationComparison single observe bound profile who deviation).Holds
          (utility · who) := by
  rw [M.isBehavioralSubgamePerfect_iff single bounded]
  simp only [continuationComparison, IncentiveComparison.Holds, FinDist.expect_map]
  constructor
  · intro perfect who ⟨⟨root, proper⟩, alternative⟩
    exact perfect root proper who alternative
  · intro respected root proper who alternative
    exact respected who (⟨root, proper⟩, alternative)

variable {T : ExecutionProtocol.{uι, us', ua'} ι}
  (N : InformationModel.{uι, us', ua', up', uq', uk'} T)
  (targetSingle : ∀ (state : T.State) {first second : ι},
    T.active state first → T.active state second → first = second)

/-- An exact criterion for fixed profiles, uniform over utilities. Applying it
to each source profile and its image characterizes a fixed compiler. -/
theorem behavioral_spe_preservation_iff_cone
    {Observation : Type uv} [Fintype Observation]
    (sourceObserve : E.History → Observation) (targetObserve : T.History → Observation)
    {sourceBound targetBound : Nat} (sourceBounded : E.BoundedHorizon sourceBound)
    (targetBounded : T.BoundedHorizon targetBound)
    (sourceProfile : Profile M.behavioralSignature)
    (targetProfile : Profile N.behavioralSignature) :
    (∀ utility : Observation → ι → ℝ,
      M.IsBehavioralSubgamePerfect single sourceBounded sourceProfile
        (fun history who => utility (sourceObserve history) who) →
      N.IsBehavioralSubgamePerfect targetSingle targetBounded targetProfile
        (fun history who => utility (targetObserve history) who)) ↔
    ∀ who (deviation : N.ContinuationDeviation who),
      (N.continuationComparison targetSingle targetObserve targetBound targetProfile who
        deviation).difference ∈ IncentiveComparison.cone
          (M.continuationComparison single sourceObserve sourceBound sourceProfile who) := by
  simp only [M.isBehavioralSubgamePerfect_iff_comparisons single sourceObserve sourceBounded,
    N.isBehavioralSubgamePerfect_iff_comparisons targetSingle targetObserve targetBounded]
  constructor
  · intro preserves who deviation
    rw [IncentiveComparison.mem_cone_iff]
    intro utility respected
    let utilities : Observation → ι → ℝ := fun outcome player =>
      if player = who then utility outcome else 0
    have source : ∀ player replacement,
        (M.continuationComparison single sourceObserve sourceBound sourceProfile
          player replacement).Holds (utilities · player) := by
      intro player replacement
      by_cases same : player = who
      · subst player
        simpa only [utilities, ↓reduceIte] using respected replacement
      · simp only [IncentiveComparison.Holds, utilities, same, ↓reduceIte,
          FinDist.expect_const, le_refl]
    simpa only [utilities, ↓reduceIte] using preserves utilities source who deviation
  · intro included utility source who deviation
    exact (IncentiveComparison.mem_cone_iff _ _).mp (included who deviation)
      (utility · who) (source who)

end GameTheory.Protocol.InformationModel
