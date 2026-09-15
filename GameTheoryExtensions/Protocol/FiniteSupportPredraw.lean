/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.Information

/-! # Predrawing on a chosen finite set of information states

Randomization outside the chosen sets is replaced by specified deterministic
fallbacks. The mixed execution law equals that restricted behavioral law under
the protocol's acts-once condition. In particular, a finite union of reachable
sets can support one predraw law for several initial histories.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

def restrictProfile {ι : Type*} {E : ExecutionProtocol ι} (M : InformationModel E)
    (policy : (i : ι) → M.BehavioralPolicy i)
    (sites : (i : ι) → Finset (M.InfoState i)) (fallback : (i : ι) → M.Policy i) :
    (i : ι) → M.BehavioralPolicy i := fun i =>
  BehavioralPolicy.restrictRandomization M (policy i) (sites i) (fallback i)

theorem restrictProfile_apply_of_mem {ι : Type*} {E : ExecutionProtocol ι}
    (M : InformationModel E)
    (policy : (i : ι) → M.BehavioralPolicy i)
    (sites : (i : ι) → Finset (M.InfoState i)) (fallback : (i : ι) → M.Policy i)
    (i : ι) (info : M.InfoState i)
    (hmem : info ∈ sites i) : restrictProfile M policy sites fallback i info = policy i info := by
  classical
  unfold restrictProfile
  simp [BehavioralPolicy.restrictRandomization, hmem]

theorem runMixedFrom_restrictRandomization {ι : Type*} [Fintype ι] {E : ExecutionProtocol ι}
    (M : InformationModel E) (hactsOnce : M.ActsOnceWhereItMatters)
    (policy : (i : ι) → M.BehavioralPolicy i)
    (sites : (i : ι) → Finset (M.InfoState i)) (fallback : (i : ι) → M.Policy i)
    (fuel : Nat) (start : E.History) :
    M.runMixedFrom (fun i => (policy i).toMixedWithin (sites i) (fallback i))
        fuel start = M.runBehavioralFrom (restrictProfile M policy sites fallback) fuel start := by
  classical
  unfold BehavioralPolicy.toMixedWithin restrictProfile
  exact M.runMixedFrom_toMixedOn hactsOnce fuel _ sites fallback start (by
      intro i info hinfo
      simp [BehavioralPolicy.restrictRandomization, hinfo])

end GameTheory.Protocol.InformationModel
