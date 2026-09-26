/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ContinuationDeviation
import GameTheoryExtensions.Analysis.Protocol.FixedDepthBayes
import GameTheoryExtensions.Math.Probability.Tremble

/-! # A continuation switch preserves the probability of its starting branch

The branch is recognized from the player's current information or own-action
record. After its decision depth, its probability equals the original site's
reach mass, independently of the continuation policy selected on that branch.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type} [Fintype Player] {E : ExecutionProtocol Player}
  (M : InformationModel E)

/-- The selected decision is current or belongs to the player's own past. -/
def continuationBranch (who : Player) (site : M.InformationSite who) : Set E.History :=
  {history | M.infoOf who history.trace = site.1 ∨ site.1 ∈ M.actedAt who history.trace}

private theorem supported_reaches (profile : ∀ who, M.BehavioralPolicy who)
    (fuel : Nat) (start last : E.History)
    (supported : last ∈ (M.runBehavioralFrom profile fuel start).support) :
    E.ReachesWithin fuel start last := by
  induction fuel generalizing start with
  | zero =>
      rw [runBehavioralFrom, runRandomizedFor_zero, FinDist.mem_support_pure] at supported
      subst last
      exact .refl 0 start
  | succ fuel ih =>
      by_cases stopped : E.terminal start.state
      · rw [M.runBehavioralFrom_of_terminal profile _ stopped,
          FinDist.mem_support_pure] at supported
        subst last
        exact .refl _ start
      · rw [M.runBehavioralFrom_succ_of_not_terminal profile fuel stopped,
          FinDist.support_bind] at supported
        obtain ⟨draw, _, supported⟩ := Set.mem_iUnion₂.mp supported
        rw [FinDist.support_bindOnSupport] at supported
        obtain ⟨next, realized, supported⟩ := Set.mem_iUnion₂.mp supported
        exact .step draw.1 draw.2 realized (ih (start.extend draw.2 realized) supported)

omit [Fintype Player] in
private theorem reached_length_bound {fuel : Nat} {first last : E.History}
    (path : E.ReachesWithin fuel first last) : last.trace.length ≤ first.trace.length + fuel := by
  induction path with
  | refl => omega
  | step joint legal realized rest ih =>
      simp only [History.extend, Trace.length] at ih
      omega

/-- At a fixed decision-depth cut, every later supported history remembers
exactly whether this branch was selected. Early terminal histories are absorbed. -/
theorem continuationBranch_suffix_iff (profile : ∀ who, M.BehavioralPolicy who)
    (who : Player) (site : M.InformationSite who) (depth : Nat)
    (sameDepth : InformationSite.CommonDepth M site depth) (fuel : Nat)
    (first : E.History) (inPrefix : first ∈ (M.runBehavioral profile depth).support)
    (last : E.History) (suffix : last ∈ (M.runBehavioralFrom profile fuel first).support) :
    last ∈ M.continuationBranch who site ↔ M.infoOf who first.trace = site.1 := by
  have bound := reached_length_bound
    (M.supported_reaches profile depth E.initHistory first inPrefix)
  have before : first.trace.length ≤ depth := by
    simpa only [initHistory, Trace.length, zero_add] using bound
  have absent := M.site_not_recorded_before_depth who site depth sameDepth first before
  by_cases stopped : E.terminal first.state
  · rw [M.runBehavioralFrom_of_terminal profile fuel stopped, FinDist.mem_support_pure] at suffix
    subst last
    simp only [continuationBranch, Set.mem_ofPred_eq, absent, or_false]
  · have atDepth := M.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
      profile depth E.initHistory first inPrefix
    rcases atDepth with terminal | atDepth
    · exact False.elim (stopped terminal)
    · have depthEq : first.trace.length = depth := by
        simpa only [initHistory, Trace.length, zero_add] using atDepth
      have path := M.supported_reaches profile fuel first last suffix
      by_cases present : M.infoOf who first.trace = site.1
      · constructor
        · exact fun _ => present
        · intro _
          cases path with
          | refl => exact Or.inl present
          | step joint legal realized rest =>
              exact Or.inr (M.site_recorded_after_step site ⟨first, present⟩ legal realized rest)
      · have outside := M.site_unvisited_after_depth who site depth sameDepth path
          depthEq.ge present absent
        simp only [continuationBranch, Set.mem_ofPred_eq, outside.1, outside.2, present,
          or_self]

/-- The branch's mass is constant after its decision depth, even under
arbitrary later behavior and early termination. -/
theorem continuationBranch_probability [Finite E.History]
    (profile : ∀ who, M.BehavioralPolicy who) (who : Player) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)] (depth : Nat)
    (sameDepth : InformationSite.CommonDepth M site depth) (fuel : Nat) :
    (M.runBehavioral profile (depth + fuel)).probOf (M.continuationBranch who site) =
      M.informationMass profile who site := by
  classical
  rw [M.informationMass_eq_fixedDepth_probOf profile who site depth sameDepth]
  unfold runBehavioral
  rw [M.runBehavioralFrom_add, FinDist.probOf_bind, ← FinDist.expect_indicator_eq_probOf]
  apply FinDist.expect_congr
  intro first inPrefix
  rw [← FinDist.expect_indicator_eq_probOf]
  calc
    _ = (M.runBehavioralFrom profile fuel first).expect
        (fun _ => if M.infoOf who first.trace = site.1 then (1 : ℝ) else 0) := by
      apply FinDist.expect_congr
      intro last suffix
      rw [M.continuationBranch_suffix_iff profile who site depth sameDepth fuel
        first inPrefix last suffix]
    _ = _ := FinDist.expect_const ..

/-- Switching at a selected information set leaves its branch probability
equal to the original reach mass at every subsequent depth. -/
theorem switched_continuationBranch_probability [DecidableEq Player] [Finite E.History]
    (recall : M.PerfectRecall) (profile : ∀ who, M.BehavioralPolicy who)
    (who : Player) (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)] (alternative : M.BehavioralPolicy who)
    (depth : Nat) (sameDepth : InformationSite.CommonDepth M site depth) (fuel : Nat) :
    (M.runBehavioral (Profile.update (sig := M.behavioralSignature) profile who
      ((profile who).switchAt M alternative site)) (depth + fuel)).probOf
        (M.continuationBranch who site) = M.informationMass profile who site := by
  rw [M.continuationBranch_probability _ who site depth sameDepth fuel,
    M.informationMass_eq_fixedDepth_probOf _ who site depth sameDepth,
    M.run_switchAt_prefix recall profile who site alternative depth sameDepth,
    ← M.informationMass_eq_fixedDepth_probOf profile who site depth sameDepth]

end GameTheory.Protocol.InformationModel
