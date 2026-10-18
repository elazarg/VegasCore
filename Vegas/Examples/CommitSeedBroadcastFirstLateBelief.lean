/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastFirstLateReferenceDensity
import Vegas.Examples.CommitSeedBroadcastQuietHistoryBound

/-! # The actual assessed first-late bad-service bound -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability Filter

/-- Actual complete information-history likelihoods obey the bad-service bound
under every raw profile. Early-helper histories remain in the full denominator. -/
theorem firstLate_bad_reach_le
    (profile : ∀ observer, rawModel.BehavioralPolicy observer)
    (owner : Player) (site : rawModel.InformationSite owner)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : site.1 = some (past, view)) (length : past.length = 1)
    (original : view.application.2.attempt = originalAttempt)
    (clock : view.application.2.native.clock = 2) (empty : view.receipts = []) :
    (∑ history : rawModel.InformationHistory owner site.1,
      (rawModel.historyReachWeight profile history.1).toReal *
        firstLateBadValue history.1.state) ≤
      (271 / 1000 : ℝ) * ∑ history : rawModel.InformationHistory owner site.1,
        (rawModel.historyReachWeight profile history.1).toReal := by
  have comparison := firstLate_reference_reach_comparison profile owner site past view observed
    original clock empty
  have reference := quiet_native_bad_reach_le (initialQuietProfile profile)
    (initialQuietProfile_initial profile) owner site past view observed length original clock
  let density := initialQuietReach (rawMenu.decodeProfile initial horizon scheduler profile)
  have densityNonnegative : 0 ≤ density := initialQuietReach_nonnegative _
  rw [comparison.1]
  calc
    _ ≤ density * ((271 / 1000 : ℝ) *
        ∑ history : rawModel.InformationHistory owner site.1,
          (rawModel.historyReachWeight (initialQuietProfile profile) history.1).toReal) :=
      mul_le_mul_of_nonneg_left reference densityNonnegative
    _ = (271 / 1000 : ℝ) * (density *
        ∑ history : rawModel.InformationHistory owner site.1,
          (rawModel.historyReachWeight (initialQuietProfile profile) history.1).toReal) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left comparison.2 (by norm_num)

/-- Bayes is computed from the original full native information fiber. The
initial quiet probability may be arbitrarily small and has already cancelled. -/
theorem firstLate_bayes_bad_le
    (profile : ∀ observer, rawModel.BehavioralPolicy observer)
    (owner : Player) (site : rawModel.InformationSite owner)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : site.1 = some (past, view)) (length : past.length = 1)
    (original : view.application.2.attempt = originalAttempt)
    (clock : view.application.2.native.clock = 2) (empty : view.receipts = [])
    (positive : 0 < rawModel.informationMass profile owner site) :
    expect (rawModel.bayesBelief profile owner site
      (rawMenu.decisionInformationAntichain initial horizon scheduler owner site) positive)
      (fun history => firstLateBadValue history.1.state) ≤ (271 / 1000 : ℝ) := by
  classical
  have bound := firstLate_bad_reach_le profile owner site past view observed length
    original clock empty
  have massEq : (rawModel.informationMass profile owner site).toReal =
      ∑ history : rawModel.InformationHistory owner site.1,
        (rawModel.historyReachWeight profile history.1).toReal := by
    change (∑' history : rawModel.InformationHistory owner site.1,
      rawModel.historyReachWeight profile history.1).toReal = _
    exact (ENNReal.tsum_toReal_eq (fun history : rawModel.InformationHistory owner site.1 =>
      PMF.apply_ne_top (rawModel.runBehavioral profile history.1.trace.length) history.1)).trans
        (tsum_fintype _)
  have denominatorPositive : 0 < (rawModel.informationMass profile owner site).toReal :=
    ENNReal.toReal_pos positive.ne' (ne_of_lt (lt_of_le_of_lt
      (rawModel.informationMass_le_one profile owner site
        (rawMenu.decisionInformationAntichain initial horizon scheduler owner site))
      ENNReal.one_lt_top))
  have normalized : expect (rawModel.bayesBelief profile owner site
      (rawMenu.decisionInformationAntichain initial horizon scheduler owner site) positive)
      (fun history => firstLateBadValue history.1.state) =
      (∑ history : rawModel.InformationHistory owner site.1,
        (rawModel.historyReachWeight profile history.1).toReal *
          firstLateBadValue history.1.state) /
            (rawModel.informationMass profile owner site).toReal := by
    simp only [expect, tsum_fintype, rawModel.bayesBelief_apply, ENNReal.toReal_div]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro history _member
    ring
  rw [normalized]
  apply (div_le_iff₀ denominatorPositive).mpr
  rwa [massEq]

/-- Every sequentially consistent native assessment has bad-service belief at
most 271/1000 at a genuine original first-late empty-receipt full input. The
approximating strategies are fully mixed raw strategies, with their original
initialized seed posterior; they are not assumed to choose the initial WAITs. -/
theorem assessed_firstLate_bad_le
    (assessment : rawModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent
      (rawMenu.decisionInformationAntichain initial horizon scheduler))
    (owner : Player) (site : rawModel.InformationSite owner)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : site.1 = some (past, view)) (length : past.length = 1)
    (original : view.application.2.attempt = originalAttempt)
    (clock : view.application.2.native.clock = 2) (empty : view.receipts = []) :
    expect (assessment.belief owner site) (fun history => firstLateBadValue history.1.state) ≤
      (271 / 1000 : ℝ) := by
  classical
  let := Fintype.ofFinite rawProtocol.History
  obtain ⟨sequence, approximate, converges⟩ := consistent
  have bound (n : Nat) : expect ((sequence n).belief owner site)
      (fun history => firstLateBadValue history.1.state) ≤ (271 / 1000 : ℝ) := by
    have positive := rawModel.informationMass_pos_of_fullSupport (sequence n).strategy
      (approximate n).1 owner site
    have law : (sequence n).belief owner site = rawModel.bayesBelief (sequence n).strategy
        owner site (rawMenu.decisionInformationAntichain initial horizon scheduler owner site)
          positive := by
      exact PMF.ext ((approximate n).2 owner site positive)
    rw [law]
    exact firstLate_bayes_bad_le (sequence n).strategy owner site past view observed length
      original clock empty positive
  have tends : Tendsto (fun n => expect ((sequence n).belief owner site)
      (fun history => firstLateBadValue history.1.state)) atTop
      (nhds (expect (assessment.belief owner site)
        (fun history => firstLateBadValue history.1.state))) := by
    simp only [expect, tsum_fintype]
    exact tendsto_finsetSum _ fun history _ =>
      ((converges.belief owner site).toReal history).mul_const _
  exact le_of_tendsto tends (Eventually.of_forall bound)

end Vegas.Examples.CommitSeedBroadcast
