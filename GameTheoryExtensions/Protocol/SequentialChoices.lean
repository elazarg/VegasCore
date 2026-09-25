/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.CounterfactualRegret
import GameTheory.Protocol.BehavioralAssessment

/-! # Supported responses under sequential rationality

The existing no-revisit condition makes a continuation value affine in the
current response distribution. Sequential rationality therefore makes every
supported current response optimal, with the subsequent strategy unchanged.
A uniform payoff gap excludes a response without requiring positive belief
on each history in the information set. Concrete applications must establish
that gap across the entire information set, including its zero-belief nodes.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ExecutionProtocol ι} {M : InformationModel E}
  {who : ι} [DecidableEq (M.InfoState who)]

omit [Fintype ι] [DecidableEq ι] in
private theorem actedAt_prefix (who : ι) {state : E.State}
    (trace : E.Trace state) (info : M.InfoState who) (member : info ∈ M.actedAt who trace) :
    ∃ (prior : E.History) (joint : ∀ player, Option (E.Action player))
      (legal : E.Legal prior.state joint) (next : E.State)
      (reached : next ∈ (E.step prior.state ⟨joint, legal⟩).support) (fuel : Nat),
      M.infoOf who prior.trace = info ∧
        E.ReachesWithin fuel (prior.extend legal reached) ⟨state, trace⟩ := by
  induction trace with
  | start => simp [InfoSignals.actedAt] at member
  | @extend source target trace joint legal reached ih =>
      have earlier (member : info ∈ M.actedAt who trace) :
          ∃ (prior : E.History) (earlierJoint : ∀ player, Option (E.Action player))
            (earlierLegal : E.Legal prior.state earlierJoint) (next : E.State)
            (moved : next ∈ (E.step prior.state ⟨earlierJoint, earlierLegal⟩).support) (fuel : Nat),
            M.infoOf who prior.trace = info ∧ E.ReachesWithin fuel
              (prior.extend earlierLegal moved) ⟨target, trace.extend joint legal reached⟩ := by
        obtain ⟨prior, earlierJoint, earlierLegal, next, moved, fuel, same, path⟩ := ih member
        exact ⟨prior, earlierJoint, earlierLegal, next, moved, fuel + 1, same,
          path.trans (.step joint legal reached (.refl 0 _))⟩
      cases selected : joint who with
      | none => exact earlier (by simpa only [InfoSignals.actedAt, selected] using member)
      | some action =>
          simp only [InfoSignals.actedAt, selected, List.mem_cons] at member
          rcases member with same | member
          · exact ⟨⟨source, trace⟩, joint, legal, target, reached, 0, same.symm, .refl 0 _⟩
          · exact earlier member

omit [Fintype ι] [DecidableEq ι] in
/-- The assessment antichain condition also provides the no-revisit premise
for affineness of continuation value in a current behavioral choice. -/
theorem actsOnce_of_decisionInformationAntichain
    (antichain : M.DecisionInformationAntichain) : M.ActsOnceAtEachInfoState := by
  intro player state trace
  induction trace with
  | start => simp [InfoSignals.actedAt]
  | @extend source target trace joint legal reached ih =>
      cases selected : joint player with
      | none => simpa only [InfoSignals.actedAt, selected] using ih
      | some action =>
          simp only [InfoSignals.actedAt, selected, List.nodup_cons]
          refine ⟨?_, ih⟩
          intro member
          have menu : some action ∈ M.menu player (M.infoOf player trace) := by
            apply (M.menu_adequate player trace (some action)).mpr
            simpa only [selected] using E.legalOption_of_legal legal player
          let site := M.informationSite player ⟨source, trace⟩ action legal.1 menu
          obtain ⟨prior, oldJoint, oldLegal, next, moved, fuel, same, path⟩ :=
            actedAt_prefix player trace _ member
          exact antichain player site ⟨prior, same⟩ ⟨⟨source, trace⟩, rfl⟩
            oldJoint oldLegal next moved fuel path

theorem BehavioralAssessment.continuationContext_value_withLaw
    (assessment : M.BehavioralAssessment) (once : M.ActsOnceWhereItMatters)
    (site : M.InformationSite who) (nonterminal : site.AllNonterminal)
    (payoff : E.History → ℝ) (fuel : Nat) (law : FinDist (M.Choice who site.1)) :
    (assessment.continuationContext site payoff (fuel + 1)).value
        ((assessment.strategy who).withLaw site.1 law) =
      law.expect (fun choice =>
        (assessment.continuationContext site payoff (fuel + 1)).value
          ((assessment.strategy who).commit site.1 choice)) := by
  simp only [BehavioralAssessment.continuationContext_value, FinDist.expect_bind]
  calc
    _ = (assessment.belief who site).expect (fun history =>
          law.expect (fun choice =>
            (M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
              assessment.strategy who ((assessment.strategy who).commit site.1 choice))
                (fuel + 1) history.1).expect payoff)) := by
      apply FinDist.expect_congr
      intro history _
      rw [M.runBehavioralFrom_update_withLaw_eq_bind once assessment.strategy who
        (assessment.strategy who) site.1 law history.1 history.2 (nonterminal history)
          (InformationSite.active M site history) fuel, FinDist.expect_bind]
    _ = _ := FinDist.expect_comm _ _ _

/-- A complete policy deviation is a mixture of policies with the same future
behavior and one fixed current response. This identity requires no optimality
assumption on the original assessment or on the alternative policy. -/
theorem BehavioralAssessment.continuationContext_value_eq_expect_commit
    (assessment : M.BehavioralAssessment) (once : M.ActsOnceWhereItMatters)
    (site : M.InformationSite who) (nonterminal : site.AllNonterminal)
    (payoff : E.History → ℝ) (fuel : Nat) (alternative : M.BehavioralPolicy who) :
    (assessment.continuationContext site payoff (fuel + 1)).value alternative =
      (alternative site.1).expect (fun choice =>
        (assessment.continuationContext site payoff (fuel + 1)).value
          (alternative.commit site.1 choice)) := by
  simp only [BehavioralAssessment.continuationContext_value, FinDist.expect_bind]
  calc
    _ = (assessment.belief who site).expect (fun history =>
          (alternative site.1).expect (fun choice =>
            (M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
              assessment.strategy who (alternative.commit site.1 choice))
                (fuel + 1) history.1).expect payoff)) := by
      apply FinDist.expect_congr
      intro history _
      have split := M.runBehavioralFrom_update_withLaw_eq_bind once assessment.strategy who
        alternative site.1 (alternative site.1) history.1 history.2 (nonterminal history)
          (InformationSite.active M site history) fuel
      rw [BehavioralPolicy.withLaw_eq_self] at split
      rw [split, FinDist.expect_bind]
    _ = _ := FinDist.expect_comm _ _ _

/-- Each supported pure current response has the same continuation value as
the rational mixed response. Future choices remain the assessment's strategy. -/
theorem BehavioralAssessment.supported_choice_value
    (assessment : M.BehavioralAssessment) (once : M.ActsOnceWhereItMatters)
    (site : M.InformationSite who) (nonterminal : site.AllNonterminal)
    (payoff : E.History → ℝ) (fuel : Nat)
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext site payoff (fuel + 1)))
    (choice : M.Choice who site.1)
    (supported : choice ∈ (assessment.strategy who site.1).support) :
    (assessment.continuationContext site payoff (fuel + 1)).value
        ((assessment.strategy who).commit site.1 choice) =
      (assessment.continuationContext site payoff (fuel + 1)).value
        (assessment.strategy who) := by
  have affine := assessment.continuationContext_value_withLaw once site nonterminal
    payoff fuel (assessment.strategy who site.1)
  rw [BehavioralPolicy.withLaw_eq_self] at affine
  apply FinDist.eq_of_expect_eq_of_le (assessment.strategy who site.1) _ _
    (fun alternative _ => rational ((assessment.strategy who).commit site.1 alternative)
      (Set.mem_univ _)) affine.symm supported

/-- Supported responses maximize against whole continuation-policy deviations,
not merely other current responses. -/
theorem BehavioralAssessment.supported_choice_optimal
    (assessment : M.BehavioralAssessment) (once : M.ActsOnceWhereItMatters)
    (site : M.InformationSite who) (nonterminal : site.AllNonterminal)
    (payoff : E.History → ℝ) (fuel : Nat)
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext site payoff (fuel + 1)))
    (choice : M.Choice who site.1)
    (supported : choice ∈ (assessment.strategy who site.1).support)
    (alternative : M.BehavioralPolicy who) :
    (assessment.continuationContext site payoff (fuel + 1)).value alternative ≤
      (assessment.continuationContext site payoff (fuel + 1)).value
        ((assessment.strategy who).commit site.1 choice) := by
  rw [assessment.supported_choice_value once site nonterminal payoff fuel rational choice supported]
  exact rational alternative (Set.mem_univ _)

/-- Uniformly worse responses receive no probability. The bounds range over
all compatible histories, so this conclusion also controls an actual history
that the assessment happens to assign zero probability. -/
theorem BehavioralAssessment.not_supported_choice_of_uniform_gap
    (assessment : M.BehavioralAssessment) (once : M.ActsOnceWhereItMatters)
    (site : M.InformationSite who) (nonterminal : site.AllNonterminal)
    (payoff : E.History → ℝ) (fuel : Nat)
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext site payoff (fuel + 1)))
    (choice : M.Choice who site.1) (alternative : M.BehavioralPolicy who)
    (upper lower : ℝ) (gap : upper < lower)
    (bad : ∀ history : M.InformationHistory who site.1,
      (M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who ((assessment.strategy who).commit site.1 choice))
          (fuel + 1) history.1).expect payoff ≤ upper)
    (good : ∀ history : M.InformationHistory who site.1,
      lower ≤ (M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who alternative) (fuel + 1) history.1).expect payoff) :
    choice ∉ (assessment.strategy who site.1).support := by
  intro supported
  have best := assessment.supported_choice_optimal once site nonterminal payoff fuel rational
    choice supported alternative
  simp only [BehavioralAssessment.continuationContext_value, FinDist.expect_bind] at best
  have badBound := FinDist.expect_le_of_forall (assessment.belief who site) _ upper
    (fun history _ => bad history)
  have goodBound : lower ≤ (assessment.belief who site).expect (fun history =>
      (M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who alternative) (fuel + 1) history.1).expect payoff) := by
    calc
      lower = (assessment.belief who site).expect (fun _ => lower) :=
        (FinDist.expect_const _ _).symm
      _ ≤ _ := FinDist.expect_mono (fun history _ => good history)
  exact (not_le_of_gt gap) (goodBound.trans (best.trans badBound))

end GameTheory.Protocol.InformationModel
