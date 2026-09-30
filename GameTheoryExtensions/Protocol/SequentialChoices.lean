/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.CounterfactualRegret
import GameTheory.Protocol.BehavioralAssessment
import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Analysis.Protocol.SupportedChoices

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

/-- Replacing the current response law makes the continuation law a mixture,
over that response, of the laws with one fixed current response. -/
theorem BehavioralAssessment.truncatedContinuationContext_outcome_withLaw
    (assessment : M.BehavioralAssessment) (once : M.ActsOnceWhereItMatters)
    (site : M.InformationSite who) (nonterminal : site.AllNonterminal)
    (payoff : E.History → ℝ) (fuel : Nat) (law : PMF (M.Choice who site.1)) :
    (assessment.truncatedContinuationContext site payoff (fuel + 1)).outcome
        ((assessment.strategy who).withLaw site.1 law) =
      law.bind fun choice => (assessment.truncatedContinuationContext site payoff (fuel +
          1)).outcome
        ((assessment.strategy who).commit site.1 choice) := by
  change (assessment.belief who site).bind _ =
    law.bind fun choice => (assessment.belief who site).bind _
  rw [← PMF.bind_comm]
  apply bind_congr_on_support
  intro history _
  exact M.runBehavioralFrom_update_withLaw_eq_bind once assessment.strategy who
    (assessment.strategy who) site.1 law history.1 history.2 (nonterminal history)
      (InformationSite.active M site history) fuel

/-- A complete policy deviation's continuation law is a mixture of the laws
of policies with the same future behavior and one fixed current response. -/
theorem BehavioralAssessment.truncatedContinuationContext_outcome_eq_bind_commit
    (assessment : M.BehavioralAssessment) (once : M.ActsOnceWhereItMatters)
    (site : M.InformationSite who) (nonterminal : site.AllNonterminal)
    (payoff : E.History → ℝ) (fuel : Nat) (alternative : M.BehavioralPolicy who) :
    (assessment.truncatedContinuationContext site payoff (fuel + 1)).outcome alternative =
      (alternative site.1).bind fun choice =>
        (assessment.truncatedContinuationContext site payoff (fuel + 1)).outcome
          (alternative.commit site.1 choice) := by
  change (assessment.belief who site).bind _ =
    (alternative site.1).bind fun choice => (assessment.belief who site).bind _
  rw [← PMF.bind_comm]
  apply bind_congr_on_support
  intro history _
  have split := M.runBehavioralFrom_update_withLaw_eq_bind once assessment.strategy who
    alternative site.1 (alternative site.1) history.1 history.2 (nonterminal history)
      (InformationSite.active M site history) fuel
  rwa [BehavioralPolicy.withLaw_eq_self] at split

theorem BehavioralAssessment.truncatedContinuationContext_value_withLaw
    (assessment : M.BehavioralAssessment) (once : M.ActsOnceWhereItMatters)
    (site : M.InformationSite who) (nonterminal : site.AllNonterminal)
    (payoff : E.History → ℝ) (fuel : Nat) (law : PMF (M.Choice who site.1))
    (integrable : (assessment.truncatedContinuationContext site payoff (fuel + 1)).IntegrableAt
      ((assessment.strategy who).withLaw site.1 law)) :
    (assessment.truncatedContinuationContext site payoff (fuel + 1)).value
        ((assessment.strategy who).withLaw site.1 law) =
      expect law (fun choice =>
        (assessment.truncatedContinuationContext site payoff (fuel + 1)).value
          ((assessment.strategy who).commit site.1 choice)) := by
  unfold Context.IntegrableAt at integrable
  unfold Context.value
  rw [assessment.truncatedContinuationContext_outcome_withLaw once site nonterminal payoff fuel law]
    at integrable ⊢
  exact expect_bind_tower _ _ _ integrable

/-- A complete policy deviation with a finite expected payoff has the average
value of policies with the same future behavior and one fixed current
response. This identity requires no optimality assumption on the original
assessment or on the alternative policy. -/
theorem BehavioralAssessment.truncatedContinuationContext_value_eq_expect_commit
    (assessment : M.BehavioralAssessment) (once : M.ActsOnceWhereItMatters)
    (site : M.InformationSite who) (nonterminal : site.AllNonterminal)
    (payoff : E.History → ℝ) (fuel : Nat) (alternative : M.BehavioralPolicy who)
    (integrable : (assessment.truncatedContinuationContext site payoff (fuel + 1)).IntegrableAt
      alternative) :
    (assessment.truncatedContinuationContext site payoff (fuel + 1)).value alternative =
      expect (alternative site.1) (fun choice =>
        (assessment.truncatedContinuationContext site payoff (fuel + 1)).value
          (alternative.commit site.1 choice)) := by
  unfold Context.IntegrableAt at integrable
  unfold Context.value
  rw [assessment.truncatedContinuationContext_outcome_eq_bind_commit once site nonterminal payoff
      fuel
    alternative] at integrable ⊢
  exact expect_bind_tower _ _ _ integrable

end GameTheory.Protocol.InformationModel
