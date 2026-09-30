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

omit [Fintype ι] in
/-- A complete policy deviation's continuation law is a mixture of the laws
of policies with the same future behavior and one fixed current response,
whenever the runner factors a law installed at the site. -/
theorem BehavioralAssessment.continuationContextWith_outcome_eq_bind_commit
    (assessment : M.BehavioralAssessment) (run : M.ContinuationRunner)
    (site : M.InformationSite who) (hfactor : M.RunnerFactorsAt run who site)
    (payoff : E.History → ℝ) (alternative : M.BehavioralPolicy who) :
    (assessment.continuationContextWith run site payoff).outcome alternative =
      (alternative site.1).bind fun choice =>
        (assessment.continuationContextWith run site payoff).outcome
          (alternative.commit site.1 choice) := by
  have split := assessment.continuationContextWith_outcome_withLaw run site hfactor payoff
    alternative (alternative site.1)
  rwa [BehavioralPolicy.withLaw_eq_self] at split

omit [Fintype ι] in
/-- Where the runner factors a law installed at the site, the continuation value
of that law is the average value of the fixed current responses. -/
theorem BehavioralAssessment.continuationContextWith_value_withLaw
    (assessment : M.BehavioralAssessment) (run : M.ContinuationRunner)
    (site : M.InformationSite who) (hfactor : M.RunnerFactorsAt run who site)
    (payoff : E.History → ℝ) (law : PMF (M.Choice who site.1))
    (integrable : (assessment.continuationContextWith run site payoff).IntegrableAt
      ((assessment.strategy who).withLaw site.1 law)) :
    (assessment.continuationContextWith run site payoff).value
        ((assessment.strategy who).withLaw site.1 law) =
      expect law (fun choice =>
        (assessment.continuationContextWith run site payoff).value
          ((assessment.strategy who).commit site.1 choice)) := by
  unfold Context.IntegrableAt at integrable
  unfold Context.value
  rw [assessment.continuationContextWith_outcome_withLaw run site hfactor payoff] at integrable ⊢
  exact expect_bind_tower _ _ _ integrable

omit [Fintype ι] in
/-- A complete policy deviation with a finite expected payoff has the average
value of policies with the same future behavior and one fixed current
response, whenever the runner factors a law installed at the site. This
identity requires no optimality assumption on the original assessment or on
the alternative policy. -/
theorem BehavioralAssessment.continuationContextWith_value_eq_expect_commit
    (assessment : M.BehavioralAssessment) (run : M.ContinuationRunner)
    (site : M.InformationSite who) (hfactor : M.RunnerFactorsAt run who site)
    (payoff : E.History → ℝ) (alternative : M.BehavioralPolicy who)
    (integrable : (assessment.continuationContextWith run site payoff).IntegrableAt
      alternative) :
    (assessment.continuationContextWith run site payoff).value alternative =
      expect (alternative site.1) (fun choice =>
        (assessment.continuationContextWith run site payoff).value
          (alternative.commit site.1 choice)) := by
  unfold Context.IntegrableAt at integrable
  unfold Context.value
  rw [assessment.continuationContextWith_outcome_eq_bind_commit run site hfactor payoff
    alternative] at integrable ⊢
  exact expect_bind_tower _ _ _ integrable

end GameTheory.Protocol.InformationModel
