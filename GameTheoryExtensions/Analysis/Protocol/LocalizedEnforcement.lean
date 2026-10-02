/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.PassageRestrictionExtension
import GameTheoryExtensions.Math.Probability.Expectation

/-! # Enforcement by clean continuation comparators

Retained histories may carry charges. Source payoffs match the target's actual
net utility. Enforced excluded actions are compared with a legal source
continuation that avoids collection against the acting player. Other excluded
actions use a direct continuation comparison, such as a private binding repair.
Each comparator is shared across the hidden histories in the information set.

Collection and clean-comparator bounds are local to enforced excluded actions.
When a local menu already contains every target choice, those obligations are
vacuous. No common decision depth or global source-clean assumption is used.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel.ActionRestriction

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E T : ExecutionProtocol Player} {M : InformationModel E} {N : InformationModel T}
  [Finite T.History] [∀ who, DecidableEq (N.InfoState who)]
  (restriction : M.ActionRestriction N)

/-- Every source SE extends when each excluded action's expected net payoff
is bounded by a legal source continuation. For enforced actions the bound is
derived from collection and a clean comparator; the remaining actions have a
direct comparison premise. Existing retained charges are part of the matched
source payoff. Bounds and comparators are uniform over extending profiles and
arbitrary beliefs at retained sites. -/
theorem sequential_equilibrium_extends_of_local_collection
    (sourceAntichain : M.DecisionInformationAntichain)
    (sourceCertificate : E.WellFoundedHistories) (targetCertificate : T.WellFoundedHistories)
    (reference : N.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (decisionRecall : N.DecisionRecall)
    (sourcePayoff : Player → E.History → ℝ) (base charge : Player → T.History → ℝ)
    (deposit : Player → ℝ)
    (matching : ∀ who history,
      base who (restriction.history history) - charge who (restriction.history history) *
        deposit who = sourcePayoff who history)
    (enforced : ∀ who (site : M.InformationSite who),
      N.Choice who (restriction.site who site).1 → Prop)
    (lower upper probability : ∀ who, M.InformationSite who → ℝ)
    (nonnegative : ∀ who, 0 ≤ deposit who)
    (sufficient : ∀ who site action, enforced who site action →
      action ∉ Set.range (restriction.choice who site.1) →
      upper who site - probability who site * deposit who ≤ lower who site)
    (targetUpper : ∀ (profile : ∀ who, N.BehavioralPolicy who) who
      (site : M.InformationSite who)
      (action : N.Choice who (restriction.site who site).1),
      action ∉ Set.range (restriction.choice who site.1) →
      enforced who site action →
      ∀ history : M.InformationHistory who site.1,
      ∀ final ∈ (N.runBehavioralTerminalFrom targetCertificate
        (Profile.update (sig := N.behavioralSignature) profile who
          ((profile who).commit (restriction.site who site).1 action))
        (restriction.history history.1)).support,
        base who final ≤ upper who site)
    (collection : ∀ (profile : ∀ who, N.BehavioralPolicy who) who
      (site : M.InformationSite who)
      (action : N.Choice who (restriction.site who site).1),
      action ∉ Set.range (restriction.choice who site.1) →
      enforced who site action →
      ∀ history : M.InformationHistory who site.1,
        probability who site ≤ expect (N.runBehavioralTerminalFrom targetCertificate
          (Profile.update (sig := N.behavioralSignature) profile who
            ((profile who).commit (restriction.site who site).1 action))
          (restriction.history history.1)) (charge who))
    (comparator : ∀ (sourceProfile : ∀ who, M.BehavioralPolicy who)
      (targetProfile : ∀ who, N.BehavioralPolicy who),
      restriction.ExtendsProfile sourceProfile targetProfile →
      ∀ who (site : M.InformationSite who)
        (action : N.Choice who (restriction.site who site).1),
        action ∉ Set.range (restriction.choice who site.1) →
        enforced who site action →
        ∀ belief : PMF (M.InformationHistory who site.1),
          ∃ alternative : M.BehavioralPolicy who,
            ∀ history ∈ belief.support,
            ∀ final ∈ (M.runBehavioralTerminalFrom sourceCertificate
              (Profile.update (sig := M.behavioralSignature) sourceProfile who alternative)
              history.1).support,
              lower who site ≤ base who (restriction.history final) ∧
                charge who (restriction.history final) = 0)
    (otherComparison : ∀ (sourceProfile : ∀ who, M.BehavioralPolicy who)
      (targetProfile : ∀ who, N.BehavioralPolicy who),
      restriction.ExtendsProfile sourceProfile targetProfile →
      ∀ who (site : M.InformationSite who)
        (action : N.Choice who (restriction.site who site).1),
        action ∉ Set.range (restriction.choice who site.1) →
        ¬ enforced who site action →
        ∀ belief : PMF (M.InformationHistory who site.1),
          ∃ alternative : M.BehavioralPolicy who,
            expect belief (fun history => expect (N.runBehavioralTerminalFrom targetCertificate
              (Profile.update (sig := N.behavioralSignature) targetProfile who
                ((targetProfile who).commit (restriction.site who site).1 action))
              (restriction.history history.1))
              (fun final => base who final - charge who final * deposit who)) ≤
            expect belief (fun history => expect (M.runBehavioralTerminalFrom sourceCertificate
              (Profile.update (sig := M.behavioralSignature) sourceProfile who alternative)
              history.1) (sourcePayoff who)))
    (source : M.BehavioralAssessment)
    (sourceEquilibrium : source.IsSequentialEquilibrium sourceAntichain sourceCertificate
      sourcePayoff) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibrium decisionRecall.decisionInformationAntichain
        targetCertificate (fun who history =>
          base who history - charge who history * deposit who) ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      (M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          restriction.history =
        N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory ∧
      (M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          (fun history => (restriction.history history, fun who => sourcePayoff who history)) =
        (N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory).map
          (fun history =>
            (history, fun who => base who history - charge who history * deposit who)) := by
  classical
  let _ := Fintype.ofFinite T.History
  have _ : Finite E.History :=
    Finite.of_injective restriction.history restriction.history.injective
  apply restriction.sequentialEquilibrium_extends_of_continuation_unclocked sourceAntichain
    sourceCertificate targetCertificate reference referenceMixed decisionRecall sourcePayoff
    (fun who history => base who history - charge who history * deposit who) matching _ source
    sourceEquilibrium
  intro sourceProfile targetProfile agrees who site action extra belief
  by_cases gated : enforced who site action
  · obtain ⟨alternative, cleanLower⟩ :=
      comparator sourceProfile targetProfile agrees who site action extra gated belief
    refine ⟨alternative, expect_mono (fun history supported => ?_)
      (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)⟩
    have upperBound := expect_le_const
      (N.runBehavioralTerminalFrom targetCertificate
        (Profile.update (sig := N.behavioralSignature) targetProfile who
          ((targetProfile who).commit (restriction.site who site).1 action))
        (restriction.history history.1)) (base who) (payoffIntegrable_of_finite _ _)
      (upper who site) (targetUpper targetProfile who site action extra gated history)
    have lowerBound : lower who site ≤ expect
        (M.runBehavioralTerminalFrom sourceCertificate
          (Profile.update (sig := M.behavioralSignature) sourceProfile who alternative)
          history.1) (sourcePayoff who) := by
      rw [← expect_constant _ (lower who site)]
      apply expect_mono _ (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _)
      intro final member
      obtain ⟨bounded, clear⟩ := cleanLower history supported final member
      rw [← matching, clear, zero_mul, sub_zero]
      exact bounded
    rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
      expect_mul_const]
    have netBound := sub_le_sub upperBound
      (mul_le_mul_of_nonneg_right (collection targetProfile who site action extra gated history)
        (nonnegative who))
    exact (netBound.trans (sufficient who site action gated extra)).trans lowerBound
  · exact otherComparison sourceProfile targetProfile agrees who site action extra gated belief

end GameTheory.Protocol.InformationModel.ActionRestriction
