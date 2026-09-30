/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.RestrictionExtension
import GameTheoryExtensions.Math.Probability.Expectation

/-! # Sequential equilibrium extends across an enforced action restriction

The target game, utilities and finite deposits are fixed before the source
assessment is chosen. A structural local execution embedding preserves the
compliant game. Sound charges and uniform conditional collection deter its
additional actions; new information sites are solved by one common consistent
completion. The result is the standard sequential-equilibrium predicate and
exact completed-run history and net-payoff laws. It does not assert reflection
of all target equilibria or a fixed playerwise map at new information sites.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel.ActionRestriction

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E T : ExecutionProtocol Player} {M : InformationModel E} {N : InformationModel T}
  [Finite T.History]
  [∀ who, DecidableEq (N.InfoState who)]
  (restriction : M.ActionRestriction N)

/-- Every source sequential equilibrium extends to the same fixed target
game under finite, sound, sufficiently costly first-departure collection.
The collection condition covers arbitrary target continuation profiles and
actual hidden histories; it contains no rational-completion premise.
Weak deterrence inequalities suffice for this forward existence conclusion.
Common decision depths are required only at the retained sites. -/
theorem sequential_equilibrium_extends
    (sourceAntichain : M.DecisionInformationAntichain)
    (sourceCertificate : E.WellFoundedHistories) (targetCertificate : T.WellFoundedHistories)
    (reference : N.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (decisionRecall : N.DecisionRecall)
    (depth : ∀ who, M.InformationSite who → Nat)
    (clock : ∀ who site, InformationSite.CommonDepth N (restriction.site who site)
      (depth who site))
    (sourcePayoff : Player → E.History → ℝ) (base charge : Player → T.History → ℝ)
    (matching : ∀ who history, base who (restriction.history history) = sourcePayoff who history)
    (clean : ∀ who history, charge who (restriction.history history) = 0)
    (lower upper detection deposit : Player → ℝ)
    (deposit_nonnegative : ∀ who, 0 ≤ deposit who)
    (source_lower : ∀ who history, lower who ≤ sourcePayoff who history)
    (target_upper : ∀ who history, base who history ≤ upper who)
    (sufficient : ∀ who, upper who - detection who * deposit who ≤ lower who)
    (collection : ∀ (profile : ∀ who, N.BehavioralPolicy who) who
      (site : M.InformationSite who)
      (action : N.Choice who (restriction.site who site).1),
      action ∉ Set.range (restriction.choice who site.1) →
      ∀ history : M.InformationHistory who site.1,
        detection who ≤ expect (N.runBehavioralTerminalFrom targetCertificate
          (Profile.update (sig := N.behavioralSignature) profile who
            ((profile who).commit (restriction.site who site).1 action))
          (restriction.history history.1)) (charge who))
    (source : M.BehavioralAssessment)
    (sourceEquilibrium : source.IsSequentialEquilibrium sourceAntichain sourceCertificate
      sourcePayoff) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibrium decisionRecall.decisionInformationAntichain
        targetCertificate (fun who history => base who history - charge who history * deposit who) ∧
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
  let utility := fun who history => base who history - charge who history * deposit who
  let comparator (who : Player) (site : M.InformationSite who)
      (_ : N.Choice who (restriction.site who site).1) : PMF (M.Choice who site.1) :=
    PMF.pure ⟨some site.2.choose_spec.2.choose, site.2.choose_spec.2.choose_spec⟩
  apply restriction.sequentialEquilibrium_extends_of_comparator sourceAntichain
    sourceCertificate targetCertificate reference referenceMixed decisionRecall depth clock
    sourcePayoff utility (fun who history => by simp only [utility, matching, clean, zero_mul,
      sub_zero]) comparator _ source sourceEquilibrium
  intro sourceProfile targetProfile _ who site action forbidden history
  have _ : Finite E.History :=
    Finite.of_injective restriction.history restriction.history.injective
  rw [show utility who = fun final => base who final - charge who final * deposit who from rfl,
    expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
    expect_mul_const]
  have upperBound : expect (N.runBehavioralTerminalFrom targetCertificate
      (Profile.update (sig := N.behavioralSignature) targetProfile who
        ((targetProfile who).commit (restriction.site who site).1 action))
      (restriction.history history.1)) (base who) ≤ upper who := by
    exact expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
      fun final _ => target_upper who final
  have netBound := sub_le_sub upperBound
    (mul_le_mul_of_nonneg_right (collection targetProfile who site action forbidden history)
      (deposit_nonnegative who))
  apply (netBound.trans (sufficient who)).trans
  exact (expect_constant _ (lower who)).symm.trans_le
    (expect_mono (fun final _ => source_lower who final) (payoffIntegrable_constant _ _)
      (payoffIntegrable_of_finite _ _))

end GameTheory.Protocol.InformationModel.ActionRestriction
