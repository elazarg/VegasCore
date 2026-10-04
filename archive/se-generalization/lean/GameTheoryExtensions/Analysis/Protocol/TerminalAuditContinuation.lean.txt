/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.TerminalAudit

/-! # Continuation incentives under a terminal audit

A one-time escrow deters a deviation through the increase in expected
collection, rather than through the deviation's absolute collection probability.
When expected collection is the same under every continuation policy, the audit
subtracts a common constant and leaves the base game's rationality comparisons
unchanged. This includes certain collection after a persistent public miss and
uncertain collection whose probability cannot be increased by further offenses.

These are conditional comparisons for the actual fixed audit. They neither
supply a continuation equilibrium nor assume that positive coverage for each
offense gives a positive increase in collection.
-/

noncomputable section

namespace GameTheory.Enforcement.TerminalAudit

open Math.Probability

variable {Player Outcome Observation : Type}

/-- Bounded collection preserves integrability of the base payoff. -/
theorem payoffIntegrable_utility (law : PMF Outcome) (base : Outcome → Player → ℝ)
    (observe : Outcome → Observation) (audit : Observation → PMF (Player → Bool))
    (deposit : Player → ℝ) (who : Player)
    (integrable : PayoffIntegrable law (fun outcome => base outcome who)) :
    PayoffIntegrable law (fun outcome => utility base observe audit deposit outcome who) := by
  exact payoffIntegrable_sub integrable
    (by simpa only [mul_comm] using
      payoffIntegrable_const_mul (c := deposit who) (payoffIntegrable_charge law observe audit who))

/-- The expected fine uses actual collection, including observation and
report-delivery failure encoded by the audit. -/
theorem expect_utility (law : PMF Outcome) (base : Outcome → Player → ℝ)
    (observe : Outcome → Observation) (audit : Observation → PMF (Player → Bool))
    (deposit : Player → ℝ) (who : Player)
    (integrable : PayoffIntegrable law (fun outcome => base outcome who)) :
    expect law (fun outcome => utility base observe audit deposit outcome who) =
      expect law (fun outcome => base outcome who) -
        expect law (fun outcome => charge observe audit outcome who) * deposit who := by
  unfold utility
  have fine : PayoffIntegrable law
      (fun outcome => charge observe audit outcome who * deposit who) := by
    have scaled := payoffIntegrable_const_mul (c := deposit who)
      (payoffIntegrable_charge law observe audit who)
    simpa only [mul_comm] using scaled
  rw [expect_sub integrable fine, expect_mul_const]

/-- A deviation is deterred exactly when its increase in expected fine covers
its gain in base payoff. No independence or nonnegative increase is assumed. -/
theorem comparison_iff (comparison : IncentiveComparison Outcome)
    (base : Outcome → Player → ℝ) (observe : Outcome → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ) (who : Player)
    (prescribedIntegrable : PayoffIntegrable comparison.prescribed
      (fun outcome => base outcome who))
    (alternativeIntegrable : PayoffIntegrable comparison.alternative
      (fun outcome => base outcome who)) :
    comparison.Holds (fun outcome => utility base observe audit deposit outcome who) ↔
      expect comparison.alternative (fun outcome => base outcome who) -
          expect comparison.prescribed (fun outcome => base outcome who) ≤
        (expect comparison.alternative (fun outcome => charge observe audit outcome who) -
          expect comparison.prescribed (fun outcome => charge observe audit outcome who)) *
            deposit who := by
  rw [comparison.holds_iff_of_integrable _
    (payoffIntegrable_utility _ _ _ _ _ _ prescribedIntegrable)
    (payoffIntegrable_utility _ _ _ _ _ _ alternativeIntegrable),
    expect_utility _ _ _ _ _ _ alternativeIntegrable,
    expect_utility _ _ _ _ _ _ prescribedIntegrable]
  constructor <;> intro bound <;> nlinarith

/-- Equal collection leaves the comparison unchanged, even when collection
is uncertain and the player does not know the watcher's observation. -/
theorem comparison_iff_of_equal_collection (comparison : IncentiveComparison Outcome)
    (base : Outcome → Player → ℝ) (observe : Outcome → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ) (who : Player)
    (prescribedIntegrable : PayoffIntegrable comparison.prescribed
      (fun outcome => base outcome who))
    (alternativeIntegrable : PayoffIntegrable comparison.alternative
      (fun outcome => base outcome who))
    (equal : expect comparison.alternative (fun outcome => charge observe audit outcome who) =
      expect comparison.prescribed (fun outcome => charge observe audit outcome who)) :
    comparison.Holds (fun outcome => utility base observe audit deposit outcome who) ↔
      comparison.Holds (fun outcome => base outcome who) := by
  rw [comparison_iff comparison base observe audit deposit who prescribedIntegrable
    alternativeIntegrable, equal, sub_self, zero_mul,
    comparison.holds_iff_of_integrable _ prescribedIntegrable alternativeIntegrable,
    sub_nonpos]

end GameTheory.Enforcement.TerminalAudit

namespace GameTheory.Protocol.InformationModel.BehavioralAssessment

open GameTheory.Math.Probability GameTheory.Enforcement.TerminalAudit

variable {Player Observation : Type} [DecidableEq Player]
  {E : ExecutionProtocol Player} {M : InformationModel E}

/-- A constant expected collection under every whole-policy continuation
leaves sequential rationality at this information site exactly unchanged.
The constant is conditional on the player's actual belief, not on omniscient
knowledge of a previously observed offense. -/
theorem isSequentiallyRationalAt_iff_of_constant_collection
    (assessment : M.BehavioralAssessment) (run : M.ContinuationRunner)
    {who : Player} (site : M.InformationSite who)
    (base : E.History → Player → ℝ) (observe : E.History → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ) (rate : ℝ)
    (integrable : ∀ alternative : M.BehavioralPolicy who,
      PayoffIntegrable
        ((assessment.continuationContextWith run site (fun final => base final who)).outcome
          alternative) (fun final => base final who))
    (constant : ∀ alternative : M.BehavioralPolicy who,
      expect
        ((assessment.continuationContextWith run site (fun final => base final who)).outcome
          alternative) (fun final => charge observe audit final who) = rate) :
    assessment.IsSequentiallyRationalAt site
        (assessment.continuationContextWith run site
          (fun final => utility base observe audit deposit final who)) ↔
      assessment.IsSequentiallyRationalAt site
        (assessment.continuationContextWith run site (fun final => base final who)) := by
  have auditedIntegrable (alternative : M.BehavioralPolicy who) :
      (assessment.continuationContextWith run site
        (fun final => utility base observe audit deposit final who)).IntegrableAt alternative :=
    payoffIntegrable_utility _ base observe audit deposit who (integrable alternative)
  unfold IsSequentiallyRationalAt
  rw [Context.isLocallyOptimal_iff_of_integrable (auditedIntegrable _)
    (fun alternative _ => auditedIntegrable alternative),
    Context.isLocallyOptimal_iff_of_integrable (integrable _)
      (fun alternative _ => integrable alternative)]
  have shifted (alternative : M.BehavioralPolicy who) :
      (assessment.continuationContextWith run site
        (fun final => utility base observe audit deposit final who)).value alternative =
      (assessment.continuationContextWith run site (fun final => base final who)).value
        alternative - rate * deposit who := by
    let law := (assessment.continuationContextWith run site
      (fun final => base final who)).outcome alternative
    change expect law (fun final => utility base observe audit deposit final who) =
      expect law (fun final => base final who) - rate * deposit who
    rw [expect_utility _ base observe audit deposit who (integrable alternative),
      constant alternative]
  simp only [shifted, sub_le_sub_iff_right]

end GameTheory.Protocol.InformationModel.BehavioralAssessment
