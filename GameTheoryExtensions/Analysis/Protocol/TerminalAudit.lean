/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.RestrictionExtension
import GameTheoryExtensions.Analysis.ObservableEnforcement
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Support

/-! # Sequential equilibrium under a terminal audit

A fixed audit observes a terminal transcript and samples a vector of collected
charges. The audit is a settlement service, with no intervening player decision
or strategic reporting player. Its verdicts may be correlated across players.

The enforcement theorem already derives incentive comparisons from payoff
bounds and conditional collection. This module instantiates that theorem with
an observation-based audit and preserves the actual randomized settlement law.
Audit completeness, attribution, and collection are backend obligations; they
are not consequences of the audit's implementation language.
-/

noncomputable section

namespace GameTheory.Enforcement.TerminalAudit

open Math.Probability

variable {Player Outcome Observation : Type}

/-- Probability that this player's charge is actually collected. An alarm
that cannot be collected must instead return `false` in this verdict. -/
def charge (observe : Outcome → Observation)
    (audit : Observation → PMF (Player → Bool)) (outcome : Outcome) (who : Player) : ℝ :=
  (((audit (observe outcome)).map (fun verdict => verdict who)) true).toReal

theorem charge_mem_Icc (observe : Outcome → Observation)
    (audit : Observation → PMF (Player → Bool)) (outcome : Outcome) (who : Player) :
    charge observe audit outcome who ∈ Set.Icc 0 1 :=
  ⟨ENNReal.toReal_nonneg, pmf_toReal_apply_le_one _ _⟩

/-- A collection probability is bounded, hence integrable under every law. -/
theorem payoffIntegrable_charge (law : PMF Outcome) (observe : Outcome → Observation)
    (audit : Observation → PMF (Player → Bool)) (who : Player) :
    PayoffIntegrable law (fun outcome => charge observe audit outcome who) :=
  payoffIntegrable_of_bounded _ _ (C := 1) fun outcome => by
    rw [abs_of_nonneg (charge_mem_Icc observe audit outcome who).1]
    exact (charge_mem_Icc observe audit outcome who).2

/-- The terminal service's joint realized payoff vector. -/
def settlement (base : Outcome → Player → ℝ) (observe : Outcome → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ)
    (outcome : Outcome) : PMF (Player → ℝ) :=
  (audit (observe outcome)).map (fun verdict who =>
    base outcome who - if verdict who then deposit who else 0)

/-- Expected terminal utility; all audit randomness occurs after strategic play. -/
def utility (base : Outcome → Player → ℝ) (observe : Outcome → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ)
    (outcome : Outcome) (who : Player) : ℝ :=
  base outcome who - charge observe audit outcome who * deposit who

theorem settlement_expect (base : Outcome → Player → ℝ) (observe : Outcome → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ)
    (outcome : Outcome) (who : Player) :
    expect (settlement base observe audit deposit outcome) (fun payoffs => payoffs who) =
      utility base observe audit deposit outcome who := by
  have reduced := expect_monitoredUtility (PMF.pure outcome) (fun result => base result who)
    observe (fun observed => (audit observed).map (fun verdict => verdict who)) (deposit who)
    (payoffIntegrable_pure _ _)
  simpa only [expect_pure, PMF.pure_map, PMF.pure_bind, monitoredUtility,
    PMF.map_comp, Function.comp_def, expect_map, id_eq, settlement, utility, charge]
    using reduced

/-- Expected collection is the actual audit's marginal collection probability.
No independence between the transcript, audit verdicts, or players is assumed. -/
theorem collection_probability (law : PMF Outcome) (observe : Outcome → Observation)
    (audit : Observation → PMF (Player → Bool)) (who : Player) :
    ((((law.map observe).bind audit).map (fun verdict => verdict who)) true).toReal =
      expect law (fun outcome => charge observe audit outcome who) := by
  rw [PMF.map_bind, toReal_bind_apply, expect_map]
  rfl

/-- Zero collection probability for every player means the joint settlement
law is exactly the original payoff vector, not merely equal in expectation. -/
theorem settlement_clean (base : Outcome → Player → ℝ) (observe : Outcome → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ)
    (outcome : Outcome) (clean : ∀ who, charge observe audit outcome who = 0) :
    settlement base observe audit deposit outcome = PMF.pure (base outcome) := by
  have quiet (verdict : Player → Bool) (supported : verdict ∈ (audit (observe outcome)).support)
      (who : Player) : verdict who = false := by
    cases selected : verdict who with
    | false => rfl
    | true =>
        have possible : true ∈
            ((audit (observe outcome)).map (fun result => result who)).support := by
          rw [PMF.support_map]
          exact ⟨verdict, supported, selected⟩
        have positive := pmf_toReal_pos_iff.mpr possible
        change 0 < charge observe audit outcome who at positive
        rw [clean who] at positive
        exact (lt_irrefl 0 positive).elim
  calc
    _ = (audit (observe outcome)).map (fun _ => base outcome) := by
      apply map_congr_on_support _
      intro verdict supported
      funext who
      simp only [quiet verdict supported who, Bool.false_eq_true, ite_false, sub_zero]
    _ = _ := by simp only [← PMF.bind_pure_comp, Function.comp_def, PMF.bind_const]

/-- **Clean settlement from a charge-free law.** Suppose a terminal law and a
reference law agree on the joint law of a readout and the vector of collection
probabilities, and the reference charges nobody. Then no outcome in the
terminal law's support is charged, and its joint law of readout and realized
settlement is the reference law of readout and base payoff, when the base payoff
is a function of the readout. -/
theorem clean_of_law_eq {Readout Source : Type*} (base : Outcome → Player → ℝ)
    (observe : Outcome → Observation) (audit : Observation → PMF (Player → Bool))
    (deposit : Player → ℝ) (readout : Outcome → Readout) (value : Readout → Player → ℝ)
    (baseEq : ∀ outcome, base outcome = value (readout outcome))
    (law : PMF Outcome) (source : PMF Source) (sourceReadout : Source → Readout)
    (equal : law.map (fun outcome =>
        (readout outcome, fun who => charge observe audit outcome who)) =
      source.map (fun state => (sourceReadout state, (0 : Player → ℝ)))) :
    (∀ outcome ∈ law.support, ∀ who, charge observe audit outcome who = 0) ∧
      law.bind (fun outcome => (settlement base observe audit deposit outcome).map
          (fun payoffs => (readout outcome, payoffs))) =
        source.map (fun state => (sourceReadout state, value (sourceReadout state))) := by
  have clean (outcome : Outcome) (supported : outcome ∈ law.support) (who : Player) :
      charge observe audit outcome who = 0 := by
    have member : (readout outcome, fun who => charge observe audit outcome who) ∈
        (law.map (fun outcome =>
          (readout outcome, fun who => charge observe audit outcome who))).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨outcome, supported, rfl⟩
    rw [equal, PMF.mem_support_map_iff] at member
    obtain ⟨_, _, same⟩ := member
    exact (congrFun (congrArg Prod.snd same) who).symm
  refine ⟨clean, ?_⟩
  calc
    _ = law.map (fun outcome => (readout outcome, value (readout outcome))) := by
      rw [← PMF.bind_pure_comp]
      apply bind_congr_on_support
      intro outcome supported
      rw [settlement_clean base observe audit deposit outcome (clean outcome supported),
        PMF.pure_map, baseEq]
      rfl
    _ = (law.map (fun outcome =>
          (readout outcome, fun who => charge observe audit outcome who))).map
          (fun pair => (pair.1, value pair.1)) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by
      rw [equal, PMF.map_comp]
      rfl

end GameTheory.Enforcement.TerminalAudit

namespace GameTheory.Protocol.InformationModel.ActionRestriction

open GameTheory.Math.Probability ExecutionProtocol Enforcement.TerminalAudit

variable {Player Observation : Type} [Fintype Player] [DecidableEq Player]
  {E T : ExecutionProtocol Player} {M : InformationModel E} {N : InformationModel T}
  [Finite T.History]
  [∀ who, DecidableEq (N.InfoState who)]
  (restriction : M.ActionRestriction N)

/-- A sound terminal audit with a uniform conditional collection guarantee
extends every restricted sequential equilibrium to the same audited target.

Collection is required for every extra action at every retained hidden history,
against arbitrary later strategies. No compliance after a collected or sunk
penalty is assumed: the existing completion theorem solves those new sites.
The conclusion is forward preservation, not reflection of all target equilibria.
-/
theorem sequential_equilibrium_extends_of_terminal_audit
    (sourceAntichain : M.DecisionInformationAntichain)
    (sourceCertificate : E.WellFoundedHistories) (targetCertificate : T.WellFoundedHistories)
    (reference : N.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (decisionRecall : N.DecisionRecall)
    (depth : ∀ who, M.InformationSite who → Nat)
    (clock : ∀ who site, InformationSite.CommonDepth N (restriction.site who site)
      (depth who site))
    (sourcePayoff : E.History → Player → ℝ) (base : T.History → Player → ℝ)
    (observe : T.History → Observation) (audit : Observation → PMF (Player → Bool))
    (matching : ∀ history who, base (restriction.history history) who = sourcePayoff history who)
    (sound : ∀ history who, charge observe audit (restriction.history history) who = 0)
    (lower upper detection deposit : Player → ℝ)
    (deposit_nonnegative : ∀ who, 0 ≤ deposit who)
    (source_lower : ∀ history who, lower who ≤ sourcePayoff history who)
    (target_upper : ∀ history who, base history who ≤ upper who)
    (sufficient : ∀ who, upper who - detection who * deposit who ≤ lower who)
    (collection : ∀ (profile : ∀ who, N.BehavioralPolicy who) who
      (site : M.InformationSite who)
      (action : N.Choice who (restriction.site who site).1),
      action ∉ Set.range (restriction.choice who site.1) →
      ∀ history : M.InformationHistory who site.1,
        detection who ≤ (((((N.runBehavioralTerminalFrom targetCertificate
          (Profile.update (sig := N.behavioralSignature) profile who
            ((profile who).commit (restriction.site who site).1 action))
          (restriction.history history.1)).map observe).bind audit).map
            (fun verdict => verdict who)) true).toReal)
    (source : M.BehavioralAssessment)
    (sourceEquilibrium : source.IsSequentialEquilibrium sourceAntichain sourceCertificate
      (fun who history => sourcePayoff history who)) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibrium decisionRecall.decisionInformationAntichain
        targetCertificate (fun who history => utility base observe audit deposit history who) ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      (M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          restriction.history =
        N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory ∧
      (M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).map
          (fun history => (restriction.history history, sourcePayoff history)) =
        (N.runBehavioralTerminalFrom targetCertificate target.strategy T.initHistory).bind
          (fun history =>
            (settlement base observe audit deposit history).map (fun payoffs => (history,
                payoffs))) ∧
      ∀ history ∈ (N.runBehavioralTerminalFrom targetCertificate target.strategy
          T.initHistory).support, ∀ who, charge observe audit history who = 0 := by
  have collects : ∀ (profile : ∀ who, N.BehavioralPolicy who) who
      (site : M.InformationSite who)
      (action : N.Choice who (restriction.site who site).1),
      action ∉ Set.range (restriction.choice who site.1) →
      ∀ history : M.InformationHistory who site.1,
        detection who ≤ expect (N.runBehavioralTerminalFrom targetCertificate
          (Profile.update (sig := N.behavioralSignature) profile who
            ((profile who).commit (restriction.site who site).1 action))
          (restriction.history history.1))
            (fun final => charge observe audit final who) := by
    intro profile who site action extra history
    rw [← collection_probability]
    exact collection profile who site action extra history
  obtain ⟨target, equilibrium, agrees, beliefs, laws, _payoffs⟩ :=
    restriction.sequential_equilibrium_extends sourceAntichain sourceCertificate
      targetCertificate reference referenceMixed decisionRecall depth clock
      (fun who history => sourcePayoff history who) (fun who history => base history who)
      (fun who history => charge observe audit history who)
      (fun who history => matching history who) (fun who history => sound history who)
      lower upper detection deposit deposit_nonnegative (fun who history => source_lower history
          who)
      (fun who history => target_upper history who) sufficient collects source sourceEquilibrium
  refine ⟨target, equilibrium, agrees, beliefs, laws, ?_, ?_⟩
  · rw [← laws, PMF.bind_map]
    calc
      _ = (M.runBehavioralTerminalFrom sourceCertificate source.strategy E.initHistory).bind
          (fun history => PMF.pure (restriction.history history, sourcePayoff history)) :=
        (PMF.bind_pure_comp _ _).symm
      _ = _ := by
        apply bind_congr_on_support _
        intro history _
        rw [Function.comp_apply, settlement_clean base observe audit deposit _ (sound history),
          PMF.pure_map]
        congr 1
        exact congrArg (fun payoffs => (restriction.history history, payoffs))
          (funext (matching history)).symm
  · intro history supported who
    rw [← laws, PMF.support_map] at supported
    obtain ⟨original, _, rfl⟩ := supported
    exact sound original who

end GameTheory.Protocol.InformationModel.ActionRestriction
