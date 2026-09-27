/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.RestrictionExtension
import GameTheoryExtensions.Analysis.ObservableEnforcement

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
    (audit : Observation → FinDist (Player → Bool)) (outcome : Outcome) (who : Player) : ℝ :=
  ((audit (observe outcome)).map (fun verdict => verdict who)).prob true

/-- The terminal service's joint realized payoff vector. -/
def settlement (base : Outcome → Player → ℝ) (observe : Outcome → Observation)
    (audit : Observation → FinDist (Player → Bool)) (deposit : Player → ℝ)
    (outcome : Outcome) : FinDist (Player → ℝ) :=
  (audit (observe outcome)).map (fun verdict who =>
    base outcome who - if verdict who then deposit who else 0)

/-- Expected terminal utility; all audit randomness occurs after strategic play. -/
def utility (base : Outcome → Player → ℝ) (observe : Outcome → Observation)
    (audit : Observation → FinDist (Player → Bool)) (deposit : Player → ℝ)
    (outcome : Outcome) (who : Player) : ℝ :=
  base outcome who - charge observe audit outcome who * deposit who

theorem settlement_expect (base : Outcome → Player → ℝ) (observe : Outcome → Observation)
    (audit : Observation → FinDist (Player → Bool)) (deposit : Player → ℝ)
    (outcome : Outcome) (who : Player) :
    (settlement base observe audit deposit outcome).expect (fun payoffs => payoffs who) =
      utility base observe audit deposit outcome who := by
  have reduced := expect_monitoredUtility (FinDist.pure outcome) (fun result => base result who)
    observe (fun observed => (audit observed).map (fun verdict => verdict who)) (deposit who)
  simpa only [FinDist.expect_pure, FinDist.map_pure, FinDist.pure_bind, monitoredUtility,
    FinDist.map_comp, Function.comp_def, FinDist.expect_map, id_eq, settlement, utility, charge]
    using reduced

/-- Expected collection is the actual audit's marginal collection probability.
No independence between the transcript, audit verdicts, or players is assumed. -/
theorem collection_probability (law : FinDist Outcome) (observe : Outcome → Observation)
    (audit : Observation → FinDist (Player → Bool)) (who : Player) :
    (((law.map observe).bind audit).map (fun verdict => verdict who)).prob true =
      law.expect (fun outcome => charge observe audit outcome who) := by
  rw [FinDist.map_bind, FinDist.prob_bind, FinDist.expect_map]
  rfl

/-- Zero collection probability for every player means the joint settlement
law is exactly the original payoff vector, not merely equal in expectation. -/
theorem settlement_clean (base : Outcome → Player → ℝ) (observe : Outcome → Observation)
    (audit : Observation → FinDist (Player → Bool)) (deposit : Player → ℝ)
    (outcome : Outcome) (clean : ∀ who, charge observe audit outcome who = 0) :
    settlement base observe audit deposit outcome = FinDist.pure (base outcome) := by
  have quiet (verdict : Player → Bool) (supported : verdict ∈ (audit (observe outcome)).support)
      (who : Player) : verdict who = false := by
    cases selected : verdict who with
    | false => rfl
    | true =>
        have possible : true ∈
            ((audit (observe outcome)).map (fun result => result who)).support := by
          rw [FinDist.support_map]
          exact ⟨verdict, supported, selected⟩
        have positive := FinDist.prob_pos_iff.mpr possible
        change 0 < charge observe audit outcome who at positive
        rw [clean who] at positive
        exact (lt_irrefl 0 positive).elim
  calc
    _ = (audit (observe outcome)).map (fun _ => base outcome) := by
      apply FinDist.map_congr_of_eq_on_support
      intro verdict supported
      funext who
      simp only [quiet verdict supported who, Bool.false_eq_true, ite_false, sub_zero]
    _ = _ := by simp only [FinDist.map_eq_bind, FinDist.bind_const]

end GameTheory.Enforcement.TerminalAudit

namespace GameTheory.Protocol.InformationModel.ActionRestriction

open GameTheory.Math.Probability ExecutionProtocol Enforcement.TerminalAudit

variable {Player Observation : Type} [Fintype Player] [DecidableEq Player]
  {E T : ExecutionProtocol Player} {M : InformationModel E} {N : InformationModel T}
  [Finite T.History]
  [∀ who, DecidableEq (N.InfoState who)]
  [∀ who (site : M.InformationSite who), Fintype (M.InformationHistory who site.1)]
  [∀ who (site : N.InformationSite who), Fintype (N.InformationHistory who site.1)]
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
    (reference : N.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (decisionRecall : N.DecisionRecall) (horizon : Nat) (bounded : T.BoundedHorizon horizon)
    (depth : ∀ who, N.InformationSite who → Nat)
    (clock : ∀ who site, InformationSite.CommonDepth N site (depth who site))
    (sourcePayoff : E.History → Player → ℝ) (base : T.History → Player → ℝ)
    (observe : T.History → Observation) (audit : Observation → FinDist (Player → Bool))
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
        detection who ≤ ((((N.runBehavioralFrom
          (Profile.update (sig := N.behavioralSignature) profile who
            ((profile who).commit (restriction.site who site).1 action))
          (horizon - depth who (restriction.site who site))
          (restriction.history history.1)).map observe).bind audit).map
            (fun verdict => verdict who)).prob true)
    (source : M.BehavioralAssessment)
    (sourceEquilibrium : source.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
      source.continuationContext site (fun history => sourcePayoff history who)
        (horizon - depth who (restriction.site who site)))) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibriumFor decisionRecall.antichain
        (fun who site => target.continuationContext site
          (fun history => utility base observe audit deposit history who)
          (horizon - depth who site)) ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      (M.runBehavioral source.strategy horizon).map restriction.history =
        N.runBehavioral target.strategy horizon ∧
      (M.runBehavioral source.strategy horizon).map
          (fun history => (restriction.history history, sourcePayoff history)) =
        (N.runBehavioral target.strategy horizon).bind (fun history =>
          (settlement base observe audit deposit history).map (fun payoffs => (history, payoffs))) ∧
      (∀ history ∈ (N.runBehavioral target.strategy horizon).support,
        ∀ who, charge observe audit history who = 0) ∧
      ∀ history ∈ (N.runBehavioral target.strategy horizon).support,
        T.terminal history.state := by
  have collects : ∀ (profile : ∀ who, N.BehavioralPolicy who) who
      (site : M.InformationSite who)
      (action : N.Choice who (restriction.site who site).1),
      action ∉ Set.range (restriction.choice who site.1) →
      ∀ history : M.InformationHistory who site.1,
        detection who ≤ (N.runBehavioralFrom
          (Profile.update (sig := N.behavioralSignature) profile who
            ((profile who).commit (restriction.site who site).1 action))
          (horizon - depth who (restriction.site who site))
          (restriction.history history.1)).expect
            (fun final => charge observe audit final who) := by
    intro profile who site action extra history
    rw [← collection_probability]
    exact collection profile who site action extra history
  obtain ⟨target, equilibrium, agrees, beliefs, laws, _payoffs, terminal⟩ :=
    restriction.sequential_equilibrium_extends sourceAntichain reference referenceMixed
      decisionRecall horizon bounded depth clock sourcePayoff base (charge observe audit)
      matching sound lower upper detection deposit deposit_nonnegative source_lower target_upper
      sufficient collects source sourceEquilibrium
  refine ⟨target, equilibrium, agrees, beliefs, laws, ?_, ?_, terminal⟩
  · rw [← laws, FinDist.bind_map]
    calc
      _ = (M.runBehavioral source.strategy horizon).bind (fun history =>
          FinDist.pure (restriction.history history, sourcePayoff history)) :=
        FinDist.map_eq_bind _ _
      _ = _ := by
        apply FinDist.bind_congr
        intro history _
        rw [settlement_clean base observe audit deposit _ (sound history), FinDist.map_pure]
        congr 1
        exact congrArg (fun payoffs => (restriction.history history, payoffs))
          (funext (matching history)).symm
  · intro history supported who
    rw [← laws, FinDist.support_map] at supported
    obtain ⟨original, _, rfl⟩ := supported
    exact sound original who

end GameTheory.Protocol.InformationModel.ActionRestriction
