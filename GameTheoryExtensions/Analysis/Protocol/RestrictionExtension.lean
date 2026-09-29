/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.RestrictionCompletion
import GameTheoryExtensions.Analysis.Protocol.RestrictionIncentives
import GameTheoryExtensions.Analysis.Protocol.SequentialOneShot

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

/-- Extend every source SE when each additional target action is bounded by
a whole legal source continuation under every paired profile and finite
posterior. One continuation serves all hidden histories in that posterior.
The comparison may repair later choices as well as the current action; it
contains no premise that any target continuation is rational.

The common consistency construction supplies rational play at new information
sites. Source whole-policy rationality and the comparison establish incentives
at retained sites, with exact initialized history and payoff laws. -/
theorem sequential_equilibrium_extends_of_continuation
    (sourceAntichain : M.DecisionInformationAntichain)
    (reference : N.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (decisionRecall : N.DecisionRecall) (horizon : Nat) (bounded : T.BoundedHorizon horizon)
    (depth : ∀ who, N.InformationSite who → Nat)
    (clock : ∀ who site, InformationSite.CommonDepth N site (depth who site))
    (sourcePayoff : E.History → Player → ℝ) (targetPayoff : T.History → Player → ℝ)
    (matching : ∀ history who,
      targetPayoff (restriction.history history) who = sourcePayoff history who)
    (comparison : ∀ (sourceProfile : ∀ who, M.BehavioralPolicy who)
      (targetProfile : ∀ who, N.BehavioralPolicy who),
      restriction.ExtendsProfile sourceProfile targetProfile →
      ∀ who (site : M.InformationSite who)
        (action : N.Choice who (restriction.site who site).1),
        action ∉ Set.range (restriction.choice who site.1) →
        ∀ belief : PMF (M.InformationHistory who site.1),
          ∃ alternative : M.BehavioralPolicy who,
            expect belief (fun history => expect (N.runBehavioralFrom
              (Profile.update (sig := N.behavioralSignature) targetProfile who
                ((targetProfile who).commit (restriction.site who site).1 action))
              (horizon - depth who (restriction.site who site))
              (restriction.history history.1)) (fun final => targetPayoff final who)) ≤
            expect belief (fun history => expect (M.runBehavioralFrom
              (Profile.update (sig := M.behavioralSignature) sourceProfile who alternative)
              (horizon - depth who (restriction.site who site))
              history.1) (fun final => sourcePayoff final who)))
    (source : M.BehavioralAssessment)
    (sourceEquilibrium : source.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
      source.continuationContext site (fun history => sourcePayoff history who)
        (horizon - depth who (restriction.site who site)))) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        decisionRecall.decisionInformationAntichain
        (fun who site => target.continuationContext site
          (fun history => targetPayoff history who) (horizon - depth who site)) ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      (M.runBehavioral source.strategy horizon).map restriction.history =
        N.runBehavioral target.strategy horizon ∧
      (M.runBehavioral source.strategy horizon).map
          (fun history => (restriction.history history, sourcePayoff history)) =
        (N.runBehavioral target.strategy horizon).map (fun history =>
          (history, targetPayoff history)) ∧
      ∀ history ∈ (N.runBehavioral target.strategy horizon).support,
        T.terminal history.state := by
  classical
  have within (who : Player) (site : N.InformationSite who) : depth who site ≤ horizon := by
    have before : depth who site < horizon := by
      by_contra late
      have stopped := bounded site.2.choose.1.state site.2.choose.1.trace
        (by have := clock who site site.2.choose; omega)
      exact site.2.choose_spec.1 stopped
    exact before.le
  obtain ⟨target, consistent, agrees, beliefs, newOptimal⟩ :=
    restriction.exists_consistent_extension source sourceAntichain sourceEquilibrium.2
      reference referenceMixed decisionRecall horizon targetPayoff depth clock within
  have rational : target.IsSequentiallyRational fun who site =>
      target.continuationContext site (fun history => targetPayoff history who)
        (horizon - depth who site) := by
    apply consistent.sequentiallyRational_of_localOptimal decisionRecall horizon
      (fun who history => targetPayoff history who) depth clock within
    intro who site _ law
    by_cases retained : restriction.Retained who site.1
    · obtain ⟨original, observed⟩ := retained
      have same : restriction.site who original = site := Subtype.ext observed
      subst site
      have _ : Finite E.History :=
        Finite.of_injective restriction.history restriction.history.injective
      apply restriction.retained_localOptimal_of_continuation source target agrees decisionRecall
        who original (beliefs who original) (fun history => sourcePayoff history who)
        (fun history => targetPayoff history who) (fun history => matching history who)
        (horizon - depth who (restriction.site who original)) (sourceEquilibrium.1 who original)
        (fun _ => payoffIntegrable_of_finite _ _) (fun _ => payoffIntegrable_of_finite _ _) _ law
      intro action extra
      obtain ⟨alternative, bound⟩ := comparison source.strategy target.strategy agrees who original
        action extra (source.belief who original)
      refine ⟨alternative, ?_⟩
      have _ : Finite E.History :=
        Finite.of_injective restriction.history restriction.history.injective
      rw [BehavioralAssessment.continuationContext_value,
        BehavioralAssessment.continuationContext_value, beliefs, PMF.bind_map,
        expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _),
        expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _)]
      simpa only [Function.comp_apply, informationHistory_val] using bound
    · exact newOptimal who site retained law
  have historyLaw := restriction.initialized_law source.strategy target.strategy agrees horizon
  refine ⟨target, ⟨rational, consistent⟩, agrees, beliefs, historyLaw, ?_, ?_⟩
  · calc
      _ = ((M.runBehavioral source.strategy horizon).map restriction.history).map
          (fun history => (history, targetPayoff history)) := by
        rw [PMF.map_comp]
        congr 1
        funext history
        have samePayoff : sourcePayoff history = targetPayoff (restriction.history history) :=
          funext fun who => (matching history who).symm
        exact congrArg (fun values : Player → ℝ => (restriction.history history, values)) samePayoff
      _ = _ := congrArg (PMF.map _) historyLaw
  · intro history supported
    exact N.runBehavioralFrom_terminal_of_bound target.strategy bounded
      T.initHistory history supported

/-- A fixed legal comparator for each additional action suffices when its
actual continuation value bounds the extra action under every paired profile.
The comparator is independent of the hidden history and future random draws.
This admits harmless undetectable actions and covers finite sanction tables;
neither detection nor a positive utility loss is required on every row. -/
theorem sequential_equilibrium_extends_of_comparator
    [∀ who, DecidableEq (M.InfoState who)]
    (sourceAntichain : M.DecisionInformationAntichain)
    (reference : N.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (decisionRecall : N.DecisionRecall) (horizon : Nat) (bounded : T.BoundedHorizon horizon)
    (depth : ∀ who, N.InformationSite who → Nat)
    (clock : ∀ who site, InformationSite.CommonDepth N site (depth who site))
    (sourcePayoff : E.History → Player → ℝ) (targetPayoff : T.History → Player → ℝ)
    (matching : ∀ history who,
      targetPayoff (restriction.history history) who = sourcePayoff history who)
    (comparator : ∀ who (site : M.InformationSite who),
      N.Choice who (restriction.site who site).1 → PMF (M.Choice who site.1))
    (comparison : ∀ (sourceProfile : ∀ who, M.BehavioralPolicy who)
      (targetProfile : ∀ who, N.BehavioralPolicy who),
      restriction.ExtendsProfile sourceProfile targetProfile →
      ∀ who (site : M.InformationSite who)
        (action : N.Choice who (restriction.site who site).1),
        action ∉ Set.range (restriction.choice who site.1) →
        ∀ history : M.InformationHistory who site.1,
          expect (N.runBehavioralFrom
            (Profile.update (sig := N.behavioralSignature) targetProfile who
              ((targetProfile who).commit (restriction.site who site).1 action))
            (horizon - depth who (restriction.site who site))
            (restriction.history history.1)) (fun final => targetPayoff final who) ≤
          expect (M.runBehavioralFrom
            (Profile.update (sig := M.behavioralSignature) sourceProfile who
              ((sourceProfile who).withLaw site.1 (comparator who site action)))
            (horizon - depth who (restriction.site who site))
            history.1) (fun final => sourcePayoff final who))
    (source : M.BehavioralAssessment)
    (sourceEquilibrium : source.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
      source.continuationContext site (fun history => sourcePayoff history who)
        (horizon - depth who (restriction.site who site)))) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        decisionRecall.decisionInformationAntichain
        (fun who site => target.continuationContext site
          (fun history => targetPayoff history who) (horizon - depth who site)) ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      (M.runBehavioral source.strategy horizon).map restriction.history =
        N.runBehavioral target.strategy horizon ∧
      (M.runBehavioral source.strategy horizon).map
          (fun history => (restriction.history history, sourcePayoff history)) =
        (N.runBehavioral target.strategy horizon).map (fun history =>
          (history, targetPayoff history)) ∧
      ∀ history ∈ (N.runBehavioral target.strategy horizon).support,
        T.terminal history.state := by
  apply restriction.sequential_equilibrium_extends_of_continuation sourceAntichain reference
    referenceMixed decisionRecall horizon bounded depth clock sourcePayoff targetPayoff matching
    _ source sourceEquilibrium
  intro sourceProfile targetProfile agrees who site action extra belief
  refine ⟨(sourceProfile who).withLaw site.1 (comparator who site action), ?_⟩
  have _ : Finite E.History :=
    Finite.of_injective restriction.history restriction.history.injective
  exact expect_mono (fun history _ =>
    comparison sourceProfile targetProfile agrees who site action extra history)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)

omit [∀ who, DecidableEq (N.InfoState who)] in
/-- Restoring choices of payoff-indifferent players preserves every restricted
sequential equilibrium. Other players retain all choices at their existing
information sites. This supports a strategic zero-utility reporter without
assuming its reporting policy is the unique or strict best response.

Indifference concerns actual utility at every target history. It is not enough
for reporting costs or payoffs merely to vanish along the implemented play. -/
theorem sequential_equilibrium_extends_of_indifference
    (sourceAntichain : M.DecisionInformationAntichain)
    (reference : N.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (decisionRecall : N.DecisionRecall) (horizon : Nat) (bounded : T.BoundedHorizon horizon)
    (depth : ∀ who, N.InformationSite who → Nat)
    (clock : ∀ who site, InformationSite.CommonDepth N site (depth who site))
    (sourcePayoff : E.History → Player → ℝ) (targetPayoff : T.History → Player → ℝ)
    (matching : ∀ history who,
      targetPayoff (restriction.history history) who = sourcePayoff history who)
    (unchangedOrIndifferent : ∀ who,
      (∀ info, Function.Surjective (restriction.choice who info)) ∨
        ∃ constant, ∀ history, targetPayoff history who = constant)
    (source : M.BehavioralAssessment)
    (sourceEquilibrium : source.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
      source.continuationContext site (fun history => sourcePayoff history who)
        (horizon - depth who (restriction.site who site)))) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibriumFor decisionRecall.decisionInformationAntichain
        (fun who site => target.continuationContext site
          (fun history => targetPayoff history who) (horizon - depth who site)) ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      (M.runBehavioral source.strategy horizon).map restriction.history =
        N.runBehavioral target.strategy horizon ∧
      (M.runBehavioral source.strategy horizon).map
          (fun history => (restriction.history history, sourcePayoff history)) =
        (N.runBehavioral target.strategy horizon).map
          (fun history => (history, targetPayoff history)) ∧
      ∀ history ∈ (N.runBehavioral target.strategy horizon).support,
        T.terminal history.state := by
  classical
  let comparator (who : Player) (site : M.InformationSite who)
      (_ : N.Choice who (restriction.site who site).1) : PMF (M.Choice who site.1) :=
    PMF.pure ⟨some site.2.choose_spec.2.choose, site.2.choose_spec.2.choose_spec⟩
  apply restriction.sequential_equilibrium_extends_of_comparator sourceAntichain
    reference referenceMixed decisionRecall horizon bounded depth clock
    sourcePayoff targetPayoff matching comparator _ source sourceEquilibrium
  intro sourceProfile targetProfile _ who site action extra history
  rcases unchangedOrIndifferent who with unchanged | ⟨constant, indifferent⟩
  · exact (extra (unchanged site.1 action)).elim
  · have sourceConstant (final : E.History) : sourcePayoff final who = constant := by
      rw [← matching]
      exact indifferent _
    simp only [indifferent, sourceConstant, expect_constant, le_refl]

/-- Every source sequential equilibrium extends to the same fixed target
game under finite, sound, sufficiently costly first-departure collection.
The collection condition covers arbitrary target continuation profiles and
actual hidden histories; it contains no rational-completion premise.
Weak deterrence inequalities suffice for this forward existence conclusion. -/
theorem sequential_equilibrium_extends
    (sourceAntichain : M.DecisionInformationAntichain)
    (reference : N.BehavioralAssessment) (referenceMixed : reference.IsFullyMixed)
    (decisionRecall : N.DecisionRecall) (horizon : Nat) (bounded : T.BoundedHorizon horizon)
    (depth : ∀ who, N.InformationSite who → Nat)
    (clock : ∀ who site, InformationSite.CommonDepth N site (depth who site))
    (sourcePayoff : E.History → Player → ℝ) (base charge : T.History → Player → ℝ)
    (matching : ∀ history who, base (restriction.history history) who = sourcePayoff history who)
    (clean : ∀ history who, charge (restriction.history history) who = 0)
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
        detection who ≤ expect (N.runBehavioralFrom
          (Profile.update (sig := N.behavioralSignature) profile who
            ((profile who).commit (restriction.site who site).1 action))
          (horizon - depth who (restriction.site who site))
          (restriction.history history.1)) (fun final => charge final who))
    (source : M.BehavioralAssessment)
    (sourceEquilibrium : source.IsSequentialEquilibriumFor sourceAntichain (fun who site =>
      source.continuationContext site (fun history => sourcePayoff history who)
        (horizon - depth who (restriction.site who site)))) :
    ∃ target : N.BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        decisionRecall.decisionInformationAntichain
        (fun who site => target.continuationContext site
          (fun history => base history who - charge history who * deposit who)
          (horizon - depth who site)) ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      (M.runBehavioral source.strategy horizon).map restriction.history =
        N.runBehavioral target.strategy horizon ∧
      (M.runBehavioral source.strategy horizon).map
          (fun history => (restriction.history history, sourcePayoff history)) =
        (N.runBehavioral target.strategy horizon).map (fun history =>
          (history, fun who => base history who - charge history who * deposit who)) ∧
      ∀ history ∈ (N.runBehavioral target.strategy horizon).support,
        T.terminal history.state := by
  classical
  let utility := fun history who => base history who - charge history who * deposit who
  let comparator (who : Player) (site : M.InformationSite who)
      (_ : N.Choice who (restriction.site who site).1) : PMF (M.Choice who site.1) :=
    PMF.pure ⟨some site.2.choose_spec.2.choose, site.2.choose_spec.2.choose_spec⟩
  apply restriction.sequential_equilibrium_extends_of_comparator sourceAntichain
    reference referenceMixed decisionRecall horizon bounded depth clock sourcePayoff utility
    (fun history who => by simp only [utility, matching, clean, zero_mul, sub_zero])
    comparator _ source sourceEquilibrium
  intro sourceProfile targetProfile _ who site action forbidden history
  have _ : Finite E.History :=
    Finite.of_injective restriction.history restriction.history.injective
  rw [show (fun final => utility final who) =
      (fun final => base final who - charge final who * deposit who) from rfl,
    expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
    expect_mul_const]
  have upperBound : expect (N.runBehavioralFrom
      (Profile.update (sig := N.behavioralSignature) targetProfile who
        ((targetProfile who).commit (restriction.site who site).1 action))
      (horizon - depth who (restriction.site who site))
      (restriction.history history.1)) (fun final => base final who) ≤ upper who := by
    exact expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
      fun final _ => target_upper final who
  have netBound := sub_le_sub upperBound
    (mul_le_mul_of_nonneg_right (collection targetProfile who site action forbidden history)
      (deposit_nonnegative who))
  apply (netBound.trans (sufficient who)).trans
  exact (expect_constant _ (lower who)).symm.trans_le
    (expect_mono (fun final _ => source_lower final who) (payoffIntegrable_constant _ _)
      (payoffIntegrable_of_finite _ _))

end GameTheory.Protocol.InformationModel.ActionRestriction
