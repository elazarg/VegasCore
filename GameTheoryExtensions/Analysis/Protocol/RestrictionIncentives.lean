/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.DecisionRecall
import GameTheoryExtensions.Protocol.RestrictionExecution
import GameTheory.Analysis.Protocol.CounterfactualRegret
import GameTheory.Protocol.BehavioralMixture

/-! # Incentives at information sites retained by an action restriction

Compliant continuation values follow from the actual execution square and a
mapped history belief. Sanctions then control the additional pure choices;
affinity at a decision-recall information site covers arbitrary local lotteries.
The construction of consistent target beliefs is separate from these incentive
arguments.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel.ActionRestriction

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E T : ExecutionProtocol Player} {M : InformationModel E} {N : InformationModel T}
  (restriction : M.ActionRestriction N)

omit [Fintype Player] in
/-- Installing corresponding local laws preserves the structural extension. -/
theorem extends_withLaw (source : ∀ who, M.BehavioralPolicy who)
    (target : ∀ who, N.BehavioralPolicy who)
    (agrees : restriction.ExtendsProfile source target)
    (who : Player) [DecidableEq (M.InfoState who)] [DecidableEq (N.InfoState who)]
    (site : M.InformationSite who) (law : PMF (M.Choice who site.1)) :
    restriction.ExtendsProfile
      (Profile.update (sig := M.behavioralSignature) source who
        ((source who).withLaw site.1 law))
      (Profile.update (sig := N.behavioralSignature) target who
        ((target who).withLaw (restriction.site who site).1
          (law.map (restriction.choice who site.1)))) := by
  intro other current
  by_cases samePlayer : other = who
  · subst other
    rw [Profile.update_same, Profile.update_same]
    by_cases sameSite : current.1 = site.1
    · have equal : current = site := Subtype.ext sameSite
      subst current
      simp only [site_val, BehavioralPolicy.withLaw_self]
    · rw [BehavioralPolicy.withLaw_of_ne _ _ _ sameSite,
        BehavioralPolicy.withLaw_of_ne _ _ _ (by
          exact fun equal => sameSite ((restriction.information who).injective equal))]
      exact agrees who current
  · rw [Profile.update_of_ne _ _ samePlayer, Profile.update_of_ne _ _ samePlayer]
    exact agrees other current

/-- The history-level execution law transports continuation laws, including
off-path beliefs, whenever the compared updated profiles are compliant. -/
theorem context_outcome_eq (source : M.BehavioralAssessment) (target : N.BehavioralAssessment)
    (who : Player) (site : M.InformationSite who)
    (belief : target.belief who (restriction.site who site) =
      (source.belief who site).map (restriction.informationHistory who site))
    (original : M.BehavioralPolicy who) (translated : N.BehavioralPolicy who)
    (agrees : restriction.ExtendsProfile
      (Profile.update (sig := M.behavioralSignature) source.strategy who original)
      (Profile.update (sig := N.behavioralSignature) target.strategy who translated))
    (sourcePayoff : E.History → ℝ) (targetPayoff : T.History → ℝ) (fuel : Nat) :
    (target.continuationContext (restriction.site who site) targetPayoff fuel).outcome
        translated =
      ((source.continuationContext site sourcePayoff fuel).outcome original).map
        restriction.history := by
  change (target.belief who (restriction.site who site)).bind _ =
    ((source.belief who site).bind _).map restriction.history
  rw [belief, PMF.bind_map, PMF.map_bind]
  apply bind_congr_on_support
  intro history _
  simp only [Function.comp_apply, informationHistory_val]
  exact (restriction.runFrom_law _ _ agrees fuel history.1).symm

/-- Corresponding continuation values agree when the payoffs correspond. -/
theorem context_value_eq (source : M.BehavioralAssessment) (target : N.BehavioralAssessment)
    (who : Player) (site : M.InformationSite who)
    (belief : target.belief who (restriction.site who site) =
      (source.belief who site).map (restriction.informationHistory who site))
    (original : M.BehavioralPolicy who) (translated : N.BehavioralPolicy who)
    (agrees : restriction.ExtendsProfile
      (Profile.update (sig := M.behavioralSignature) source.strategy who original)
      (Profile.update (sig := N.behavioralSignature) target.strategy who translated))
    (sourcePayoff : E.History → ℝ) (targetPayoff : T.History → ℝ)
    (payoff : ∀ history, targetPayoff (restriction.history history) = sourcePayoff history)
    (fuel : Nat) :
    (target.continuationContext (restriction.site who site) targetPayoff fuel).value translated =
      (source.continuationContext site sourcePayoff fuel).value original := by
  unfold Context.value
  rw [restriction.context_outcome_eq source target who site belief original translated agrees
    sourcePayoff targetPayoff fuel, expect_map]
  exact expect_congr_on_support fun history _ => payoff history

/-- In particular, an arbitrary lawful one-site deviation has exactly its
source continuation value. -/
theorem context_withLaw_value_eq
    (source : M.BehavioralAssessment) (target : N.BehavioralAssessment)
    (agrees : restriction.ExtendsProfile source.strategy target.strategy)
    (who : Player) [DecidableEq (M.InfoState who)] [DecidableEq (N.InfoState who)]
    (site : M.InformationSite who)
    (belief : target.belief who (restriction.site who site) =
      (source.belief who site).map (restriction.informationHistory who site))
    (law : PMF (M.Choice who site.1))
    (sourcePayoff : E.History → ℝ) (targetPayoff : T.History → ℝ)
    (payoff : ∀ history, targetPayoff (restriction.history history) = sourcePayoff history)
    (fuel : Nat) :
    (target.continuationContext (restriction.site who site) targetPayoff fuel).value
        ((target.strategy who).withLaw (restriction.site who site).1
          (law.map (restriction.choice who site.1))) =
      (source.continuationContext site sourcePayoff fuel).value
        ((source.strategy who).withLaw site.1 law) :=
  restriction.context_value_eq source target who site belief _ _
    (restriction.extends_withLaw source.strategy target.strategy agrees who site law)
    sourcePayoff targetPayoff payoff fuel

/-- At a decision-recall site the continuation law after a local response law
is the mixture, over that response, of the laws with one committed choice. -/
private theorem context_outcome_withLaw
    (target : N.BehavioralAssessment) (recall : N.DecisionRecall) (who : Player)
    [DecidableEq (N.InfoState who)] (site : N.InformationSite who) (payoff : T.History → ℝ)
    (fuel : Nat) (law : PMF (N.Choice who site.1)) :
    (target.continuationContext site payoff fuel).outcome
        ((target.strategy who).withLaw site.1 law) =
      law.bind fun choice => (target.continuationContext site payoff fuel).outcome
        ((target.strategy who).commit site.1 choice) := by
  change (target.belief who site).bind _ = law.bind fun choice => (target.belief who site).bind _
  rw [← PMF.bind_comm]
  apply bind_congr_on_support
  intro history _
  cases fuel with
  | zero =>
      simp only [runBehavioralFrom, runRandomizedFor_zero, PMF.bind_const]
  | succ fuel =>
      by_cases stopped : T.terminal history.1.state
      · simp only [N.runBehavioralFrom_of_terminal _ _ stopped, PMF.bind_const]
      · exact N.runBehavioralFrom_update_withLaw_eq_bind recall.actsOnceWhereItMatters
          target.strategy who (target.strategy who) site.1 law history.1 history.2 stopped
          (InformationSite.active N site history) fuel

private theorem context_withLaw_affine (target : N.BehavioralAssessment)
    (recall : N.DecisionRecall) (who : Player) [DecidableEq (N.InfoState who)]
    (site : N.InformationSite who) (payoff : T.History → ℝ) (fuel : Nat)
    (law : PMF (N.Choice who site.1))
    (integrable : (target.continuationContext site payoff fuel).IntegrableAt
      ((target.strategy who).withLaw site.1 law)) :
    (target.continuationContext site payoff fuel).value
        ((target.strategy who).withLaw site.1 law) =
      expect law (fun choice => (target.continuationContext site payoff fuel).value
        ((target.strategy who).commit site.1 choice)) ∧
    PayoffIntegrable law (fun choice => (target.continuationContext site payoff fuel).value
        ((target.strategy who).commit site.1 choice)) := by
  unfold Context.IntegrableAt at integrable
  rw [context_outcome_withLaw target recall who site payoff fuel law] at integrable
  refine ⟨?_, payoffIntegrable_bind_conditionalExpectation _ _ _ integrable⟩
  unfold Context.value
  rw [context_outcome_withLaw target recall who site payoff fuel law]
  exact expect_bind_tower _ _ _ integrable

/-- Each extra target choice can be compared with an entire legal source
continuation, uniformly over the current posterior. The replacement may change
future source choices; sequential rationality bounds the whole policy. It need
not be the same comparator at different beliefs, but cannot use the actual
hidden history when selecting its policy. Every target continuation deviation
at the site must have a finite expected payoff. -/
theorem retained_localOptimal_of_continuation
    (source : M.BehavioralAssessment) (target : N.BehavioralAssessment)
    (agrees : restriction.ExtendsProfile source.strategy target.strategy)
    (recall : N.DecisionRecall)
    (who : Player) [DecidableEq (N.InfoState who)]
    (site : M.InformationSite who)
    (belief : target.belief who (restriction.site who site) =
      (source.belief who site).map (restriction.informationHistory who site))
    (sourcePayoff : E.History → ℝ) (targetPayoff : T.History → ℝ)
    (payoff : ∀ history, targetPayoff (restriction.history history) = sourcePayoff history)
    (fuel : Nat)
    (rational : source.IsSequentiallyRationalAt site
      (source.continuationContext site sourcePayoff fuel))
    (sourceIntegrable : ∀ policy,
      (source.continuationContext site sourcePayoff fuel).IntegrableAt policy)
    (targetIntegrable : ∀ policy,
      (target.continuationContext (restriction.site who site) targetPayoff fuel).IntegrableAt
        policy)
    (comparison : ∀ action : N.Choice who (restriction.site who site).1,
      action ∉ Set.range (restriction.choice who site.1) →
      ∃ alternative : M.BehavioralPolicy who,
        (target.continuationContext (restriction.site who site) targetPayoff fuel).value
            ((target.strategy who).commit (restriction.site who site).1 action) ≤
          (source.continuationContext site sourcePayoff fuel).value alternative)
    (law : PMF (N.Choice who (restriction.site who site).1)) :
    (target.continuationContext (restriction.site who site) targetPayoff fuel).value
        ((target.strategy who).withLaw (restriction.site who site).1 law) ≤
      (target.continuationContext (restriction.site who site) targetPayoff fuel).value
        (target.strategy who) := by
  classical
  have real := (Context.isLocallyOptimal_iff_of_integrable (sourceIntegrable _)
    fun alternative _ => sourceIntegrable alternative).mp rational
  have baseline := restriction.context_value_eq source target who site belief
    (source.strategy who) (target.strategy who)
    (by simpa only [Profile.update_eq_self] using agrees) sourcePayoff targetPayoff payoff fuel
  have pureOptimal (action : N.Choice who (restriction.site who site).1) :
      (target.continuationContext (restriction.site who site) targetPayoff fuel).value
          ((target.strategy who).commit (restriction.site who site).1 action) ≤
        (target.continuationContext (restriction.site who site) targetPayoff fuel).value
          (target.strategy who) := by
    by_cases permitted : action ∈ Set.range (restriction.choice who site.1)
    · obtain ⟨original, rfl⟩ := permitted
      have equality := restriction.context_withLaw_value_eq source target agrees who site belief
        (PMF.pure original) sourcePayoff targetPayoff payoff fuel
      simp only [PMF.pure_map] at equality
      change (target.continuationContext _ targetPayoff fuel).value
          ((target.strategy who).withLaw _ (PMF.pure _)) ≤ _
      rw [equality, baseline]
      exact real ((source.strategy who).withLaw site.1 (PMF.pure original)) (Set.mem_univ _)
    · obtain ⟨alternative, bound⟩ := comparison action permitted
      exact bound.trans ((real alternative (Set.mem_univ _)).trans_eq baseline.symm)
  obtain ⟨affine, valueIntegrable⟩ := context_withLaw_affine target recall who
    (restriction.site who site) targetPayoff fuel law (targetIntegrable _)
  rw [affine]
  exact expect_le_const _ _ valueIntegrable _ fun action _ => pureOptimal action

/-- Each forbidden action is bounded by one legal source lottery, shared by
all hidden histories in the information set. The comparison concerns actual
execution under the same remaining paired profiles, so it cannot select a
comparator using hidden state or future opponents' random draws. Every target
continuation deviation at the site must have a finite expected payoff. -/
theorem retained_localOptimal_of_comparator
    (source : M.BehavioralAssessment) (target : N.BehavioralAssessment)
    (agrees : restriction.ExtendsProfile source.strategy target.strategy)
    (recall : N.DecisionRecall)
    (who : Player) [DecidableEq (M.InfoState who)] [DecidableEq (N.InfoState who)]
    (site : M.InformationSite who)
    (belief : target.belief who (restriction.site who site) =
      (source.belief who site).map (restriction.informationHistory who site))
    (sourcePayoff : E.History → ℝ) (targetPayoff : T.History → ℝ)
    (payoff : ∀ history, targetPayoff (restriction.history history) = sourcePayoff history)
    (fuel : Nat)
    (rational : source.IsSequentiallyRationalAt site
      (source.continuationContext site sourcePayoff fuel))
    (sourceIntegrable : ∀ policy,
      (source.continuationContext site sourcePayoff fuel).IntegrableAt policy)
    (targetIntegrable : ∀ policy,
      (target.continuationContext (restriction.site who site) targetPayoff fuel).IntegrableAt
        policy)
    (comparator : N.Choice who (restriction.site who site).1 → PMF (M.Choice who site.1))
    (comparison : ∀ action : N.Choice who (restriction.site who site).1,
      action ∉ Set.range (restriction.choice who site.1) →
      ∀ history : M.InformationHistory who site.1,
        expect (N.runBehavioralFrom
          (Profile.update (sig := N.behavioralSignature) target.strategy who
            ((target.strategy who).commit (restriction.site who site).1 action))
          fuel (restriction.history history.1)) targetPayoff ≤
        expect (M.runBehavioralFrom
          (Profile.update (sig := M.behavioralSignature) source.strategy who
            ((source.strategy who).withLaw site.1 (comparator action)))
          fuel history.1) sourcePayoff)
    (law : PMF (N.Choice who (restriction.site who site).1)) :
    (target.continuationContext (restriction.site who site) targetPayoff fuel).value
        ((target.strategy who).withLaw (restriction.site who site).1 law) ≤
      (target.continuationContext (restriction.site who site) targetPayoff fuel).value
        (target.strategy who) := by
  apply restriction.retained_localOptimal_of_continuation source target agrees recall who site
    belief sourcePayoff targetPayoff payoff fuel rational sourceIntegrable targetIntegrable _ law
  intro action extra
  let alternative := (source.strategy who).withLaw site.1 (comparator action)
  refine ⟨alternative, ?_⟩
  have targetLaw := targetIntegrable ((target.strategy who).commit (restriction.site who site).1
    action)
  have sourceLaw := sourceIntegrable alternative
  unfold Context.IntegrableAt at targetLaw sourceLaw
  unfold Context.value
  change PayoffIntegrable ((target.belief who (restriction.site who site)).bind _) _ at targetLaw
  change expect ((target.belief who (restriction.site who site)).bind _) _ ≤
    expect ((source.belief who site).bind _) _
  rw [belief, PMF.bind_map] at targetLaw ⊢
  rw [expect_bind_tower _ _ _ targetLaw, expect_bind_tower _ _ _ sourceLaw]
  apply expect_mono _ (payoffIntegrable_bind_conditionalExpectation _ _ _ targetLaw)
    (payoffIntegrable_bind_conditionalExpectation _ _ _ sourceLaw)
  intro history _
  exact comparison action extra history

end GameTheory.Protocol.InformationModel.ActionRestriction
