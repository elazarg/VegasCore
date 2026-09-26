/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Protocol.RestrictionExecution
import GameTheory.Analysis.Protocol.CounterfactualRegret

/-! # Incentives at information sites retained by an action restriction

Compliant continuation values follow from the actual execution square and a
mapped history belief. Sanctions then control the additional pure choices;
affinity at a perfect-recall information site covers arbitrary local lotteries.
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
    (site : M.InformationSite who) (law : FinDist (M.Choice who site.1)) :
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

/-- The history-level execution law transports continuation values, including
off-path beliefs, whenever the compared updated profiles are compliant. -/
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
  simp only [BehavioralAssessment.continuationContext_value, belief,
    FinDist.expect_bind, FinDist.expect_map]
  apply FinDist.expect_congr
  intro history _
  rw [informationHistory_val, ← restriction.runFrom_law _ _ agrees,
    FinDist.expect_map]
  exact FinDist.expect_congr fun next _ => payoff next

/-- In particular, an arbitrary lawful one-site deviation has exactly its
source continuation value. -/
theorem context_withLaw_value_eq
    (source : M.BehavioralAssessment) (target : N.BehavioralAssessment)
    (agrees : restriction.ExtendsProfile source.strategy target.strategy)
    (who : Player) [DecidableEq (M.InfoState who)] [DecidableEq (N.InfoState who)]
    (site : M.InformationSite who)
    (belief : target.belief who (restriction.site who site) =
      (source.belief who site).map (restriction.informationHistory who site))
    (law : FinDist (M.Choice who site.1))
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

private theorem context_withLaw_affine (target : N.BehavioralAssessment)
    (recall : N.PerfectRecall) (who : Player) [DecidableEq (N.InfoState who)]
    (site : N.InformationSite who) (payoff : T.History → ℝ) (fuel : Nat)
    (law : FinDist (N.Choice who site.1)) :
    (target.continuationContext site payoff fuel).value
        ((target.strategy who).withLaw site.1 law) =
      law.expect (fun choice => (target.continuationContext site payoff fuel).value
        ((target.strategy who).commit site.1 choice)) := by
  simp only [BehavioralAssessment.continuationContext_value, FinDist.expect_bind]
  have each (history : N.InformationHistory who site.1) :
      (N.runBehavioralFrom
        (Profile.update (sig := N.behavioralSignature) target.strategy who
          ((target.strategy who).withLaw site.1 law)) fuel history.1).expect payoff =
      law.expect (fun choice => (N.runBehavioralFrom
        (Profile.update (sig := N.behavioralSignature) target.strategy who
          ((target.strategy who).commit site.1 choice)) fuel history.1).expect payoff) := by
    cases fuel with
    | zero =>
        simp only [runBehavioralFrom, runRandomizedFor_zero,
          FinDist.expect_pure, FinDist.expect_const]
    | succ fuel =>
        by_cases stopped : T.terminal history.1.state
        · simp only [N.runBehavioralFrom_of_terminal _ _ stopped,
            FinDist.expect_pure, FinDist.expect_const]
        · exact N.behavioralContinuationValue_withLaw_eq_expect
            (N.actsOnceWhereItMatters_of_perfectRecall recall) target.strategy who site
            (target.strategy who) law history stopped payoff fuel
  calc
    _ = (target.belief who site).expect (fun history => law.expect (fun choice =>
        (N.runBehavioralFrom
          (Profile.update (sig := N.behavioralSignature) target.strategy who
            ((target.strategy who).commit site.1 choice)) fuel history.1).expect payoff)) :=
      FinDist.expect_congr fun history _ => each history
    _ = _ := FinDist.expect_comm _ _ _

/-- Each forbidden action is bounded by one legal source lottery, shared by
all hidden histories in the information set. The comparison concerns actual
execution under the same remaining paired profiles, so it cannot select a
comparator using hidden state or future opponents' random draws. -/
theorem retained_localOptimal_of_comparator
    (source : M.BehavioralAssessment) (target : N.BehavioralAssessment)
    (agrees : restriction.ExtendsProfile source.strategy target.strategy)
    (recall : N.PerfectRecall)
    (who : Player) [DecidableEq (M.InfoState who)] [DecidableEq (N.InfoState who)]
    (site : M.InformationSite who)
    (belief : target.belief who (restriction.site who site) =
      (source.belief who site).map (restriction.informationHistory who site))
    (sourcePayoff : E.History → ℝ) (targetPayoff : T.History → ℝ)
    (payoff : ∀ history, targetPayoff (restriction.history history) = sourcePayoff history)
    (fuel : Nat)
    (rational : source.IsSequentiallyRationalAt site
      (source.continuationContext site sourcePayoff fuel))
    (comparator : N.Choice who (restriction.site who site).1 → FinDist (M.Choice who site.1))
    (comparison : ∀ action : N.Choice who (restriction.site who site).1,
      action ∉ Set.range (restriction.choice who site.1) →
      ∀ history : M.InformationHistory who site.1,
        (N.runBehavioralFrom
          (Profile.update (sig := N.behavioralSignature) target.strategy who
            ((target.strategy who).commit (restriction.site who site).1 action))
          fuel (restriction.history history.1)).expect targetPayoff ≤
        (M.runBehavioralFrom
          (Profile.update (sig := M.behavioralSignature) source.strategy who
            ((source.strategy who).withLaw site.1 (comparator action)))
          fuel history.1).expect sourcePayoff)
    (law : FinDist (N.Choice who (restriction.site who site).1)) :
    (target.continuationContext (restriction.site who site) targetPayoff fuel).value
        ((target.strategy who).withLaw (restriction.site who site).1 law) ≤
      (target.continuationContext (restriction.site who site) targetPayoff fuel).value
        (target.strategy who) := by
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
        (FinDist.pure original) sourcePayoff targetPayoff payoff fuel
      simp only [FinDist.map_pure] at equality
      change (target.continuationContext _ targetPayoff fuel).value
          ((target.strategy who).withLaw _ (FinDist.pure _)) ≤ _
      rw [equality, baseline]
      exact rational ((source.strategy who).withLaw site.1 (FinDist.pure original)) (Set.mem_univ _)
    · apply le_trans _ ((rational
        ((source.strategy who).withLaw site.1 (comparator action)) (Set.mem_univ _)).trans_eq
          baseline.symm)
      simp only [BehavioralAssessment.continuationContext_value, belief,
        FinDist.expect_bind, FinDist.expect_map, informationHistory_val]
      exact FinDist.expect_mono fun history _ => comparison action permitted history
  rw [context_withLaw_affine target recall who (restriction.site who site) targetPayoff fuel law]
  exact (FinDist.expect_mono fun action _ => pureOptimal action).trans_eq (FinDist.expect_const _ _)

end GameTheory.Protocol.InformationModel.ActionRestriction
