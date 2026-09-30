/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.Perturbation
import GameTheoryExtensions.Analysis.Protocol.Sequential
import GameTheory.Analysis.Protocol.CounterfactualRegret
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Optimal behavior at a player's last decision

If a player has no later decision, its full continuation behavior factors
through the one current choice. Finite maximization then chooses an optimal
response at each information site. If changing this player's policy leaves
every decision-history reach probability unchanged and the other players are
indifferent, a common fully mixed perturbation supplies a sequential
equilibrium. The maximization constructs an equilibrium; it is not a strategy
compiler and may depend on the utility.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ExecutionProtocol ι} {M : InformationModel E}

/-- A structural property of legal continuations, independent of strategies. -/
def LastDecision (who : ι) : Prop :=
  ∀ (history : E.History), E.active history.state who →
    ∀ (joint : ∀ player, Option (E.Action player)) (legal : E.Legal history.state joint)
      (target : E.State) (realized : target ∈ (E.step history.state ⟨joint, legal⟩).support)
      (fuel : Nat) (later : E.History),
      E.ReachesWithin fuel (history.extend legal realized) later →
        ¬ E.active later.state who

theorem LastDecision.run_eq_of_current_law {who : ι} (last : LastDecision (E := E) who)
    (profile : ∀ player, M.BehavioralPolicy player)
    (first second : M.BehavioralPolicy who) (history : E.History)
    (active : E.active history.state who)
    (same : first (M.infoOf who history.trace) = second (M.infoOf who history.trace))
    (fuel : Nat) :
    M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature) profile who first)
      fuel history =
    M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature) profile who second)
      fuel history := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      by_cases stopped : E.terminal history.state
      · rw [M.runBehavioralFrom_of_terminal _ _ stopped,
          M.runBehavioralFrom_of_terminal _ _ stopped]
      · have current : M.behavioralJoint
            (Profile.update (sig := M.behavioralSignature) profile who first)
            history.trace stopped = M.behavioralJoint
            (Profile.update (sig := M.behavioralSignature) profile who second)
            history.trace stopped := by
          apply M.behavioralJoint_congr
          intro player
          by_cases own : player = who
          · subst player
            simpa only [Profile.update_same] using same
          · rw [Profile.update_of_ne _ _ own, Profile.update_of_ne _ _ own]
        rw [M.runBehavioralFrom_succ_of_not_terminal _ fuel stopped,
          M.runBehavioralFrom_succ_of_not_terminal _ fuel stopped, current]
        apply bind_congr_on_support _
        intro draw _
        apply bindOnSupport_congr _
        intro target realized
        apply M.runBehavioralFrom_congr
        intro later reached _ player
        by_cases own : player = who
        · subst player
          rw [Profile.update_same, Profile.update_same]
          exact M.behavioral_eq_of_not_active _ _ later.trace
            (last history active draw.1 draw.2 target realized fuel later reached)
        · rw [Profile.update_of_ne _ _ own, Profile.update_of_ne _ _ own]

theorem LastDecision.run_eq_bind_choices {who : ι} (last : LastDecision (E := E) who)
    (profile : ∀ player, M.BehavioralPolicy player) (alternative : M.BehavioralPolicy who)
    [DecidableEq (M.InfoState who)] (history : E.History)
    (observed : M.InfoState who) (same : M.infoOf who history.trace = observed)
    (running : ¬ E.terminal history.state) (active : E.active history.state who)
    (fuel : Nat) :
    M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
      profile who alternative) (fuel + 1) history =
    (alternative observed).bind (fun choice =>
      M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
        profile who ((profile who).commit observed choice))
          (fuel + 1) history) := by
  subst observed
  let info := M.infoOf who history.trace
  let law := alternative info
  rw [last.run_eq_of_current_law profile alternative ((profile who).withLaw info law)
    history active (by simp [info, law])]
  rw [M.runBehavioralFrom_succ_of_not_terminal _ fuel running,
    M.behavioralJoint_update_withLaw_eq_bind profile who (profile who) info law
      history.trace running rfl, PMF.bind_bind]
  apply bind_congr_on_support _
  intro choice _
  rw [M.runBehavioralFrom_succ_of_not_terminal _ fuel running]
  apply bind_congr_on_support _
  intro draw _
  apply bindOnSupport_congr _
  intro target realized
  apply M.runBehavioralFrom_congr
  intro later reached _ player
  by_cases own : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
    exact M.behavioral_eq_of_not_active _ _ later.trace
      (last history active draw.1 draw.2 target realized fuel later reached)
  · rw [Profile.update_of_ne _ _ own, Profile.update_of_ne _ _ own]

/-- At a last decision, a deviation's continuation law is a lottery over the
current choice. Its value is therefore the average of the committed choices'
values whenever the deviation has a finite expected payoff. -/
theorem LastDecision.context_value_eq_expect {who : ι} (last : LastDecision (E := E) who)
    (assessment : M.BehavioralAssessment) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who) (nonterminal : site.AllNonterminal)
    (payoff : E.History → ℝ) (fuel : Nat) (alternative : M.BehavioralPolicy who)
    (integrable : (assessment.truncatedContinuationContext site payoff (fuel + 1)).IntegrableAt
      alternative) :
    (assessment.truncatedContinuationContext site payoff (fuel + 1)).value alternative =
      expect (alternative site.1) (fun choice =>
        (assessment.truncatedContinuationContext site payoff (fuel + 1)).value
          ((assessment.strategy who).commit site.1 choice)) := by
  let context := assessment.truncatedContinuationContext site payoff (fuel + 1)
  have factored : context.outcome alternative = (alternative site.1).bind fun choice =>
      context.outcome ((assessment.strategy who).commit site.1 choice) := by
    change (assessment.belief who site).bind _ = (alternative site.1).bind fun choice =>
      (assessment.belief who site).bind _
    rw [← PMF.bind_comm]
    apply bind_congr_on_support
    intro history _
    exact last.run_eq_bind_choices assessment.strategy alternative history.1 site.1 history.2
      (nonterminal history) (InformationSite.active M site history) fuel
  change PayoffIntegrable (context.outcome alternative) context.continuation at integrable
  change expect (context.outcome alternative) context.continuation = _
  rw [factored] at integrable ⊢
  exact expect_bind_tower _ _ _ integrable

section Finite

variable (reference : M.BehavioralAssessment) (mixed : reference.IsFullyMixed)
  (antichain : M.DecisionInformationAntichain) (who : ι)
  [∀ site : M.InformationSite who, Finite (M.Choice who site.1)]
  (payoff : E.History → ℝ) (fuel : Nat)

def lastChoiceValue (site : M.InformationSite who) (choice : M.Choice who site.1) : ℝ := by
  classical
  exact ((InformationModel.bayesAssessment _ reference.strategy mixed
      antichain).truncatedContinuationContext
    site payoff (fuel + 1)).value ((reference.strategy who).commit site.1 choice)

def bestLastChoice (site : M.InformationSite who) : M.Choice who site.1 := by
  classical
  let : Nonempty (M.Choice who site.1) :=
    ⟨(reference.strategy who site.1).support_nonempty.choose⟩
  exact Classical.choose (Finite.exists_max
    (lastChoiceValue reference mixed antichain who payoff fuel site))

theorem lastChoiceValue_le_best (site : M.InformationSite who) (choice : M.Choice who site.1) :
    lastChoiceValue reference mixed antichain who payoff fuel site choice ≤
      lastChoiceValue reference mixed antichain who payoff fuel site
        (bestLastChoice reference mixed antichain who payoff fuel site) := by
  classical
  let : Nonempty (M.Choice who site.1) :=
    ⟨(reference.strategy who site.1).support_nonempty.choose⟩
  exact Classical.choose_spec (Finite.exists_max
    (lastChoiceValue reference mixed antichain who payoff fuel site)) choice

def bestLastPolicy : M.BehavioralPolicy who := by
  classical
  exact fun info =>
    if decision : M.IsDecisionInfo who info then
      PMF.pure (bestLastChoice reference mixed antichain who payoff fuel ⟨info, decision⟩)
    else reference.strategy who info

theorem bestLastPolicy_at (site : M.InformationSite who) :
    bestLastPolicy reference mixed antichain who payoff fuel site.1 =
      PMF.pure (bestLastChoice reference mixed antichain who payoff fuel site) := by
  classical
  simp only [bestLastPolicy, site.2, ↓reduceDIte]; rfl

/-- The maximizing last choice is optimal against every deviation with a
finite expected payoff. -/
theorem bestLastPolicy_optimal (last : LastDecision (E := E) who)
    (site : M.InformationSite who) (nonterminal : site.AllNonterminal)
    (alternative : M.BehavioralPolicy who)
    (alternativeIntegrable : ((InformationModel.bayesAssessment _ reference.strategy mixed
      antichain).truncatedContinuationContext site payoff (fuel + 1)).IntegrableAt alternative)
    (bestIntegrable : ((InformationModel.bayesAssessment _ reference.strategy mixed
      antichain).truncatedContinuationContext site payoff (fuel + 1)).IntegrableAt
        (bestLastPolicy reference mixed antichain who payoff fuel)) :
    ((InformationModel.bayesAssessment _ reference.strategy mixed
        antichain).truncatedContinuationContext
      site payoff (fuel + 1)).value alternative ≤
    ((InformationModel.bayesAssessment _ reference.strategy mixed
        antichain).truncatedContinuationContext
      site payoff (fuel + 1)).value (bestLastPolicy reference mixed antichain who payoff fuel) := by
  classical
  rw [last.context_value_eq_expect _ site nonterminal payoff fuel alternative
      alternativeIntegrable,
    last.context_value_eq_expect _ site nonterminal payoff fuel
      (bestLastPolicy reference mixed antichain who payoff fuel) bestIntegrable,
    bestLastPolicy_at, expect_pure]
  exact expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ fun choice _ =>
    lastChoiceValue_le_best reference mixed antichain who payoff fuel site choice

end Finite

section Consistency

/-- When one player's policy cannot affect any decision-history reach
weight, replacing it preserves the reference Bayes beliefs. One common
fully mixed sequence witnesses consistency of the replaced profile. -/
theorem consistent_update_of_reach_invariant
    (reference : M.BehavioralAssessment) (mixed : reference.IsFullyMixed)
    (antichain : M.DecisionInformationAntichain) (who : ι)
    (reach : ∀ (alternative : M.BehavioralPolicy who) (player : ι)
      (site : M.InformationSite player) (history : M.InformationHistory player site.1),
      M.historyReachWeight
        (Profile.update (sig := M.behavioralSignature) reference.strategy who alternative)
          history.1 = M.historyReachWeight reference.strategy history.1)
    (policy : M.BehavioralPolicy who) :
    (⟨Profile.update (sig := M.behavioralSignature) reference.strategy who policy,
      (InformationModel.bayesAssessment _ reference.strategy mixed antichain).belief⟩ :
        M.BehavioralAssessment).IsSequentiallyConsistent antichain := by
  classical
  let weight (n : Nat) : ℝ := 1 / ((n : ℝ) + 1)
  have positive (n : Nat) : 0 < weight n := by dsimp [weight]; positivity
  have atMostOne (n : Nat) : weight n ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have vanishes : Tendsto weight atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let response (n : Nat) : M.BehavioralPolicy who := fun info =>
    mix (weight n) (positive n).le (atMostOne n)
      (reference.strategy who info) (policy info)
  let sequence (n : Nat) : M.BehavioralAssessment :=
    ⟨Profile.update (sig := M.behavioralSignature) reference.strategy who (response n),
      (InformationModel.bayesAssessment _ reference.strategy mixed antichain).belief⟩
  refine ⟨sequence, ?_, ?_⟩
  · intro n
    constructor
    · intro player site choice
      by_cases own : player = who
      · subst player
        change choice ∈ (Profile.update (sig := M.behavioralSignature)
          reference.strategy who (response n) who site.1).support
        rw [Profile.update_same]
        exact mem_support_mix_left _ _ _ (positive n) (mixed who site choice)
      · change choice ∈ (Profile.update (sig := M.behavioralSignature)
          reference.strategy who (response n) player site.1).support
        rw [Profile.update_of_ne _ _ own]
        exact mixed player site choice
    · intro player site _ history
      have mass : M.informationMass (sequence n).strategy player site =
          M.informationMass reference.strategy player site := by
        unfold informationMass
        exact tsum_congr fun next => reach (response n) player site next
      change (InformationModel.bayesAssessment _ reference.strategy mixed antichain).belief
        player site history = _
      rw [InformationModel.bayesAssessment, bayesBelief_apply, mass]
      exact congrArg (fun value => value / M.informationMass reference.strategy player site)
        (reach (response n) player site history).symm
  · constructor
    · intro player site
      by_cases own : player = who
      · subst player
        change PMFConvergesPointwise
          (fun n => Profile.update (sig := M.behavioralSignature)
            reference.strategy who (response n) who site.1)
          (Profile.update (sig := M.behavioralSignature)
            reference.strategy who policy who site.1)
        rw [pmfConvergesPointwise_iff_toReal]
        intro choice
        simp only [Profile.update_same]
        simp only [response, mix_apply_toReal]
        have first := vanishes.mul_const (((reference.strategy who site.1) choice).toReal)
        have one : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
        have second := (one.sub vanishes).mul_const (((policy site.1) choice).toReal)
        simpa only [zero_mul, sub_zero, one_mul, zero_add] using first.add second
      · change PMFConvergesPointwise
          (fun n => Profile.update (sig := M.behavioralSignature)
            reference.strategy who (response n) player site.1)
          (Profile.update (sig := M.behavioralSignature)
            reference.strategy who policy player site.1)
        simp only [Profile.update_of_ne _ _ own]
        exact pmfConvergesPointwise_const _
    · intro player site
      exact pmfConvergesPointwise_const _

/-- One final decision maker, with indifferent other participants, has a
sequential equilibrium whenever its policy does not change the reach law of
any decision site, its menus are finite, and each of its continuation
deviations has a finite expected payoff. The conclusion uses all
continuation-policy deviations. -/
theorem exists_sequential_equilibrium_of_last_decision
    (reference : M.BehavioralAssessment) (mixed : reference.IsFullyMixed)
    (antichain : M.DecisionInformationAntichain) (who : ι)
    [∀ site : M.InformationSite who, Finite (M.Choice who site.1)]
    (last : LastDecision (E := E) who)
    (nonterminal : ∀ site : M.InformationSite who, site.AllNonterminal)
    (reach : ∀ (alternative : M.BehavioralPolicy who) (player : ι)
      (site : M.InformationSite player) (history : M.InformationHistory player site.1),
      M.historyReachWeight
        (Profile.update (sig := M.behavioralSignature) reference.strategy who alternative)
          history.1 = M.historyReachWeight reference.strategy history.1)
    (payoff : ι → E.History → ℝ) (neutral : ∀ player, player ≠ who → payoff player = fun _ => 0)
    (fuel : Nat)
    (integrable : ∀ (site : M.InformationSite who) (alternative : M.BehavioralPolicy who),
      ((InformationModel.bayesAssessment _ reference.strategy mixed
          antichain).truncatedContinuationContext
        site (payoff who) (fuel + 1)).IntegrableAt alternative) :
    ∃ assessment : M.BehavioralAssessment,
      assessment.strategy = Profile.update (sig := M.behavioralSignature) reference.strategy who
        (bestLastPolicy reference mixed antichain who (payoff who) fuel) ∧
      assessment.IsSequentialEquilibriumFor antichain (fun player site =>
        assessment.truncatedContinuationContext site (payoff player) (fuel + 1)) := by
  classical
  let policy := bestLastPolicy reference mixed antichain who (payoff who) fuel
  let assessment : M.BehavioralAssessment :=
    ⟨Profile.update (sig := M.behavioralSignature) reference.strategy who policy,
      (InformationModel.bayesAssessment _ reference.strategy mixed antichain).belief⟩
  refine ⟨assessment, rfl, ?_,
    consistent_update_of_reach_invariant reference mixed antichain who reach policy⟩
  intro player site
  change (assessment.truncatedContinuationContext site (payoff player) (fuel + 1)).IsLocallyOptimal
    Set.univ (assessment.strategy player)
  by_cases own : player = who
  · subst player
    have overwrite (response : M.BehavioralPolicy who) :
        Profile.update (sig := M.behavioralSignature) assessment.strategy who response =
          Profile.update (sig := M.behavioralSignature) reference.strategy who response := by
      funext player
      by_cases same : player = who
      · subst player
        rw [Profile.update_same, Profile.update_same]
      · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]
        change Profile.update (sig := M.behavioralSignature)
          reference.strategy who policy player = _
        exact Profile.update_of_ne _ _ same
    have same : assessment.truncatedContinuationContext site (payoff who) (fuel + 1) =
        (InformationModel.bayesAssessment _ reference.strategy mixed
            antichain).truncatedContinuationContext
          site (payoff who) (fuel + 1) := by
      simp only [BehavioralAssessment.truncatedContinuationContext,
          BehavioralAssessment.continuationContextWith, overwrite]
      rfl
    have chosen : assessment.strategy who = policy := by
      change Profile.update (sig := M.behavioralSignature) reference.strategy who policy who = _
      exact Profile.update_same (sig := M.behavioralSignature) reference.strategy who policy
    rw [same, chosen]
    exact (Context.isLocallyOptimal_iff_of_integrable (integrable site policy)
      fun alternative _ => integrable site alternative).mpr fun alternative _ =>
        bestLastPolicy_optimal reference mixed antichain who (payoff who) fuel
          last site (nonterminal site) alternative (integrable site alternative)
          (integrable site policy)
  · have zero := neutral player own
    have constant (response : M.BehavioralPolicy player) :
        (assessment.truncatedContinuationContext site (payoff player) (fuel +
            1)).IntegrableAt response ∧
          (assessment.truncatedContinuationContext site (payoff player) (fuel +
              1)).value response = 0 := by
      simp only [Context.IntegrableAt, Context.value,
          BehavioralAssessment.truncatedContinuationContext,
          BehavioralAssessment.continuationContextWith,
        Context.ofBelief, zero, expect_constant]
      exact ⟨payoffIntegrable_constant _ 0, trivial⟩
    exact (Context.isLocallyOptimal_iff_of_integrable (constant _).1 fun alternative _ =>
        (constant alternative).1).mpr
      fun alternative _ => by rw [(constant alternative).2, (constant _).2]

end Consistency

end GameTheory.Protocol.InformationModel
