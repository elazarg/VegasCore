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
        apply FinDist.bind_congr
        intro draw _
        apply FinDist.bindOnSupport_congr
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
      history.trace running rfl, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro choice _
  rw [M.runBehavioralFrom_succ_of_not_terminal _ fuel running]
  apply FinDist.bind_congr
  intro draw _
  apply FinDist.bindOnSupport_congr
  intro target realized
  apply M.runBehavioralFrom_congr
  intro later reached _ player
  by_cases own : player = who
  · subst player
    rw [Profile.update_same, Profile.update_same]
    exact M.behavioral_eq_of_not_active _ _ later.trace
      (last history active draw.1 draw.2 target realized fuel later reached)
  · rw [Profile.update_of_ne _ _ own, Profile.update_of_ne _ _ own]

theorem LastDecision.context_value_eq_expect {who : ι} (last : LastDecision (E := E) who)
    (assessment : M.BehavioralAssessment) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who) (nonterminal : site.AllNonterminal)
    (payoff : E.History → ℝ) (fuel : Nat) (alternative : M.BehavioralPolicy who) :
    (assessment.continuationContext site payoff (fuel + 1)).value alternative =
      (alternative site.1).expect (fun choice =>
        (assessment.continuationContext site payoff (fuel + 1)).value
          ((assessment.strategy who).commit site.1 choice)) := by
  simp only [BehavioralAssessment.continuationContext_value, FinDist.expect_bind]
  calc
    _ = (assessment.belief who site).expect (fun history =>
          (alternative site.1).expect (fun choice =>
            (M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
              assessment.strategy who ((assessment.strategy who).commit site.1 choice))
                (fuel + 1) history.1).expect payoff)) := by
      apply FinDist.expect_congr
      intro history _
      rw [last.run_eq_bind_choices assessment.strategy alternative history.1
        site.1 history.2
        (nonterminal history) (InformationSite.active M site history) fuel, FinDist.expect_bind]
    _ = _ := FinDist.expect_comm _ _ _

section Finite

variable [∀ player (site : M.InformationSite player),
    Fintype (M.InformationHistory player site.1)]
  (reference : M.BehavioralAssessment) (mixed : reference.IsFullyMixed)
  (antichain : M.DecisionInformationAntichain) (who : ι)
  (payoff : E.History → ℝ) (fuel : Nat)

def lastChoiceValue (site : M.InformationSite who) (choice : M.Choice who site.1) : ℝ := by
  classical
  exact ((reference.bayes mixed antichain).continuationContext site payoff (fuel + 1)).value
    ((reference.strategy who).commit site.1 choice)

def bestLastChoice (site : M.InformationSite who) : M.Choice who site.1 := by
  classical
  let := mixed.finite_choice who site
  let : Nonempty (M.Choice who site.1) := ⟨(reference.strategy who site.1).support_nonempty.choose⟩
  exact Classical.choose (Finite.exists_max
    (lastChoiceValue reference mixed antichain who payoff fuel site))

theorem lastChoiceValue_le_best (site : M.InformationSite who) (choice : M.Choice who site.1) :
    lastChoiceValue reference mixed antichain who payoff fuel site choice ≤
      lastChoiceValue reference mixed antichain who payoff fuel site
        (bestLastChoice reference mixed antichain who payoff fuel site) := by
  classical
  let := mixed.finite_choice who site
  let : Nonempty (M.Choice who site.1) := ⟨(reference.strategy who site.1).support_nonempty.choose⟩
  exact Classical.choose_spec (Finite.exists_max
    (lastChoiceValue reference mixed antichain who payoff fuel site)) choice

def bestLastPolicy : M.BehavioralPolicy who := by
  classical
  exact fun info =>
    if decision : ∃ history : M.InformationHistory who info,
        ¬ E.terminal history.1.state ∧ ∃ action : E.Action who, some action ∈ M.menu who info
    then FinDist.pure (bestLastChoice reference mixed antichain who payoff fuel ⟨info, decision⟩)
    else reference.strategy who info

theorem bestLastPolicy_at (site : M.InformationSite who) :
    bestLastPolicy reference mixed antichain who payoff fuel site.1 =
      FinDist.pure (bestLastChoice reference mixed antichain who payoff fuel site) := by
  classical
  simp only [bestLastPolicy, dite_eq_left site.2]; rfl

theorem bestLastPolicy_optimal (last : LastDecision (E := E) who)
    (site : M.InformationSite who) (nonterminal : site.AllNonterminal)
    (alternative : M.BehavioralPolicy who) :
    ((reference.bayes mixed antichain).continuationContext site payoff (fuel + 1)).value
      alternative ≤
    ((reference.bayes mixed antichain).continuationContext site payoff (fuel + 1)).value
      (bestLastPolicy reference mixed antichain who payoff fuel) := by
  classical
  rw [last.context_value_eq_expect _ site nonterminal payoff fuel alternative,
    last.context_value_eq_expect _ site nonterminal payoff fuel
      (bestLastPolicy reference mixed antichain who payoff fuel),
    bestLastPolicy_at, FinDist.expect_pure]
  apply FinDist.expect_le_of_forall
  intro choice _
  exact lastChoiceValue_le_best reference mixed antichain who payoff fuel site choice

end Finite

section Consistency

variable [∀ player (site : M.InformationSite player),
    Fintype (M.InformationHistory player site.1)]

/-- When one player's policy cannot affect any decision-history reach
probability, replacing it preserves the reference Bayes beliefs. One common
fully mixed sequence witnesses consistency of the replaced profile. -/
theorem consistent_update_of_reach_invariant
    (reference : M.BehavioralAssessment) (mixed : reference.IsFullyMixed)
    (antichain : M.DecisionInformationAntichain) (who : ι)
    (reach : ∀ (alternative : M.BehavioralPolicy who) (player : ι)
      (site : M.InformationSite player) (history : M.InformationHistory player site.1),
      M.historyReachProbability
        (Profile.update (sig := M.behavioralSignature) reference.strategy who alternative)
          history.1 = M.historyReachProbability reference.strategy history.1)
    (policy : M.BehavioralPolicy who) :
    (⟨Profile.update (sig := M.behavioralSignature) reference.strategy who policy,
      (reference.bayes mixed antichain).belief⟩ : M.BehavioralAssessment).IsSequentiallyConsistent
        antichain := by
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
    FinDist.mix (weight n) (positive n).le (atMostOne n)
      (reference.strategy who info) (policy info)
  let sequence (n : Nat) : M.BehavioralAssessment :=
    ⟨Profile.update (sig := M.behavioralSignature) reference.strategy who (response n),
      (reference.bayes mixed antichain).belief⟩
  refine ⟨sequence, ?_, ?_⟩
  · intro n
    constructor
    · intro player site choice
      by_cases own : player = who
      · subst player
        change choice ∈ (Profile.update (sig := M.behavioralSignature)
          reference.strategy who (response n) who site.1).support
        rw [Profile.update_same]
        exact FinDist.mem_support_mix_left _ _ _ (positive n) (mixed who site choice)
      · change choice ∈ (Profile.update (sig := M.behavioralSignature)
          reference.strategy who (response n) player site.1).support
        rw [Profile.update_of_ne _ _ own]
        exact mixed player site choice
    · intro player site _ history
      have mass : M.informationMass (sequence n).strategy player site =
          M.informationMass reference.strategy player site := by
        unfold informationMass
        apply Finset.sum_congr rfl
        intro next _
        exact reach (response n) player site next
      change ((reference.bayes mixed antichain).belief player site).prob history = _
      rw [BehavioralAssessment.bayes, bayesBelief_prob, mass]
      exact congrArg (fun value => value / M.informationMass reference.strategy player site)
        (reach (response n) player site history).symm
  · constructor
    · intro player site
      by_cases own : player = who
      · subst player
        intro choice
        change Tendsto (fun n =>
          (Profile.update (sig := M.behavioralSignature)
            reference.strategy who (response n) who site.1).prob choice) atTop
          (nhds ((Profile.update (sig := M.behavioralSignature)
            reference.strategy who policy who site.1).prob choice))
        simp only [Profile.update_same]
        simp only [response, FinDist.prob_mix]
        have first := vanishes.mul_const ((reference.strategy who site.1).prob choice)
        have one : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
        have second := (one.sub vanishes).mul_const ((policy site.1).prob choice)
        simpa only [zero_mul, sub_zero, one_mul, zero_add] using first.add second
      · change FinDistConvergesPointwise
          (fun n => Profile.update (sig := M.behavioralSignature)
            reference.strategy who (response n) player site.1)
          (Profile.update (sig := M.behavioralSignature)
            reference.strategy who policy player site.1)
        simp only [Profile.update_of_ne _ _ own]
        exact finDistConvergesPointwise_const _
    · intro player site
      exact finDistConvergesPointwise_const _

/-- One final decision maker, with indifferent other participants, has a
sequential equilibrium whenever its policy does not change the reach law of
any decision site. The conclusion uses all continuation-policy deviations. -/
theorem exists_sequential_equilibrium_of_last_decision
    (reference : M.BehavioralAssessment) (mixed : reference.IsFullyMixed)
    (antichain : M.DecisionInformationAntichain) (who : ι)
    (last : LastDecision (E := E) who)
    (nonterminal : ∀ site : M.InformationSite who, site.AllNonterminal)
    (reach : ∀ (alternative : M.BehavioralPolicy who) (player : ι)
      (site : M.InformationSite player) (history : M.InformationHistory player site.1),
      M.historyReachProbability
        (Profile.update (sig := M.behavioralSignature) reference.strategy who alternative)
          history.1 = M.historyReachProbability reference.strategy history.1)
    (payoff : ι → E.History → ℝ) (neutral : ∀ player, player ≠ who → payoff player = fun _ => 0)
    (fuel : Nat) :
    ∃ assessment : M.BehavioralAssessment,
      assessment.strategy = Profile.update (sig := M.behavioralSignature) reference.strategy who
        (bestLastPolicy reference mixed antichain who (payoff who) fuel) ∧
      assessment.IsSequentialEquilibriumFor antichain (fun player site =>
        assessment.continuationContext site (payoff player) (fuel + 1)) := by
  classical
  let policy := bestLastPolicy reference mixed antichain who (payoff who) fuel
  let assessment : M.BehavioralAssessment :=
    ⟨Profile.update (sig := M.behavioralSignature) reference.strategy who policy,
      (reference.bayes mixed antichain).belief⟩
  refine ⟨assessment, rfl, ?_,
    consistent_update_of_reach_invariant reference mixed antichain who reach policy⟩
  intro player site alternative _
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
    have value (response : M.BehavioralPolicy who) :
        (assessment.continuationContext site (payoff who) (fuel + 1)).value response =
          ((reference.bayes mixed antichain).continuationContext
            site (payoff who) (fuel + 1)).value response := by
      simp only [BehavioralAssessment.continuationContext_value, overwrite]
      rfl
    change (assessment.continuationContext site (payoff who) (fuel + 1)).value alternative ≤ _
    rw [value, value]
    have chosen : assessment.strategy who = policy := by
      change Profile.update (sig := M.behavioralSignature) reference.strategy who policy who = _
      exact Profile.update_same (sig := M.behavioralSignature) reference.strategy who policy
    rw [chosen]
    exact bestLastPolicy_optimal reference mixed antichain who (payoff who) fuel last
      site (nonterminal site) alternative
  · have zero := neutral player own
    change (assessment.continuationContext site (payoff player) (fuel + 1)).value alternative ≤ _
    simp [BehavioralAssessment.continuationContext, Context.value, zero]

end Consistency

end GameTheory.Protocol.InformationModel
