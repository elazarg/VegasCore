/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Tremble
import GameTheoryExtensions.Protocol.FiniteInformation

/-! # Independent local trembles on finite decision plans

The laws here are distributions on existing decision tables. They introduce no
protocol actions or private-memory representation. Each decision coordinate is
randomized independently conditional on the prescribed plan.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {ι : Type*} {E : ExecutionProtocol ι} {M : InformationModel E} {who : ι}

instance InformationSite.choice_nonempty (site : M.InformationSite who) :
    Nonempty (M.Choice who site.1) := by
  obtain ⟨_history, _nonterminal, action, permitted⟩ := site.2
  exact ⟨⟨some action, permitted⟩⟩

/-- Every recorded own action was taken at a genuine legal decision site. -/
theorem exists_informationSite_of_mem_ownPlay {state : E.State} (trace : E.Trace state)
    {recorded : M.InfoState who × E.Action who} (member : recorded ∈ M.ownPlay who trace) :
    ∃ site : M.InformationSite who, site.1 = recorded.1 ∧
      some recorded.2 ∈ M.menu who site.1 := by
  induction trace with
  | start => simp only [InfoSignals.ownPlay, List.not_mem_nil] at member
  | @extend source target prior joint legal realized induction =>
    cases acted : joint who with
    | none =>
      simp only [InfoSignals.ownPlay, acted] at member
      exact induction member
    | some action =>
      simp only [InfoSignals.ownPlay, acted, List.mem_cons] at member
      rcases member with same | member
      · subst recorded
        have permitted : some action ∈ M.menu who (M.infoOf who prior) := by
          rw [← acted]
          exact (M.menu_adequate who prior (joint who)).mpr
            (E.legalOption_of_legal legal who)
        exact ⟨M.informationSite who ⟨source, prior⟩ action legal.1 permitted, rfl, permitted⟩
      · exact induction member

/-- A current decision site has not already occurred in its own-action record.
Equal constraints alone do not imply this: the proof uses perfect recall. -/
theorem InformationSite.not_mem_recordAt (recall : M.PerfectRecall)
    (site : M.InformationSite who) (action : E.Action who) :
    (site.1, action) ∉ M.recordAt who site.1 := by
  obtain ⟨history, nonterminal, _witness, _permitted⟩ := site.2
  obtain ⟨joint, legal⟩ := E.exists_legal nonterminal
  obtain ⟨chosen, acted⟩ := (E.legalOption_of_legal legal who).exists_eq_some_of_active
    (joint who) (InformationSite.active M site history)
  obtain ⟨next, realized⟩ := (E.step history.1.state ⟨joint, legal⟩).support_nonempty
  let extended : E.Trace next := .extend history.1.trace joint legal realized
  have noRepeat := InfoSignals.PerfectRecall.actsOnceAtEachInfoState
    M.toInfoSignals recall who extended
  simp only [extended, InfoSignals.actedAt, acted, List.nodup_cons] at noRepeat
  rw [← history.2, M.recordAt_eq_ownPlay recall who history.1]
  intro member
  exact noRepeat.1 (by
    rw [M.actedAt_eq_map_ownPlay]
    exact List.mem_map.mpr ⟨_, member, rfl⟩)

/-- The choices at a table coordinate compatible with the player's remembered
actions before reaching the supplied information site. -/
def InformationSite.recordChoices (current site : M.InformationSite who) :
    Set (M.Choice who site.1) :=
  {choice | ∀ recorded ∈ M.recordAt who current.1,
    recorded.1 = site.1 → choice.1 = some recorded.2}

theorem InformationSite.recordChoices_self (recall : M.PerfectRecall)
    (current : M.InformationSite who) : current.recordChoices current = Set.univ := by
  ext choice
  simp only [InformationSite.recordChoices, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  intro recorded member same
  exact (current.not_mem_recordAt recall recorded.2 (same ▸ member)).elim

/-- Perfect recall makes the past restrictions jointly satisfiable: no table
coordinate is required to record two different own actions. -/
theorem InformationSite.recordChoices_nonempty (recall : M.PerfectRecall)
    (current site : M.InformationSite who) : (current.recordChoices site).Nonempty := by
  classical
  obtain ⟨history, _nonterminal, _action, _permitted⟩ := current.2
  have record : M.recordAt who current.1 = M.ownPlay who history.1.trace := by
    exact (congrArg (M.recordAt who) history.2).symm.trans
      (M.recordAt_eq_ownPlay recall who history.1)
  have noRepeat : ((M.recordAt who current.1).map Prod.fst).Nodup := by
    rw [record, ← M.actedAt_eq_map_ownPlay]
    exact InfoSignals.PerfectRecall.actsOnceAtEachInfoState M.toInfoSignals recall who _
  by_cases visited : ∃ recorded ∈ M.recordAt who current.1, recorded.1 = site.1
  · obtain ⟨recorded, member, same⟩ := visited
    have past : recorded ∈ M.ownPlay who history.1.trace := record ▸ member
    obtain ⟨earlier, earlierSame, permitted⟩ :=
      M.exists_informationSite_of_mem_ownPlay history.1.trace past
    have legal : some recorded.2 ∈ M.menu who site.1 := by
      simpa only [earlierSame, same] using permitted
    refine ⟨⟨some recorded.2, legal⟩, ?_⟩
    intro other otherMember otherSame
    have equal := List.inj_on_of_nodup_map noRepeat otherMember member
      (otherSame.trans same.symm)
    exact congrArg (fun pair : M.InfoState who × E.Action who => some pair.2) equal.symm
  · refine ⟨Classical.choice (inferInstance : Nonempty (M.Choice who site.1)), ?_⟩
    intro recorded member same
    exact (visited ⟨recorded, member, same⟩).elim

/-- Extending a decision table preserves exactly the existing mixed-policy
compatibility event used by the behavioral realization construction. -/
theorem DecisionPlan.consistentAt_extend_iff (recall : M.PerfectRecall)
    (plan : M.DecisionPlan who) (fallback : M.Policy who)
    (current : M.InformationSite who) :
    plan.extend fallback ∈ M.ConsistentAt who current.1 ↔
      ∀ site, plan site ∈ current.recordChoices site := by
  constructor
  · intro compatible site recorded member same
    have agreement := compatible recorded member
    rw [same, DecisionPlan.extend_site] at agreement
    exact agreement
  · intro compatible recorded member
    obtain ⟨history, _nonterminal, _action, _permitted⟩ := current.2
    have past : recorded ∈ M.ownPlay who history.1.trace := by
      simpa only [← history.2, M.recordAt_eq_ownPlay recall who history.1] using member
    obtain ⟨site, same, _permitted⟩ :=
      M.exists_informationSite_of_mem_ownPlay history.1.trace past
    rw [← same, DecisionPlan.extend_site]
    exact compatible site recorded member same.symm

variable [Fintype (M.InformationSite who)]
  [∀ site : M.InformationSite who, Fintype (M.Choice who site.1)]

/-- Independently reserve epsilon mass for every legal choice at every
decision site of the prescribed plan. -/
def DecisionPlan.tremble (plan : M.DecisionPlan who) (epsilon : ℝ)
    (nonnegative : 0 ≤ epsilon)
    (small : ∀ site : M.InformationSite who,
      epsilon * Fintype.card (M.Choice who site.1) ≤ 1) : FinDist (M.DecisionPlan who) :=
  FinDist.pi fun site => (FinDist.pure (plan site)).tremble epsilon nonnegative (small site)

/-- The current local law is the prescribed choice with its own independent
uniform tremble. This statement precedes any conditioning on past choices. -/
theorem DecisionPlan.tremble_marginal (plan : M.DecisionPlan who) (epsilon : ℝ)
    (nonnegative : 0 ≤ epsilon)
    (small : ∀ site : M.InformationSite who,
      epsilon * Fintype.card (M.Choice who site.1) ≤ 1)
    (site : M.InformationSite who) :
    (plan.tremble epsilon nonnegative small).map (fun realized => realized site) =
      (FinDist.pure (plan site)).tremble epsilon nonnegative (small site) := by
  classical
  exact FinDist.map_apply_pi site _

theorem DecisionPlan.mem_support_tremble (plan : M.DecisionPlan who) (epsilon : ℝ)
    (positive : 0 < epsilon)
    (small : ∀ site : M.InformationSite who,
      epsilon * Fintype.card (M.Choice who site.1) ≤ 1)
    (realized : M.DecisionPlan who) :
    realized ∈ (plan.tremble epsilon positive.le small).support := by
  apply FinDist.mem_support_pi.mpr
  intro site
  apply FinDist.prob_pos_iff.mp
  exact positive.trans_le
    (FinDist.le_prob_tremble _ epsilon positive.le (small site) (realized site))

/-- Mix prescribed finite plans, independently tremble their decision
coordinates, and extend the realized table to the existing pure-policy carrier. -/
def trembledMixedPolicy (plans : FinDist (M.DecisionPlan who)) (epsilon : ℝ)
    (nonnegative : 0 ≤ epsilon)
    (small : ∀ site : M.InformationSite who,
      epsilon * Fintype.card (M.Choice who site.1) ≤ 1)
    (fallback : M.Policy who) : M.MixedPolicy who :=
  (plans.bind fun plan => plan.tremble epsilon nonnegative small).map
    (fun plan => plan.extend fallback)

/-- Every legal decision record has positive compatible mass under positive
local trembles, regardless of correlations in the prescribed-plan law. -/
theorem trembledMixedPolicy_consistent (recall : M.PerfectRecall)
    (plans : FinDist (M.DecisionPlan who)) (epsilon : ℝ) (positive : 0 < epsilon)
    (small : ∀ site : M.InformationSite who,
      epsilon * Fintype.card (M.Choice who site.1) ≤ 1)
    (fallback : M.Policy who) (current : M.InformationSite who) :
    ∃ policy ∈ M.ConsistentAt who current.1,
      policy ∈ (trembledMixedPolicy plans epsilon positive.le small fallback).support := by
  classical
  let realized : M.DecisionPlan who := fun site =>
    (current.recordChoices_nonempty recall site).choose
  have compatible : ∀ site, realized site ∈ current.recordChoices site :=
    fun site => (current.recordChoices_nonempty recall site).choose_spec
  obtain ⟨prescribed, supported⟩ := plans.support_nonempty
  refine ⟨realized.extend fallback,
    (realized.consistentAt_extend_iff recall fallback current).mpr compatible, ?_⟩
  rw [trembledMixedPolicy, FinDist.support_map]
  refine ⟨realized, ?_, rfl⟩
  rw [FinDist.support_bind]
  exact Set.mem_iUnion₂.mpr
    ⟨prescribed, supported, prescribed.mem_support_tremble epsilon positive small realized⟩

/-- The existing mixed-to-behavioral realization retains epsilon at every
decision choice. Perfect recall supplies both record satisfiability and the
fact that the current coordinate has not been conditioned on already. -/
theorem le_prob_trembledMixedPolicy_toBehavioralWith (recall : M.PerfectRecall)
    (plans : FinDist (M.DecisionPlan who)) (epsilon : ℝ) (positive : 0 < epsilon)
    (small : ∀ site : M.InformationSite who,
      epsilon * Fintype.card (M.Choice who site.1) ≤ 1)
    (fallback : M.Policy who) (current : M.InformationSite who)
    (action : M.Choice who current.1) :
    epsilon ≤ ((trembledMixedPolicy plans epsilon positive.le small fallback).toBehavioralWith
      fallback current.1).prob action := by
  classical
  let law := plans.bind fun plan => plan.tremble epsilon positive.le small
  let extend : M.DecisionPlan who → M.Policy who := fun plan => plan.extend fallback
  let event : Set (M.DecisionPlan who) :=
    {plan | ∀ site, plan site ∈ current.recordChoices site}
  have event_eq : extend ⁻¹' M.ConsistentAt who current.1 = event := by
    ext plan
    exact plan.consistentAt_extend_iff recall fallback current
  have answer_eq : extend ⁻¹' (fun policy : M.Policy who => policy current.1) ⁻¹' {action} =
      (fun plan : M.DecisionPlan who => plan current) ⁻¹' {action} := by
    ext plan
    simp [extend]
  have supported := trembledMixedPolicy_consistent recall plans epsilon positive small
    fallback current
  have table_positive : ∃ plan ∈ event, plan ∈ law.support := by
    obtain ⟨policy, compatible, present⟩ := supported
    rw [trembledMixedPolicy, FinDist.support_map] at present
    obtain ⟨plan, present, rfl⟩ := present
    refine ⟨plan, ?_, present⟩
    exact (plan.consistentAt_extend_iff recall fallback current).mp compatible
  have lower := FinDist.le_prob_condOn_mixture_pi plans
    (fun plan site => (FinDist.pure (plan site)).tremble epsilon positive.le (small site))
    current.recordChoices current (current.recordChoices_self recall) action epsilon
    (fun plan _ => FinDist.le_prob_tremble _ epsilon positive.le (small current) action)
    table_positive
  rw [FinDist.prob_map_eq_probOf_preimage_singleton,
    FinDist.probOf_condOn_eq_inter] at lower
  change epsilon ≤ (MixedPolicy.toBehavioralWith (M := M)
    (law.map extend) fallback current.1).prob action
  change ∃ policy ∈ M.ConsistentAt who current.1,
    policy ∈ (law.map extend).support at supported
  rw [MixedPolicy.toBehavioralWith, dite_eq_left supported,
    FinDist.prob_map_eq_probOf_preimage_singleton, FinDist.probOf_condOn_eq_inter,
    FinDist.probOf_map, FinDist.probOf_map, Set.preimage_inter, event_eq, answer_eq]
  exact lower

/-- Independent residual prescriptions for a behavioral table with a uniform
probability floor. -/
def BehavioralDecisionPlan.residualPlans (policy : M.BehavioralDecisionPlan who)
    (epsilon : ℝ)
    (small : ∀ site : M.InformationSite who,
      epsilon * Fintype.card (M.Choice who site.1) < 1)
    (floor : ∀ site (choice : M.Choice who site.1), epsilon ≤ (policy site).prob choice) :
    FinDist (M.DecisionPlan who) :=
  FinDist.pi fun site => (policy site).removeTremble epsilon (small site) (floor site)

/-- Independent residual plans followed by independent local trembles recover
the exact product law of the original behavioral choices. -/
theorem BehavioralDecisionPlan.residualPlans_tremble (policy : M.BehavioralDecisionPlan who)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon)
    (small : ∀ site : M.InformationSite who,
      epsilon * Fintype.card (M.Choice who site.1) < 1)
    (floor : ∀ site (choice : M.Choice who site.1), epsilon ≤ (policy site).prob choice) :
    (policy.residualPlans epsilon small floor).bind
        (fun plan => plan.tremble epsilon nonnegative (fun site => (small site).le)) =
      FinDist.pi policy := by
  exact (FinDist.pi_bind
    (fun site : M.InformationSite who =>
      (policy site).removeTremble epsilon (small site) (floor site))
    (fun (site : M.InformationSite who) (choice : M.Choice who site.1) =>
      (FinDist.pure choice).tremble epsilon nonnegative (small site).le)).trans
    (congrArg FinDist.pi (funext fun site =>
      (FinDist.bind_tremble_pure _ epsilon nonnegative (small site).le).trans
        (FinDist.tremble_removeTremble _ epsilon nonnegative (small site) (floor site))))

end GameTheory.Protocol.InformationModel
