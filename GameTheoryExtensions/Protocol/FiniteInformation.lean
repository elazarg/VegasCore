/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.BehavioralAssessment
import GameTheory.Protocol.DecisionRecall

/-! # Finite decision information

Finite legal histories imply finite decision sites, finite menus at each of
them, and finitely many outcomes of every reachable transition. The ambient
information carrier may remain infinite: unreachable information values are
irrelevant.
-/

noncomputable section

namespace GameTheory.Protocol.ExecutionProtocol

variable {ι : Type*} (E : ExecutionProtocol ι)

/-- Every legal transition from a nonterminal history has finitely many
outcomes. Transitions from states no history reaches are unconstrained. -/
def FiniteTransitions : Prop :=
  ∀ history : E.History, ¬ E.terminal history.state →
    ∀ draw : { joint : ∀ i, Option (E.Action i) // E.Legal history.state joint },
      (E.step history.state draw).support.Finite

/-- Finitely many legal histories bound every reachable transition: distinct
outcomes of one transition extend its history to distinct histories. -/
theorem FiniteTransitions.of_finite_history [Finite E.History] : E.FiniteTransitions := by
  intro history _ draw
  let extend (target : (E.step history.state draw).support) : E.History :=
    history.extend draw.2 target.2
  have injective : Function.Injective extend := fun first second same =>
    Subtype.ext (congrArg ExecutionProtocol.History.state same)
  exact Set.finite_coe_iff.mp (Finite.of_injective extend injective)

end GameTheory.Protocol.ExecutionProtocol

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {ι : Type*} {E : ExecutionProtocol ι} {M : InformationModel E}

instance InformationSite.finite [Finite E.History] (who : ι) :
    Finite (M.InformationSite who) := by
  let witness (site : M.InformationSite who) : E.History := site.2.choose.1
  apply Finite.of_injective witness
  intro first second same
  apply Subtype.ext
  exact first.2.choose.2.symm.trans
    ((congrArg (fun history : E.History => M.infoOf who history.trace) same).trans
      second.2.choose.2)

/-- The last joint action recorded by a history, if any. -/
private def lastJoint : E.History → Option (∀ i, Option (E.Action i))
  | ⟨_, .start⟩ => none
  | ⟨_, .extend _ joint _ _⟩ => some joint

/-- Finitely many legal histories allow only finitely many legal choices at a
decision site: distinct choices extend one site history to distinct histories. -/
instance InformationSite.finite_choice [Finite E.History] (who : ι)
    (site : M.InformationSite who) : Finite (M.Choice who site.1) := by
  classical
  obtain ⟨history, running, _⟩ := site.2
  obtain ⟨base, baseLegal⟩ := E.exists_legal running
  let joint (choice : M.Choice who site.1) : ∀ player, Option (E.Action player) :=
    Function.update base who choice.1
  have legal (choice : M.Choice who site.1) : E.Legal history.1.state (joint choice) := by
    apply E.legal_of_legalOption running
    intro player
    by_cases same : player = who
    · subst player
      simp only [joint, Function.update_self]
      apply (M.menu_adequate _ history.1.trace choice.1).mp
      rw [history.2]
      exact choice.2
    · simp only [joint, Function.update_of_ne same]
      exact E.legalOption_of_legal baseLegal player
  let extend (choice : M.Choice who site.1) : E.History :=
    history.1.extend (legal choice)
      (E.step history.1.state ⟨joint choice, legal choice⟩).support_nonempty.choose_spec
  apply Finite.of_injective extend
  intro first second same
  have joints := congrArg lastJoint same
  simp only [extend, ExecutionProtocol.History.extend, lastJoint, Option.some.injEq] at joints
  apply Subtype.ext
  simpa only [joint, Function.update_self] using congrFun joints who

/-- A pure plan records only legal decision sites, retaining each site's menu. -/
abbrev DecisionPlan (who : ι) :=
  (site : M.InformationSite who) → M.Choice who site.1

instance DecisionPlan.finite (who : ι) [Finite E.History]
    [∀ site : M.InformationSite who, Finite (M.Choice who site.1)] :
    Finite (M.DecisionPlan who) := by
  unfold DecisionPlan
  infer_instance

/-- Restrict an existing policy to the decision sites it can encounter. -/
def Policy.restrictToDecisions {who : ι} (policy : M.Policy who) : M.DecisionPlan who :=
  fun site => policy site.1

/-- Extend a finite decision table using a legal fallback at other information
values. The fallback need not agree with the table. -/
def DecisionPlan.extend {who : ι} (plan : M.DecisionPlan who)
    (fallback : M.Policy who) : M.Policy who := by
  classical
  exact fun info =>
    if available : ∃ history : M.InformationHistory who info,
        ¬ E.terminal history.1.state ∧
          ∃ action : E.Action who, some action ∈ M.menu who info then
      plan ⟨info, available⟩
    else fallback info

@[simp]
theorem DecisionPlan.extend_site {who : ι} (plan : M.DecisionPlan who)
    (fallback : M.Policy who) (site : M.InformationSite who) :
    plan.extend fallback site.1 = plan site := by
  unfold DecisionPlan.extend
  split
  · rfl
  · rename_i unavailable
    exact absurd site.2 unavailable

@[simp]
theorem DecisionPlan.restrict_extend {who : ι} (plan : M.DecisionPlan who)
    (fallback : M.Policy who) :
    (plan.extend fallback).restrictToDecisions = plan := by
  funext site
  exact plan.extend_site fallback site

/-- Restriction followed by extension preserves every choice execution can
consult, including the uniquely determined choice of an inactive player. -/
theorem Policy.extend_restrict_at_history {who : ι} (policy fallback : M.Policy who)
    (history : E.History) (nonterminal : ¬ E.terminal history.state) :
    policy.restrictToDecisions.extend fallback (M.infoOf who history.trace) =
      policy (M.infoOf who history.trace) := by
  classical
  by_cases active : E.active history.state who
  · obtain ⟨site, same⟩ := M.exists_informationSite_of_active who history nonterminal active
    rw [← same, DecisionPlan.extend_site]
    rfl
  · have := M.subsingleton_choice_of_not_active history.trace active
    exact Subsingleton.elim _ _

/-- Finite decision tables preserve the complete history law from every legal
continuation, independently of the chosen fallback policies. -/
theorem runFrom_extend_restrict (policies fallback : (who : ι) → M.Policy who)
    (fuel : ℕ) (history : E.History) :
    M.runFrom (fun who => (policies who).restrictToDecisions.extend (fallback who))
        fuel history = M.runFrom policies fuel history := by
  apply M.runFrom_congr_of_act_eq fuel history
  intro later _ nonterminal who
  exact congrArg Subtype.val
    ((policies who).extend_restrict_at_history (fallback who) later nonterminal)

/-- Local randomization over the same finite decision table. -/
abbrev BehavioralDecisionPlan (who : ι) :=
  (site : M.InformationSite who) → PMF (M.Choice who site.1)

/-- Restrict an existing behavioral policy to its legal decision sites. -/
def BehavioralPolicy.restrictToDecisions {who : ι} (policy : M.BehavioralPolicy who) :
    M.BehavioralDecisionPlan who := fun site => policy site.1

/-- Extend a local randomized decision table using a behavioral fallback. -/
def BehavioralDecisionPlan.extend {who : ι} (plan : M.BehavioralDecisionPlan who)
    (fallback : M.BehavioralPolicy who) : M.BehavioralPolicy who := by
  classical
  exact fun info =>
    if available : ∃ history : M.InformationHistory who info,
        ¬ E.terminal history.1.state ∧
          ∃ action : E.Action who, some action ∈ M.menu who info then
      plan ⟨info, available⟩
    else fallback info

@[simp]
theorem BehavioralDecisionPlan.extend_site {who : ι} (plan : M.BehavioralDecisionPlan who)
    (fallback : M.BehavioralPolicy who) (site : M.InformationSite who) :
    plan.extend fallback site.1 = plan site := by
  unfold BehavioralDecisionPlan.extend
  split
  · rfl
  · rename_i unavailable
    exact absurd site.2 unavailable

@[simp]
theorem BehavioralDecisionPlan.restrict_extend {who : ι}
    (plan : M.BehavioralDecisionPlan who) (fallback : M.BehavioralPolicy who) :
    (plan.extend fallback).restrictToDecisions = plan := by
  funext site
  exact plan.extend_site fallback site

/-- Behavioral restriction and extension preserve every law at a nonterminal
legal history; inactivity makes the fallback law unique there. -/
theorem BehavioralPolicy.extend_restrict_at_history {who : ι}
    (policy fallback : M.BehavioralPolicy who)
    (history : E.History) (nonterminal : ¬ E.terminal history.state) :
    policy.restrictToDecisions.extend fallback (M.infoOf who history.trace) =
      policy (M.infoOf who history.trace) := by
  classical
  by_cases active : E.active history.state who
  · obtain ⟨site, same⟩ := M.exists_informationSite_of_active who history nonterminal active
    rw [← same, BehavioralDecisionPlan.extend_site]
    rfl
  · exact M.behavioral_eq_of_not_active _ _ history.trace active

/-- Behavioral decision tables preserve every complete continuation law. -/
theorem runBehavioralFrom_extend_restrict [Fintype ι]
    (policies fallback : (who : ι) → M.BehavioralPolicy who)
    (fuel : ℕ) (history : E.History) :
    M.runBehavioralFrom
        (fun who => (policies who).restrictToDecisions.extend (fallback who)) fuel history =
      M.runBehavioralFrom policies fuel history := by
  apply M.runBehavioralFrom_congr fuel history
  intro later _ nonterminal who
  exact (policies who).extend_restrict_at_history (fallback who) later nonterminal

end GameTheory.Protocol.InformationModel
