/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.BehavioralAssessment

/-! # Finite decision information

Finite legal histories imply finite decision sites. The ambient information
carrier may remain infinite: unreachable information values are irrelevant.
-/

noncomputable section

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

/-- Every active player at a nonterminal legal history is at a decision site. -/
theorem exists_informationSite_of_active (who : ι) (history : E.History)
    (nonterminal : ¬ E.terminal history.state) (active : E.active history.state who) :
    ∃ site : M.InformationSite who, site.1 = M.infoOf who history.trace := by
  obtain ⟨joint, legal⟩ := E.exists_legal nonterminal
  obtain ⟨action, same⟩ :=
    (E.legalOption_of_legal legal who).exists_eq_some_of_active (joint who) active
  have permitted : some action ∈ M.menu who (M.infoOf who history.trace) := by
    rw [← same]
    exact (M.menu_adequate who history.trace (joint who)).mpr
      (E.legalOption_of_legal legal who)
  exact ⟨M.informationSite who history action nonterminal permitted, rfl⟩

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
  simp only [DecisionPlan.extend, dite_eq_left site.2]
  rfl

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
  (site : M.InformationSite who) → FinDist (M.Choice who site.1)

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
  simp only [BehavioralDecisionPlan.extend, dite_eq_left site.2]
  rfl

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
