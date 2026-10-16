/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryContinuingProbability
import Vegas.Game.CommitRecoveryValuePlan
import GameTheoryExtensions.Analysis.Protocol.SingleMoverReach

/-! # Opening-choice factors along genuine source recovery histories -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem nonfailure_noncommit_unique (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (view : ProtocolView who program)
      (_notCommit : ProtocolView.atCommit who program view = false)
      (first second : OwnAction Player L),
      first ∈ ProtocolView.available who program (CommitmentInterface.forfeiture program) view →
      second ∈ ProtocolView.available who program (CommitmentInterface.forfeiture program) view →
      ¬ first.IsFailure → ¬ second.IsFailure → first = second
 := by
  intro Γ O program
  induction program with
  | ret payoffs => intro view notCommit first second left; exact left.elim
  | sample name fresh law next ih =>
      intro view notCommit first second left right lf rf
      cases view with
      | inl _ => exact left.elim
      | inr view => exact ih view notCommit first second left right lf rf
  | commit name owner fresh guard next ih =>
      intro view notCommit first second left right lf rf
      cases view with
      | inl _ => cases notCommit
      | inr view => exact ih view notCommit first second left right lf rf
  | reveal published owner name fresh source unresolved next ih =>
      intro view notCommit first second left right lf rf
      cases view with
      | inl _ =>
          obtain ⟨leftFlag, rfl⟩ := left
          obtain ⟨rightFlag, rfl⟩ := right
          have leftTrue : leftFlag = true := by
            cases leftFlag <;> simp_all only [OwnAction.IsFailure, not_true_eq_false]
          have rightTrue : rightFlag = true := by
            cases rightFlag <;> simp_all only [OwnAction.IsFailure, not_true_eq_false]
          rw [leftTrue, rightTrue]
      | inr view => exact ih view notCommit first second left right lf rf

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

private theorem continuing_noncommit_unique (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (notCommit : info.1.1.1.elim false (ProtocolView.atCommit who setup.program) = false)
    (first second : setup.commitRecoveryModel.Choice who info)
    (left : setup.CommitRecoveryContinues who info first.val)
    (right : setup.CommitRecoveryContinues who info second.val) : first = second := by
  apply Subtype.ext
  have firstLegal := first.property
  have secondLegal := second.property
  cases firstEq : first.val with
  | none =>
      cases secondEq : second.val with
      | none => rfl
      | some second =>
          rw [firstEq] at firstLegal
          change ¬ setup.commitRecoveryActive who info.1.1 at firstLegal
          rw [secondEq] at secondLegal
          change setup.commitRecoveryMenu who info (some second) at secondLegal
          exact (firstLegal secondLegal.1).elim
  | some first =>
      cases secondEq : second.val with
      | none =>
          rw [secondEq] at secondLegal
          rw [firstEq] at firstLegal
          exact (secondLegal firstLegal.1).elim
      | some second =>
          rw [firstEq] at firstLegal
          rw [secondEq] at secondLegal
          have leftFacts := left first firstEq
          have rightFacts := right second secondEq
          have actions : first.action = second.action := by
            cases viewed : info.1.1.1 with
            | none => simpa only [viewed, Option.elim_none] using firstLegal.2
            | some view =>
                apply nonfailure_noncommit_unique who setup.program view
                  (by simpa only [viewed, Option.elim_some] using notCommit)
                  first.action second.action
                · have offered : first ∈ ProtocolView.recoveryAvailable who setup.program
                      view := by simpa only [viewed, Option.elim_some] using firstLegal.2
                  exact offered.1
                · have offered : second ∈ ProtocolView.recoveryAvailable who setup.program
                      view := by simpa only [viewed, Option.elim_some] using secondLegal.2
                  exact offered.1
                · exact leftFacts.2 notCommit
                · exact rightFacts.2 notCommit
          have same : first = second := by
            cases first
            cases second
            simp_all only
          exact congrArg some same

variable [Fintype Player] (wellFormed : setup.WellFormed)
  (reference target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    reference target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)

open Classical in
/-- Outside binding instructions the continuing source choice is unique.
Its actual approximant atom is at least one minus the original source tremble. -/
theorem commitRecovery_noncommit_choice_lower
    (n : Nat) (who : Player) (site : setup.commitRecoveryModel.InformationSite who)
    (notCommit : site.1.1.1.1.elim false (ProtocolView.atCommit who setup.program) = false)
    (chosen : setup.commitRecoveryModel.Choice who site.1)
    (continues : setup.CommitRecoveryContinues who site.1 chosen.val) :
    1 - approximation.epsilon n ≤
      ((approximation.sequence n).strategy who site.1 chosen).toReal := by
  let law := (approximation.sequence n).strategy who site.1
  have event : (law.map (fun choice =>
      decide (setup.CommitRecoveryContinues who site.1 choice.val))) true = law chosen := by
    rw [PMF.map_apply]
    have unique (choice : setup.commitRecoveryModel.Choice who site.1) :
        true = decide (setup.CommitRecoveryContinues who site.1 choice.val) ↔ choice = chosen := by
      constructor
      · intro accepted
        have continuing : setup.CommitRecoveryContinues who site.1 choice.val := by
          exact of_decide_eq_true accepted.symm
        exact continuing_noncommit_unique setup who site.1 notCommit choice chosen
          continuing continues
      · rintro rfl
        simp only [continues, decide_true]
    simp only [unique, tsum_ite_eq]
  rw [← event, setup.commitRecovery_approximation_continuing_law wellFormed reference target
    approximation n who site, mix_apply_toReal, toReal_pure_apply]
  simp only [↓reduceIte, mul_one]
  exact le_add_of_nonneg_left (mul_nonneg (approximation.positive n).le ENNReal.toReal_nonneg)

open Classical in
/-- The actual selected atom at any clear source nonbinding step has the
same lower bound, including inactive owners. No intendedness is required. -/
theorem commitRecovery_clear_noncommit_atom_lower
    (n : Nat) {before after : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace before)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal before joint)
    (reached : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support)
    (clear : setup.CommitRecoveryClear after)
    (notCommit : before.elim false (fun current =>
      ProtocolState.atCommit setup.program current.point) = false) (who : Player) :
    1 - approximation.epsilon n ≤
      ((approximation.sequence n).strategy who (setup.commitRecoveryModel.infoOf who prior)
        (setup.commitRecoveryModel.choicesOfLegal prior ⟨joint, legal⟩ who)).toReal := by
  cases chosen : joint who with
  | none =>
      rw [setup.commitRecoveryModel.choicesOfLegal_mass_eq_one_of_none
        (approximation.sequence n).strategy prior ⟨joint, legal⟩ chosen]
      linarith [(approximation.positive n).le]
  | some action =>
      let choice := setup.commitRecoveryModel.choicesOfLegal prior ⟨joint, legal⟩ who
      have offered : some action ∈ setup.commitRecoveryModel.menu who
          (setup.commitRecoveryModel.infoOf who prior) := by
        have permitted := choice.property
        change joint who ∈ _ at permitted
        rwa [chosen] at permitted
      let site : setup.commitRecoveryModel.InformationSite who :=
        ⟨setup.commitRecoveryModel.infoOf who prior, ⟨⟨before, prior⟩, rfl⟩, legal.1,
          action, offered⟩
      have continues : setup.CommitRecoveryContinues who site.1 choice.val := by
        by_contra denied
        have excluded := setup.commitRecovery_voluntaryFailure_step who prior choice denied
          joint legal rfl after reached
        cases after with
        | none => simp only [commitRecoveryPublic, Finset.notMem_empty] at excluded
        | some after =>
            change after.excluded = ∅ at clear
            simp only [commitRecoveryPublic, clear, Finset.notMem_empty] at excluded
      exact setup.commitRecovery_noncommit_choice_lower wellFormed reference target approximation
        n who site (by rw [setup.commitRecovery_atCommit_info who prior]; exact notCommit)
          choice continues

/-- The actual nonbinding source-choice factors. Chance atoms, binding choices,
and accepted unusable bindings are not included in this scalar. -/
def commitRecoveryOpeningFactor
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
    ∀ {state : setup.commitRecoveryProtocol.State},
      setup.commitRecoveryProtocol.Trace state → ℝ
  | _, .start => 1
  | _, .extend (source := source) prior joint legal _ =>
      commitRecoveryOpeningFactor profile prior *
        if source.elim false (fun current =>
            ProtocolState.atCommit setup.program current.point) then 1 else
          ∏ who, (profile who (setup.commitRecoveryModel.infoOf who prior)
            (setup.commitRecoveryModel.choicesOfLegal prior ⟨joint, legal⟩ who)).toReal

/-- The source binding-choice product and the actual source transition atoms,
on the SAME genuine trace. This is a scalar history weight, not a continuation
runner or a newly sampled entry. -/
def commitRecoveryBindingContent
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
    ∀ {state : setup.commitRecoveryProtocol.State},
      setup.commitRecoveryProtocol.Trace state → ℝ
  | _, .start => 1
  | target, .extend (source := source) prior joint legal _ =>
      commitRecoveryBindingContent profile prior *
        (if source.elim false (fun current =>
            ProtocolState.atCommit setup.program current.point) then
          ∏ who, (profile who (setup.commitRecoveryModel.infoOf who prior)
            (setup.commitRecoveryModel.choicesOfLegal prior ⟨joint, legal⟩ who)).toReal else 1) *
        ((setup.commitRecoveryProtocol.step source ⟨joint, legal⟩) target).toReal

/-- Exact source reach retains its original reveal-TRUE factors separately
from binding content and nature. Every original trace instruction is retained. -/
theorem commitRecovery_source_content_density
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
    ∀ {state : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace state),
      (setup.commitRecoveryModel.historyReachWeight profile ⟨state, trace⟩).toReal =
        setup.commitRecoveryOpeningFactor profile trace *
          setup.commitRecoveryBindingContent profile trace
  | _, .start => by simp [commitRecoveryOpeningFactor, commitRecoveryBindingContent,
      InformationModel.historyReachWeight, InformationModel.runBehavioral,
      InformationModel.runBehavioralFrom, Trace.length,
      ExecutionProtocol.runRandomizedFor_zero, PMF.pure_apply, ExecutionProtocol.initHistory]
  | _, .extend prior joint legal reached => by
      rw [setup.commitRecoveryModel.historyReachProbability_extend,
        commitRecovery_source_content_density profile prior]
      unfold GameTheory.Protocol.InformationModel.stepProb
      rw [setup.commitRecoveryModel.behavioralJoint_prob_eq_prod]
      simp only [commitRecoveryOpeningFactor, commitRecoveryBindingContent]
      split <;> ring

/-- Every actual clear source path loses at most one source tremble factor
per owner and instruction when its reveal-choice factors are removed. -/
theorem commitRecovery_opening_factor_bounds (n : Nat) :
    ∀ {state : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace state) (_clear : setup.CommitRecoveryClear state),
      (1 - approximation.epsilon n) ^ (Fintype.card Player * trace.length) ≤
          setup.commitRecoveryOpeningFactor (approximation.sequence n).strategy trace ∧
        setup.commitRecoveryOpeningFactor (approximation.sequence n).strategy trace ≤ 1
  | _, .start, _ => by simp only [commitRecoveryOpeningFactor, Trace.length, mul_zero, pow_zero,
      le_refl, and_self]
  | _, .extend (source := before) prior joint legal reached, clear => by
      have beforeClear := setup.commitRecoveryClear_before ⟨joint, legal⟩ reached clear
      obtain ⟨lower, upper⟩ := commitRecovery_opening_factor_bounds n prior beforeClear
      let base := 1 - approximation.epsilon n
      have baseNonnegative : 0 ≤ base := sub_nonneg.mpr (approximation.small n).le
      have baseBounded : base ≤ 1 := sub_le_self _ (approximation.positive n).le
      let current := if before.elim false (fun state =>
          ProtocolState.atCommit setup.program state.point) then (1 : ℝ) else
        ∏ who, ((approximation.sequence n).strategy who (setup.commitRecoveryModel.infoOf who prior)
          (setup.commitRecoveryModel.choicesOfLegal prior ⟨joint, legal⟩ who)).toReal
      have currentNonnegative : 0 ≤ current := by
        dsimp only [current]
        split
        · exact zero_le_one
        · exact Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
      have currentBounds : base ^ Fintype.card Player ≤ current ∧ current ≤ 1 := by
        dsimp only [current]
        split
        · exact ⟨pow_le_one₀ baseNonnegative baseBounded, le_refl _⟩
        · rename_i notCommit
          have notCommit : before.elim false (fun state =>
              ProtocolState.atCommit setup.program state.point) = false :=
            Bool.eq_false_iff.mpr notCommit
          constructor
          · calc
              _ = ∏ _who : Player, base := by simp only [Finset.prod_const, Finset.card_univ]
              _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => baseNonnegative) fun who _ =>
                setup.commitRecovery_clear_noncommit_atom_lower wellFormed reference target
                  approximation n prior joint legal reached clear notCommit who
          · exact Finset.prod_le_one₀ (fun _ _ => ENNReal.toReal_nonneg)
              (fun who _ => pmf_toReal_apply_le_one _ _)
      change base ^ (Fintype.card Player * (prior.length + 1)) ≤
          setup.commitRecoveryOpeningFactor (approximation.sequence n).strategy prior * current ∧
        setup.commitRecoveryOpeningFactor (approximation.sequence n).strategy prior * current ≤ 1
      constructor
      · rw [Nat.mul_add, Nat.mul_one, pow_add]
        exact mul_le_mul lower currentBounds.1 (pow_nonneg baseNonnegative _)
          ((pow_nonneg baseNonnegative _).trans lower)
      · exact (mul_le_mul_of_nonneg_right upper currentNonnegative).trans
          (by simpa only [one_mul] using currentBounds.2)

private theorem binding_content_nonnegative
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) :
    ∀ {state : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace state),
      0 ≤ setup.commitRecoveryBindingContent profile trace
  | _, .start => zero_le_one
  | _, .extend prior _ _ _ => by
      change 0 ≤ _ * _ * _
      refine mul_nonneg (mul_nonneg (binding_content_nonnegative profile prior) ?_)
        ENNReal.toReal_nonneg
      split
      · exact Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
      · exact zero_le_one

/-- Binding content and the original chance atoms approximate the ACTUAL AUX
source reach relatively. The missing factor is the genuine reveal-choice
product, not an erased physical opening-WAIT or an assumed posterior identity. -/
theorem commitRecovery_source_binding_bounds (n : Nat)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (clear : setup.CommitRecoveryClear state) :
    (1 - approximation.epsilon n) ^ (Fintype.card Player * trace.length) *
        setup.commitRecoveryBindingContent (approximation.sequence n).strategy trace ≤
      (setup.commitRecoveryModel.historyReachWeight (approximation.sequence n).strategy
        ⟨state, trace⟩).toReal ∧
    (setup.commitRecoveryModel.historyReachWeight (approximation.sequence n).strategy
        ⟨state, trace⟩).toReal ≤
      setup.commitRecoveryBindingContent (approximation.sequence n).strategy trace := by
  obtain ⟨lower, upper⟩ := setup.commitRecovery_opening_factor_bounds wellFormed reference target
    approximation n trace clear
  rw [setup.commitRecovery_source_content_density]
  have nonnegative := binding_content_nonnegative setup (approximation.sequence n).strategy trace
  exact ⟨mul_le_mul_of_nonneg_right lower nonnegative,
    (mul_le_mul_of_nonneg_right upper nonnegative).trans_eq (one_mul _)⟩

open Filter in
/-- The reveal correction tends to one even when the genuine clear source
history varies with the approximant. The uniform exponent is derived from
the actual source protocol budget, including its recovery bookkeeping. -/
theorem commitRecovery_opening_factor_tendsto
    (histories : Nat → setup.commitRecoveryProtocol.History)
    (clear : ∀ n, setup.CommitRecoveryClear (histories n).state) :
    Tendsto (fun n => setup.commitRecoveryOpeningFactor (approximation.sequence n).strategy
      (histories n).trace) atTop (nhds 1) := by
  let horizon := (Fintype.card Player + 1) * (instructionCount setup.program + 1)
  have lowerLimit : Tendsto (fun n => (1 - approximation.epsilon n) ^
      (Fintype.card Player * horizon)) atTop (nhds (1 : ℝ)) := by
    simpa only [sub_zero, one_pow] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub approximation.vanishes).pow
        (Fintype.card Player * horizon)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le lowerLimit tendsto_const_nhds
  · intro n
    obtain ⟨lower, _⟩ := setup.commitRecovery_opening_factor_bounds wellFormed reference target
      approximation n (histories n).trace (clear n)
    have budget : (histories n).trace.length ≤ horizon := by
      have actual := setup.commitRecovery_history_budget (histories n).trace
      omega
    exact (pow_le_pow_of_le_one (sub_nonneg.mpr (approximation.small n).le)
      (sub_le_self _ (approximation.positive n).le)
      (Nat.mul_le_mul_left (Fintype.card Player) budget)).trans lower
  · intro n
    exact (setup.commitRecovery_opening_factor_bounds wellFormed reference target approximation
      n (histories n).trace (clear n)).2

end Setup
end Vegas.SourceProgram
