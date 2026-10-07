/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.RestrictionDomination
import GameTheory.Protocol.RestrictionExecution
import GameTheory.Protocol.RestrictionProfile
import GameTheory.Protocol.Strategic
import GameTheory.Core.UtilityTransfer
import GameTheoryExtensions.Protocol.MenuRestriction

/-! # Whole-policy deviations under an action restriction

An action restriction embeds a smaller protocol into a larger one that offers
additional choices. Against a profile that extends a profile of the smaller
protocol, a deviation in the larger protocol is compared with its *retained
conditional*: at every embedded information value the deviator plays the
deviation's law conditioned on the retained choices
(`GameTheory.Protocol.InformationModel.ActionRestriction.retainedPolicy`).
Whenever a realized transition from an embedded history reaches an embedded
history only along retained choices, every embedded history is at least as
likely under the retained conditional as under the deviation
(`GameTheory.Protocol.InformationModel.ActionRestriction.runBehavioral_embedded_le`).

If, moreover, an additional choice of the deviator leaves it in an absorbing
debt whose terminal payoffs are no larger than any terminal payoff of the
smaller protocol, the retained conditional is at least as good as the deviation
(`GameTheory.Protocol.InformationModel.ActionRestriction.expect_deviation_le_retained`),
and every approximate Nash equilibrium of the smaller protocol extends to an
approximate Nash equilibrium of the larger one with the same slack
(`GameTheory.Protocol.InformationModel.ActionRestriction.isεNash_extends_of_debt`).
-/

noncomputable section

namespace GameTheory.Math.Probability

open scoped ENNReal

variable {α β : Type*}

open Classical in
/-- The conditional of a law on the image of an embedding, pulled back along
the embedding; the fallback when the image has no mass. -/
def embeddedConditional (law : PMF β) (embedding : α ↪ β) (fallback : PMF α) : PMF α :=
  if present : ∃ a, law (embedding a) ≠ 0 then
    (law.filter (Set.range embedding) ⟨embedding present.choose, ⟨present.choose, rfl⟩,
      (PMF.mem_support_iff _ _).mpr present.choose_spec⟩).map
        (@Function.invFun _ _ ⟨present.choose⟩ embedding)
  else fallback

/-- Conditioning on the retained image never lowers the probability of a
retained value. -/
theorem le_embeddedConditional (law : PMF β) (embedding : α ↪ β) (fallback : PMF α) (a : α) :
    law (embedding a) ≤ embeddedConditional law embedding fallback a := by
  classical
  by_cases present : ∃ a, law (embedding a) ≠ 0
  · have support : ∃ b ∈ Set.range embedding, b ∈ law.support :=
      ⟨embedding present.choose, ⟨present.choose, rfl⟩,
        (PMF.mem_support_iff _ _).mpr present.choose_spec⟩
    simp only [embeddedConditional, present, ↓reduceDIte]
    have inverse : @Function.invFun _ _ ⟨present.choose⟩ embedding (embedding a) = a :=
      @Function.leftInverse_invFun _ _ ⟨present.choose⟩ _ embedding.injective a
    calc law (embedding a)
        ≤ law (embedding a) * (∑' b, (Set.range embedding).indicator law b)⁻¹ := by
          apply le_mul_of_one_le_right zero_le
          apply ENNReal.one_le_inv.mpr
          calc ∑' b, (Set.range embedding).indicator law b ≤ ∑' b, law b :=
                ENNReal.tsum_le_tsum fun b => Set.indicator_le_self _ _ b
            _ = 1 := law.tsum_coe
      _ = (law.filter (Set.range embedding) support) (embedding a) := by
          rw [PMF.filter_apply, Set.indicator_of_mem (Set.mem_range_self a)]
      _ ≤ _ := by
          rw [PMF.map_apply]
          refine le_trans ?_ (ENNReal.le_tsum (embedding a))
          simp only [inverse, ↓reduceIte, le_refl]
  · have absent : law (embedding a) = 0 := by
      by_contra nonzero
      exact present ⟨a, nonzero⟩
    rw [absent]
    exact zero_le

private theorem sum_toReal_eq_one {α : Type*} [Fintype α] (law : PMF α) :
    ∑ a, (law a).toReal = 1 := by
  have constant := expect_constant law 1
  rw [expect_eq_sum] at constant
  simpa using constant

private theorem expect_eq_shifted {α : Type*} [Fintype α] (law : PMF α) (payoff : α → ℝ)
    (floor : ℝ) : expect law payoff = (∑ a, (law a).toReal * (payoff a - floor)) + floor := by
  rw [expect_eq_sum]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_toReal_eq_one law]
  ring

end GameTheory.Math.Probability

namespace GameTheory.Protocol.InformationModel.ActionRestriction

open GameTheory.Math.Probability ExecutionProtocol
open scoped ENNReal

variable {ι : Type*} {E T : ExecutionProtocol ι}
  {M : InformationModel E} {N : InformationModel T} (restriction : M.ActionRestriction N)

/-- **The retained conditional of a deviation.** At every information value of
the smaller model, play the deviation's law at the embedded value conditioned
on the retained choices, or the fallback when they have no mass. -/
def retainedPolicy (who : ι) (deviation : N.BehavioralPolicy who)
    (fallback : M.BehavioralPolicy who) : M.BehavioralPolicy who := fun info =>
  embeddedConditional (deviation (restriction.information who info))
    (restriction.choice who info) (fallback info)

private theorem transport_apply {Index : Type*} {Value : Index → Type*}
    (laws : ∀ index, PMF (Value index)) {first second : Index} (same : second = first)
    (value : Value second) :
    laws first (Eq.mp (congrArg Value same) value) = laws second value := by
  subst same
  rfl

private theorem map_apply_embedding {α β : Type*} (law : PMF α) (embedding : α → β)
    (injective : Function.Injective embedding) (a : α) :
    law.map embedding (embedding a) = law a := by
  classical
  rw [PMF.map_apply]
  rw [tsum_eq_single a]
  · simp
  · intro other different
    rw [ite_eq_right_iff.mpr fun same => (different (injective same).symm).elim]

/-- The transitions from an embedded history reaching an embedded history are
those of the smaller protocol: every source of such a transition is embedded,
and from an embedded nonterminal history every joint draw reaching an embedded
history is the embedding of a draw of the smaller protocol. -/
structure Reflecting : Prop where
  prefixClosed : ∀ (history : T.History) choices (next : E.History),
    restriction.history next ∈ (N.localStep history choices).support →
      ∃ original, restriction.history original = history
  retainedDraws : ∀ (original : E.History)
    (choices : ∀ who, N.Choice who (N.infoOf who (restriction.history original).trace))
    (next : E.History), ¬ E.terminal original.state →
      restriction.history next ∈ (N.localStep (restriction.history original) choices).support →
      ∃ draws : ∀ who, M.Choice who (M.infoOf who original.trace),
        choices = fun who => restriction.choiceAt who original (draws who)

variable [Fintype ι] [DecidableEq ι] {restriction}

/-- One embedded step is at least as likely under the retained conditional. -/
private theorem one_step_le (reflecting : restriction.Reflecting)
    (source : ∀ i, M.BehavioralPolicy i) (target : ∀ i, N.BehavioralPolicy i)
    (agrees : restriction.ExtendsProfile source target) (who : ι)
    (deviation : N.BehavioralPolicy who) (fallback : M.BehavioralPolicy who)
    (original next : E.History) :
    N.runBehavioralFrom (Function.update target who deviation) 1
        (restriction.history original) (restriction.history next) ≤
      M.runBehavioralFrom (Function.update source who
        (restriction.retainedPolicy who deviation fallback)) 1 original next := by
  classical
  by_cases stopped : E.terminal original.state
  · rw [N.runBehavioralFrom_of_terminal _ _ ((restriction.terminal original).mpr stopped),
      M.runBehavioralFrom_of_terminal _ _ stopped, PMF.pure_apply, PMF.pure_apply]
    by_cases same : next = original
    · subst same; simp
    · rw [ite_eq_right_iff.mpr fun equal => (same (restriction.history.injective equal)).elim,
        ite_eq_right_iff.mpr fun equal => (same equal).elim]
  · rw [N.runBehavioralFrom_one_localStep, M.runBehavioralFrom_one_localStep, PMF.bind_apply,
      PMF.bind_apply]
    let embed := fun draws : (∀ i, M.Choice i (M.infoOf i original.trace)) =>
      fun i => restriction.choiceAt i original (draws i)
    have embedInjective : Function.Injective embed := by
      intro first second same
      funext i
      exact (restriction.choiceAt i original).injective (congrFun same i)
    rw [← embedInjective.tsum_eq]
    · apply ENNReal.tsum_le_tsum
      intro draws
      have stepEq : N.localStep (restriction.history original) (embed draws) =
          (M.localStep original draws).map restriction.history :=
        (restriction.step original draws).symm
      rw [stepEq, map_apply_embedding _ _ restriction.history.injective]
      gcongr
      rw [independentProduct_apply, independentProduct_apply]
      apply Finset.prod_le_prod
      intro i _
      by_cases deviating : i = who
      · subst deviating
        simp only [Function.update_self, embed, choiceAt, Function.Embedding.coeFn_mk]
        rw [transport_apply deviation (restriction.observed i original).symm]
        exact le_embeddedConditional _ _ _ _
      · simp only [Function.update_of_ne deviating, embed]
        rw [restriction.extends_at_history source target agrees original stopped i]
        exact (map_apply_embedding _ _ (restriction.choiceAt i original).injective _).le
    · intro choices nonzero
      have reached : restriction.history next ∈
          (N.localStep (restriction.history original) choices).support := by
        rw [PMF.mem_support_iff]
        exact right_ne_zero_of_mul nonzero
      obtain ⟨draws, rfl⟩ := reflecting.retainedDraws original choices next stopped reached
      exact ⟨draws, rfl⟩

/-- **Embedded histories under the retained conditional.** Against a profile
extending one of the smaller protocol, every embedded history is at least as
likely when the deviator plays the retained conditional of its deviation. -/
theorem runBehavioral_embedded_le (reflecting : restriction.Reflecting)
    (source : ∀ i, M.BehavioralPolicy i) (target : ∀ i, N.BehavioralPolicy i)
    (agrees : restriction.ExtendsProfile source target) (who : ι)
    (deviation : N.BehavioralPolicy who) (fallback : M.BehavioralPolicy who)
    (fuel : ℕ) (history : E.History) :
    N.runBehavioral (Function.update target who deviation) fuel (restriction.history history) ≤
      M.runBehavioral (Function.update source who
        (restriction.retainedPolicy who deviation fallback)) fuel history := by
  classical
  induction fuel generalizing history with
  | zero =>
      simp only [runBehavioral, runBehavioralFrom, ExecutionProtocol.runRandomizedFor,
        ← restriction.initial, PMF.pure_apply]
      by_cases same : history = E.initHistory
      · subst same; simp
      · rw [ite_eq_right_iff.mpr fun equal => (same (restriction.history.injective equal)).elim,
        ite_eq_right_iff.mpr fun equal => (same equal).elim]
  | succ fuel ih =>
      unfold runBehavioral
      rw [N.runBehavioralFrom_add _ fuel 1, M.runBehavioralFrom_add _ fuel 1, PMF.bind_apply,
        PMF.bind_apply, ← restriction.history.injective.tsum_eq]
      · apply ENNReal.tsum_le_tsum
        intro original
        exact mul_le_mul' (ih original)
          (one_step_le reflecting source target agrees who deviation fallback original history)
      · intro prior nonzero
        have reached : restriction.history history ∈
            (N.runBehavioralFrom (Function.update target who deviation) 1 prior).support := by
          rw [PMF.mem_support_iff]
          exact right_ne_zero_of_mul nonzero
        by_cases stopped : T.terminal prior.state
        · rw [N.runBehavioralFrom_of_terminal _ _ stopped] at reached
          exact ⟨history, ((PMF.mem_support_pure_iff _ _).mp reached)⟩
        · rw [N.runBehavioralFrom_one_localStep, PMF.support_bind] at reached
          obtain ⟨choices, _, step⟩ := Set.mem_iUnion₂.mp reached
          exact reflecting.prefixClosed prior choices history step

/-- Under the profile extending a profile of the smaller protocol and any
deviation, every reached history is embedded or carries the deviator's debt,
provided the debt is absorbing and an additional choice of the deviator from
an embedded history incurs it. -/
theorem embedded_or_debt (source : ∀ i, M.BehavioralPolicy i)
    (target : ∀ i, N.BehavioralPolicy i) (agrees : restriction.ExtendsProfile source target)
    (who : ι) (deviation : N.BehavioralPolicy who) (debt : T.State → Prop)
    (absorbing : ∀ (history : T.History) choices next, debt history.state →
      next ∈ (N.localStep history choices).support → debt next.state)
    (incurred : ∀ (original : E.History)
      (choices : ∀ i, N.Choice i (N.infoOf i (restriction.history original).trace)) next,
      ¬ E.terminal original.state →
      (∀ i, i ≠ who → choices i ∈ Set.range (restriction.choiceAt i original)) →
      choices who ∉ Set.range (restriction.choiceAt who original) →
      next ∈ (N.localStep (restriction.history original) choices).support → debt next.state)
    (fuel : ℕ) :
    ∀ reached ∈ (N.runBehavioral (Function.update target who deviation) fuel).support,
      reached ∈ Set.range restriction.history ∨ debt reached.state := by
  classical
  induction fuel with
  | zero =>
      intro reached member
      simp only [runBehavioral, runBehavioralFrom, ExecutionProtocol.runRandomizedFor,
        PMF.mem_support_pure_iff] at member
      exact Or.inl ⟨E.initHistory, member ▸ restriction.initial⟩
  | succ fuel ih =>
      intro reached member
      unfold runBehavioral at member
      rw [N.runBehavioralFrom_add _ fuel 1, PMF.support_bind] at member
      obtain ⟨prior, priorMember, step⟩ := Set.mem_iUnion₂.mp member
      rcases ih prior priorMember with ⟨original, rfl⟩ | indebted
      · by_cases stopped : E.terminal original.state
        · rw [N.runBehavioralFrom_of_terminal _ _ ((restriction.terminal original).mpr stopped),
            PMF.mem_support_pure_iff] at step
          exact Or.inl ⟨original, step.symm⟩
        · rw [N.runBehavioralFrom_one_localStep, PMF.support_bind] at step
          obtain ⟨choices, drawn, realized⟩ := Set.mem_iUnion₂.mp step
          rw [independentProduct_support_iff] at drawn
          have others : ∀ i, i ≠ who → choices i ∈ Set.range (restriction.choiceAt i original) := by
            intro i different
            have member := drawn i
            simp only [Function.update_of_ne different] at member
            rw [restriction.extends_at_history source target agrees original stopped i,
              PMF.support_map] at member
            obtain ⟨draw, _, equal⟩ := member
            exact ⟨draw, equal⟩
          by_cases retained : choices who ∈ Set.range (restriction.choiceAt who original)
          · left
            have all : ∀ i, choices i ∈ Set.range (restriction.choiceAt i original) := by
              intro i
              by_cases same : i = who
              · subst same; exact retained
              · exact others i same
            choose draws drawsEq using all
            have spelled : choices = fun i => restriction.choiceAt i original (draws i) :=
              funext fun i => (drawsEq i).symm
            subst spelled
            have square := restriction.step original draws
            change _ = N.localStep _ (fun i => restriction.choiceAt i original (draws i))
              at square
            rw [← square, PMF.support_map] at realized
            obtain ⟨next, _, equal⟩ := realized
            exact ⟨next, equal⟩
          · exact Or.inr (incurred original choices reached stopped others retained realized)
      · right
        by_cases stopped : T.terminal prior.state
        · rw [N.runBehavioralFrom_of_terminal _ _ stopped, PMF.mem_support_pure_iff] at step
          exact step ▸ indebted
        · rw [N.runBehavioralFrom_one_localStep, PMF.support_bind] at step
          obtain ⟨choices, _, realized⟩ := Set.mem_iUnion₂.mp step
          exact absorbing prior choices reached indebted realized

/-- **The retained conditional is at least as good as the deviation.** If
the deviator's debt is absorbing, is incurred by every additional choice from
an embedded history, and every terminal payoff in debt is no larger than every
terminal payoff of the smaller protocol, then the deviation's expected payoff
is at most that of its retained conditional. -/
theorem expect_deviation_le_retained [Finite T.History] {fuel : ℕ}
    (bounded : T.BoundedHorizon fuel) (reflecting : restriction.Reflecting)
    (source : ∀ i, M.BehavioralPolicy i) (target : ∀ i, N.BehavioralPolicy i)
    (agrees : restriction.ExtendsProfile source target) (who : ι)
    (deviation : N.BehavioralPolicy who) (fallback : M.BehavioralPolicy who)
    (debt : T.State → Prop)
    (absorbing : ∀ (history : T.History) choices next, debt history.state →
      next ∈ (N.localStep history choices).support → debt next.state)
    (incurred : ∀ (original : E.History)
      (choices : ∀ i, N.Choice i (N.infoOf i (restriction.history original).trace)) next,
      ¬ E.terminal original.state →
      (∀ i, i ≠ who → choices i ∈ Set.range (restriction.choiceAt i original)) →
      choices who ∉ Set.range (restriction.choiceAt who original) →
      next ∈ (N.localStep (restriction.history original) choices).support → debt next.state)
    (sourcePayoff : E.History → ℝ) (targetPayoff : T.History → ℝ)
    (matching : ∀ history, targetPayoff (restriction.history history) = sourcePayoff history)
    (forfeits : ∀ (indebted : T.History) (history : E.History), debt indebted.state →
      T.terminal indebted.state → E.terminal history.state →
      targetPayoff indebted ≤ sourcePayoff history) :
    expect (N.runBehavioral (Function.update target who deviation) fuel) targetPayoff ≤
      expect (M.runBehavioral (Function.update source who
        (restriction.retainedPolicy who deviation fallback)) fuel) sourcePayoff := by
  classical
  let _ : Fintype T.History := Fintype.ofFinite _
  have : Finite E.History := Finite.of_injective _ restriction.history.injective
  let _ : Fintype E.History := Fintype.ofFinite _
  let embed := restriction.history
  let deviated := N.runBehavioral (Function.update target who deviation) fuel
  let retained := M.runBehavioral (Function.update source who
    (restriction.retainedPolicy who deviation fallback)) fuel
  have sourceBounded : E.BoundedHorizon fuel := restriction.boundedHorizon bounded
  -- The smallest payoff the retained conditional realizes.
  obtain ⟨least, leastMember, leastMin⟩ :=
    (retained.support.toFinite.toFinset).exists_min_image sourcePayoff
      ((Set.Finite.toFinset_nonempty _).mpr retained.support_nonempty)
  rw [Set.Finite.mem_toFinset] at leastMember
  let floor := sourcePayoff least
  have floorLe : ∀ history ∈ retained.support, floor ≤ sourcePayoff history :=
    fun history member => leastMin history ((Set.Finite.mem_toFinset _).mpr member)
  have dominated : ∀ history, (deviated (embed history)).toReal ≤ (retained history).toReal :=
    fun history => ENNReal.toReal_mono (PMF.apply_ne_top _ _)
      (runBehavioral_embedded_le reflecting source target agrees who deviation fallback fuel
        history)
  have outside : ∀ reached, reached ∉ Set.range embed → (deviated reached).toReal ≠ 0 →
      targetPayoff reached ≤ floor := by
    intro reached notEmbedded positive
    have member : reached ∈ deviated.support := by
      rw [PMF.mem_support_iff]
      intro zero
      exact positive (by rw [zero, ENNReal.toReal_zero])
    have indebted := (embedded_or_debt source target agrees who deviation debt absorbing
      incurred fuel reached member).resolve_left notEmbedded
    exact forfeits reached least indebted
      (N.runBehavioralFrom_terminal_of_bound _ bounded _ reached member)
      (M.runBehavioralFrom_terminal_of_bound _ sourceBounded _ least leastMember)
  rw [expect_eq_shifted deviated _ floor, expect_eq_shifted retained _ floor,
    add_le_add_iff_right]
  calc ∑ reached, (deviated reached).toReal * (targetPayoff reached - floor)
      ≤ ∑ reached, (if reached ∈ Set.range embed then
          (deviated reached).toReal * (targetPayoff reached - floor) else 0) := by
        apply Finset.sum_le_sum
        intro reached _
        split_ifs with embedded
        · exact le_rfl
        · by_cases zero : (deviated reached).toReal = 0
          · rw [zero, zero_mul]
          · exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg
              (sub_nonpos.mpr (outside reached embedded zero))
    _ = ∑ history, (deviated (embed history)).toReal * (sourcePayoff history - floor) := by
        rw [← Finset.sum_filter]
        have rewritten : ∑ history, (deviated (embed history)).toReal *
              (sourcePayoff history - floor) =
            ∑ history, (fun reached => (deviated reached).toReal *
              (targetPayoff reached - floor)) (embed history) :=
          Finset.sum_congr rfl fun history _ => by simp only [embed, matching]
        rw [rewritten, ← Finset.sum_map Finset.univ embed
          (fun reached => (deviated reached).toReal * (targetPayoff reached - floor))]
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext reached
        simp [Set.mem_range]
    _ ≤ ∑ history, (retained history).toReal * (sourcePayoff history - floor) := by
        apply Finset.sum_le_sum
        intro history _
        by_cases zero : (retained history).toReal = 0
        · have below := dominated history
          rw [zero] at below ⊢
          rw [le_antisymm below ENNReal.toReal_nonneg, zero_mul]
        · have member : history ∈ retained.support := by
            rw [PMF.mem_support_iff]
            intro equal
            exact zero (by rw [equal, ENNReal.toReal_zero])
          exact mul_le_mul_of_nonneg_right (dominated history)
            (sub_nonneg.mpr (floorLe history member))

/-- **Approximate Nash extends across a debt-enforced restriction.** Let every
additional choice of a player from an embedded history leave it in an
absorbing debt whose terminal payoffs are no larger than any terminal payoff of
the smaller protocol, and let the payoffs agree on embedded histories. Then
every profile extending an `ε`-Nash equilibrium of the smaller protocol is an
`ε`-Nash equilibrium of the larger one, at any horizon bounding the larger
protocol. -/
theorem isεNash_extends_of_debt [Finite T.History] {fuel : ℕ}
    (bounded : T.BoundedHorizon fuel) (reflecting : restriction.Reflecting)
    (source : ∀ i, M.BehavioralPolicy i) (target : ∀ i, N.BehavioralPolicy i)
    (agrees : restriction.ExtendsProfile source target)
    (debt : ι → T.State → Prop)
    (absorbing : ∀ who (history : T.History) choices next, debt who history.state →
      next ∈ (N.localStep history choices).support → debt who next.state)
    (incurred : ∀ who (original : E.History)
      (choices : ∀ i, N.Choice i (N.infoOf i (restriction.history original).trace)) next,
      ¬ E.terminal original.state →
      (∀ i, i ≠ who → choices i ∈ Set.range (restriction.choiceAt i original)) →
      choices who ∉ Set.range (restriction.choiceAt who original) →
      next ∈ (N.localStep (restriction.history original) choices).support →
        debt who next.state)
    (sourceUtility : E.History → ι → ℝ) (targetUtility : T.History → ι → ℝ)
    (matching : ∀ history who,
      targetUtility (restriction.history history) who = sourceUtility history who)
    (forfeits : ∀ who (indebted : T.History) (history : E.History), debt who indebted.state →
      T.terminal indebted.state → E.terminal history.state →
      targetUtility indebted who ≤ sourceUtility history who)
    (ε : ℝ) (equilibrium : IsεNash (M.toBehavioralGameForm fuel) sourceUtility ε source) :
    IsεNash (N.toBehavioralGameForm fuel) targetUtility ε target := by
  classical
  have : Finite E.History := Finite.of_injective _ restriction.history.injective
  refine GameForm.isεNash_of_deviation_bounds (source := M.toBehavioralGameForm fuel)
    (target := N.toBehavioralGameForm fuel) (sourceUtility := sourceUtility)
    (targetUtility := targetUtility) source target (fun who _ => ?_) (fun who replacement => ?_)
    ε equilibrium
  · have law := restriction.initialized_law source target agrees fuel
    have integrable : UtilityIntegrable targetUtility who (N.runBehavioral target fuel) :=
      payoffIntegrable_of_finite _ _
    have sourceIntegrable : UtilityIntegrable sourceUtility who (M.runBehavioral source fuel) :=
      payoffIntegrable_of_finite _ _
    refine ⟨integrable.hasExpectation, ?_⟩
    change extendedExpectedUtility targetUtility who (N.runBehavioral target fuel) =
      extendedExpectedUtility sourceUtility who (M.runBehavioral source fuel)
    rw [extendedExpectedUtility_eq integrable, extendedExpectedUtility_eq sourceIntegrable]
    unfold expectedUtility
    rw [← law, expect_map]
    exact congrArg (fun value : ℝ => (value : EReal))
      (congrArg (expect _) (funext fun history => matching history who))
  · refine ⟨restriction.retainedPolicy who replacement (source who), fun _ => ?_⟩
    have integrable : UtilityIntegrable targetUtility who
        (N.runBehavioral (Function.update target who replacement) fuel) :=
      payoffIntegrable_of_finite _ _
    have sourceIntegrable : UtilityIntegrable sourceUtility who
        (M.runBehavioral (Function.update source who
          (restriction.retainedPolicy who replacement (source who))) fuel) :=
      payoffIntegrable_of_finite _ _
    refine ⟨integrable.hasExpectation, ?_⟩
    change extendedExpectedUtility targetUtility who
        (N.runBehavioral (Function.update target who replacement) fuel) ≤
      extendedExpectedUtility sourceUtility who
        (M.runBehavioral (Function.update source who
          (restriction.retainedPolicy who replacement (source who))) fuel)
    rw [extendedExpectedUtility_eq integrable, extendedExpectedUtility_eq sourceIntegrable]
    exact EReal.coe_le_coe_iff.mpr (expect_deviation_le_retained bounded reflecting source
      target agrees who replacement (source who) (debt who) (absorbing who) (incurred who)
      (fun history => sourceUtility history who) (fun history => targetUtility history who)
      (fun history => matching history who) (forfeits who))

omit [Fintype ι] [DecidableEq ι] in
/-- Updating one player of a profile with a policy, and of an extension of the
profile with an extension of that policy, keeps the extension. -/
theorem ExtendsProfile.update {source : (i : ι) → M.BehavioralPolicy i}
    {target : (i : ι) → N.BehavioralPolicy i} (agrees : restriction.ExtendsProfile source target)
    [DecidableEq ι] (who : ι) (deviation : M.BehavioralPolicy who)
    (extension : N.BehavioralPolicy who)
    (extended : ∀ original : M.InformationSite who,
      extension (restriction.information who original.1) =
        (deviation original.1).map (restriction.choice who original.1)) :
    restriction.ExtendsProfile (Function.update source who deviation)
      (Function.update target who extension) := by
  intro player original
  rcases eq_or_ne player who with rfl | different
  · simp only [Function.update_self]
    exact extended original
  · simp only [Function.update_of_ne different]
    exact agrees player original

omit [Fintype ι] [DecidableEq ι] in
/-- Updating one player of a profile with a policy keeps an extension of the
profile an extension, once that player plays the extension of the updated
profile. -/
theorem ExtendsProfile.update_extendProfile {source : (i : ι) → M.BehavioralPolicy i}
    {target : (i : ι) → N.BehavioralPolicy i} (agrees : restriction.ExtendsProfile source target)
    [DecidableEq ι] (who : ι) (deviation : M.BehavioralPolicy who) :
    restriction.ExtendsProfile (Function.update source who deviation)
      (Function.update target who
        (restriction.extendProfile (Function.update source who deviation) target who)) :=
  agrees.update who deviation _ fun original => by
    have extended := restriction.extendProfile_extends (Function.update source who deviation)
      target who original
    simpa only [Function.update_self] using extended

end GameTheory.Protocol.InformationModel.ActionRestriction

namespace GameTheory.Protocol.InformationModel

open ExecutionProtocol

variable {ι : Type*} {E : ExecutionProtocol ι} (M : InformationModel E)
  {available : (state : E.State) → (i : ι) → Set (E.Action i)}
  {included : ∀ state i, available state i ⊆ E.available state i}
  {progress : ∀ state, ¬ E.terminal state →
    ∃ joint, IsLegalJoint (E.active state) (available state) joint}

private theorem cast_choice_val {who : ι} {first second : M.InfoState who}
    (same : first = second) (cast : M.Choice who first = M.Choice who second)
    (choice : M.Choice who first) : (Eq.mp cast choice).1 = choice.1 := by
  subst same
  rfl

omit M in
/-- A restricted history extending an original history extends a restricted
history by a joint action legal in the restricted protocol. -/
theorem restrictAvailable_history_eq_extend
    {next : (E.restrictAvailable available included progress).History}
    {history : E.History} {joint : ∀ i, Option (E.Action i)}
    {legal : E.Legal history.state joint} {target : E.State}
    {realized : target ∈ (E.step history.state ⟨joint, legal⟩).support}
    (same : restrictAvailable.history next = history.extend legal realized) :
    ∃ prior : (E.restrictAvailable available included progress).History,
      restrictAvailable.history prior = history ∧
        (E.restrictAvailable available included progress).Legal history.state joint := by
  rcases history with ⟨state, trace⟩
  rcases next with ⟨nextState, nextTrace⟩
  cases nextTrace with
  | start =>
      simp only [restrictAvailable.history, restrictAvailable.trace, History.extend,
        History.mk.injEq] at same
      obtain ⟨rfl, mismatch⟩ := same
      cases mismatch
  | extend prior otherJoint permitted otherRealized =>
      simp only [restrictAvailable.history, restrictAvailable.trace, History.extend,
        History.mk.injEq] at same
      obtain ⟨rfl, rfl, priorEq, rfl⟩ := same
      refine ⟨⟨_, prior⟩, ?_, permitted⟩
      simp only [restrictAvailable.history]

variable (menu : ∀ who, M.InfoState who → Set (Option (E.Action who)))
  (adequate : ∀ who {state}
    (trace : (E.restrictAvailable available included progress).Trace state)
    (choice : Option (E.Action who)),
    choice ∈ menu who (M.infoOf who (restrictAvailable.trace trace)) ↔
      LegalOption (E.restrictAvailable available included progress) state who choice)
  (menuIncluded : ∀ who info, menu who info ⊆ M.menu who info)

/-- The embedded choice at a restricted history spells the same option. -/
theorem menuRestriction_choiceAt_val (who : ι)
    (original : (E.restrictAvailable available included progress).History)
    (choice : (M.restrictMenu menu adequate).Choice who
      ((M.restrictMenu menu adequate).infoOf who original.trace)) :
    ((M.menuRestriction menu adequate menuIncluded).choiceAt who original choice).1 =
      choice.1 := by
  simp only [ActionRestriction.choiceAt, Function.Embedding.coeFn_mk]
  rw [cast_choice_val M ((M.menuRestriction menu adequate menuIncluded).observed who
    original).symm]
  rfl

/-- An additional choice at a restricted history is an action missing from the
restricted menu: silence is never additional, since activity is unchanged. -/
theorem menuRestriction_extraAt (who : ι)
    (original : (E.restrictAvailable available included progress).History)
    (choice : M.Choice who (M.infoOf who (restrictAvailable.history original).trace))
    (extra : choice ∉ Set.range ((M.menuRestriction menu adequate menuIncluded).choiceAt who
      original)) :
    ∃ action, choice.1 = some action ∧
      some action ∉ menu who (M.infoOf who (restrictAvailable.trace original.trace)) := by
  have missing : choice.1 ∉ menu who (M.infoOf who (restrictAvailable.trace original.trace)) := by
    intro member
    apply extra
    refine ⟨⟨choice.1, by rw [restrictMenu_infoOf]; exact member⟩, ?_⟩
    apply Subtype.ext
    exact M.menuRestriction_choiceAt_val menu adequate menuIncluded who original _
  cases spelled : choice.1 with
  | some action => exact ⟨action, rfl, spelled ▸ missing⟩
  | none =>
      exfalso
      apply missing
      rw [spelled, adequate who original.trace none]
      have legal := (M.menu_adequate who (restrictAvailable.history original).trace
        choice.1).mp choice.2
      rw [spelled] at legal
      exact legal

/-- A menu restriction reflects transitions: the source of a transition into a
restricted history is restricted, and every joint draw from a restricted
history into a restricted history is a draw of the restricted menus. -/
theorem menuRestriction_reflecting :
    (M.menuRestriction menu adequate menuIncluded).Reflecting where
  prefixClosed history choices next reached := by
    by_cases stopped : E.terminal history.state
    · simp only [localStep, dite_eq_left_of_eq_true (eq_true stopped),
        PMF.mem_support_pure_iff] at reached
      exact ⟨next, reached⟩
    · simp only [localStep, dite_eq_right_of_eq_false (eq_false stopped),
        PMF.mem_support_bindOnSupport_iff, PMF.mem_support_pure_iff] at reached
      obtain ⟨_, _, extended⟩ := reached
      obtain ⟨prior, priorEq, _⟩ := restrictAvailable_history_eq_extend extended
      exact ⟨prior, priorEq⟩
  retainedDraws original choices next running reached := by
    have running' : ¬ E.terminal (restrictAvailable.history original).state := running
    simp only [menuRestriction_history] at reached
    simp only [localStep, dite_eq_right_of_eq_false (eq_false running'),
      PMF.mem_support_bindOnSupport_iff, PMF.mem_support_pure_iff] at reached
    obtain ⟨_, _, extended⟩ := reached
    obtain ⟨_, _, permitted⟩ := restrictAvailable_history_eq_extend extended
    refine ⟨fun who => ⟨(choices who).1, by
      rw [restrictMenu_infoOf]
      exact (adequate who original.trace (choices who).1).mpr
        (legalOption_of_legal permitted who)⟩, ?_⟩
    funext who
    apply Subtype.ext
    simp only [ActionRestriction.choiceAt, Function.Embedding.coeFn_mk]
    rw [cast_choice_val M ((M.menuRestriction menu adequate menuIncluded).observed who
      original).symm]
    rfl

end GameTheory.Protocol.InformationModel


