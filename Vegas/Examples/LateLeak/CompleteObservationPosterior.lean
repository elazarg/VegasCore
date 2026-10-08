/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.CompleteObservation

/-! # Bayes beliefs for complete public opening traffic

The sender's explicit perturbations ignore its extra public transcript. Before
the listener's answer their history weights therefore equal those in the
original state-based execution. Equal label weights are proved from these
primitive choice laws, including unreached late turns.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter
open scoped ENNReal

variable {G : LateLeakParameters}

private theorem public_prefix_joint (G : LateLeakParameters) (n : ℕ)
    (history : (lateLeakExecution G true).History)
    (running : ¬ history.state.IsFinished)
    (notListener : history.state.actor ≠ some .listener) :
    (lateOpeningPublicModel G).behavioralJoint (lateOpeningPublicTrembleProfile G n)
        history.trace running =
      (lateLeakModel G true).behavioralJoint (lateOpeningPublicPrefixReference G n)
        history.trace running := by
  have unique : ∀ who, (lateLeakExecution G true).active history.state who →
      who = .sender := by
    intro who active
    cases who with
    | sender => rfl
    | listener => exact (notListener active).elim
  apply pmf_map_injective Subtype.val_injective
  rw [(lateOpeningPublicModel G).behavioralJoint_eq_map_of_at_most_one_active
      _ history.trace running .sender unique,
    (lateLeakModel G true).behavioralJoint_eq_map_of_at_most_one_active
      _ history.trace running .sender unique]
  simp only [PMF.map_comp]
  cases history with
  | mk state trace => cases trace <;> rfl

private theorem public_prefix_step (G : LateLeakParameters) (n : ℕ)
    (history : (lateLeakExecution G true).History)
    (notListener : history.state.actor ≠ some .listener) :
    (lateOpeningPublicModel G).runBehavioralFrom (lateOpeningPublicTrembleProfile G n)
        1 history =
      (lateLeakModel G true).runBehavioralFrom (lateOpeningPublicPrefixReference G n)
        1 history := by
  apply (lateLeakExecution G true).runRandomizedFor_one_congr_at_start
  exact fun running => public_prefix_joint G n history running notListener

/-- Before the final answer, the actual refined information and the old
reference profile have identical history reach weights. -/
theorem lateOpeningPublic_prefix_reach (G : LateLeakParameters) (n : ℕ) :
    ∀ {state} (trace : (lateLeakExecution G true).Trace state),
      ¬ state.IsFinished →
      (lateOpeningPublicModel G).historyReachWeight (lateOpeningPublicTrembleProfile G n)
          ⟨state, trace⟩ =
        (lateLeakModel G true).historyReachWeight (lateOpeningPublicPrefixReference G n)
          ⟨state, trace⟩
  | _, .start, _ => by
      change (lateOpeningPublicModel G).historyReachWeight _
        (lateLeakExecution G true).initHistory =
        (lateLeakModel G true).historyReachWeight _ (lateLeakExecution G true).initHistory
      rw [InformationModel.historyReachWeight_initHistory,
        InformationModel.historyReachWeight_initHistory]
  | _, .extend (source := source) (target := target) prior joint legal realized, running => by
      have notListener : source.actor ≠ some .listener := by
        change target ∈ (lateLeakAdvance G source (joint source.mover)).support at realized
        cases source with
        | answering secret resolution =>
            simp only [lateLeakAdvance, PMF.mem_support_pure_iff] at realized
            subst realized
            exact (running trivial).elim
        | _ => simp [LateLeakState.actor]
      let history : (lateLeakExecution G true).History :=
        ⟨target, .extend prior joint legal realized⟩
      change (lateOpeningPublicModel G).historyReachWeight _ history =
        (lateLeakModel G true).historyReachWeight _ history
      rw [(lateOpeningPublicModel G).historyReachWeight_eq_prior_mul _ history
          (Nat.succ_pos _),
        (lateLeakModel G true).historyReachWeight_eq_prior_mul _ history
          (Nat.succ_pos _)]
      change (lateOpeningPublicModel G).historyReachWeight _ ⟨source, prior⟩ *
        (lateOpeningPublicModel G).runBehavioralFrom _ 1 ⟨source, prior⟩ _ =
        (lateLeakModel G true).historyReachWeight _ ⟨source, prior⟩ *
        (lateLeakModel G true).runBehavioralFrom _ 1 ⟨source, prior⟩ _
      rw [lateOpeningPublic_prefix_reach G n prior legal.1,
        public_prefix_step G n ⟨source, prior⟩ notListener]

/-- Perturbed protected-send probabilities are independent of both hidden
type components. This is a primitive policy equality, not a belief premise. -/
theorem lateOpeningPublic_protected_law_type_independent (G : LateLeakParameters) (n : ℕ)
    (first second : LateLeakType) :
    lateLeakOpeningLaw (lateOpeningPublicPrefixReference G n) (.protectedTurn first) =
      lateLeakOpeningLaw (lateOpeningPublicPrefixReference G n) (.protectedTurn second) := by
  rfl

theorem lateOpeningPublic_first_law_type_independent (G : LateLeakParameters) (n : ℕ)
    (first second : LateLeakType) :
    lateLeakOpeningLaw (lateOpeningPublicPrefixReference G n) (.firstLate first) =
      lateLeakOpeningLaw (lateOpeningPublicPrefixReference G n) (.firstLate second) := by
  rfl

theorem lateOpeningPublic_second_law_type_independent (G : LateLeakParameters) (n : ℕ)
    (first second : LateLeakType) :
    lateLeakOpeningLaw (lateOpeningPublicPrefixReference G n) (.secondLate first) =
      lateLeakOpeningLaw (lateOpeningPublicPrefixReference G n) (.secondLate second) := by
  rfl

/-- The unique pre-answer history realizing a specified type and resolution. -/
def lateOpeningPublicAnswerHistory (G : LateLeakParameters) (secret : LateLeakType) :
    LateLeakResolution → (lateLeakExecution G true).History
  | .protectedOpen => lateLeakOpenedHistory G true secret
  | .firstIncluded => lateLeakFirstSentHistory G secret true
  | .firstDropped => lateLeakFirstSentHistory G secret false
  | .secondIncluded => lateLeakSecondSentHistory G secret true
  | .secondDropped => lateLeakSecondSentHistory G secret false
  | .withheld => (lateLeakSecondHistory G secret).extend
      (lateLeak_sender_legal G true (.secondLate secret) rfl false ⟨false, rfl⟩)
      (target := .answering secret .withheld) (by
        change _ ∈ (lateLeakAdvance G (.secondLate secret) (some (.opening false))).support
        simp [lateLeakAdvance])

theorem lateOpeningPublicAnswerHistory_state (G : LateLeakParameters)
    (secret : LateLeakType) (resolution : LateLeakResolution) :
    (lateOpeningPublicAnswerHistory G secret resolution).state = .answering secret resolution := by
  cases resolution <;> rfl

/-- Complete traffic information at the listener's unique decision. -/
def lateOpeningPublicListenerInfo (bit : Bool) (resolution : LateLeakResolution) :
    (lateOpeningPublicModel G).InfoState .listener :=
  ((.asked (lateLeakSignal (bit, .a) resolution),
    lateOpeningPublicTranscript (.answering (bit, .a) resolution)), [])

def lateOpeningPublicAnswerMember (G : LateLeakParameters) (bit : Bool)
    (resolution : LateLeakResolution) (label : LateLeakLabel) :
    (lateOpeningPublicModel G).InformationHistory .listener
      (lateOpeningPublicListenerInfo (G := G) bit resolution) :=
  ⟨lateOpeningPublicAnswerHistory G (bit, label) resolution, by
    cases resolution <;> apply lateOpeningPublic_listener_info_answering⟩

theorem lateOpeningPublicAnswerHistory_info (G : LateLeakParameters)
    (secret : LateLeakType) (resolution : LateLeakResolution) :
    (lateOpeningPublicModel G).infoOf .listener
        (lateOpeningPublicAnswerHistory G secret resolution).trace =
      ((.asked (lateLeakSignal secret resolution),
        lateOpeningPublicTranscript (.answering secret resolution)), []) := by
  cases resolution <;> apply lateOpeningPublic_listener_info_answering

/-- A compatible listener history has exactly the publicly recorded
resolution. Every emitted packet also fixes its transmitted bit. -/
theorem lateOpeningPublic_listener_fiber_state (bit : Bool) (resolution : LateLeakResolution)
    (history : (lateOpeningPublicModel G).InformationHistory .listener
      (lateOpeningPublicListenerInfo (G := G) bit resolution)) :
    ∃ secret, history.1.state = .answering secret resolution ∧
      (resolution ≠ .withheld → secret.1 = bit) := by
  have original : (lateLeakModel G true).infoOf .listener history.1.trace =
      .asked (lateLeakSignal (bit, .a) resolution) := by
    rw [lateLeak_model_infoOf]
    have oldView := congrArg (fun info => info.1.1)
      (lateOpeningPublicModel_infoOf G .listener history.1.trace)
    exact oldView.symm.trans (congrArg (fun info => info.1.1) history.2)
  obtain ⟨secret, actual, state, _signal⟩ := lateLeak_listener_fiber_state
    (late := true) ⟨history.1, original⟩
  have same : history.1 = lateOpeningPublicAnswerHistory G secret actual :=
    lateLeak_history_eq_of_state_eq (state.trans
      (lateOpeningPublicAnswerHistory_state G secret actual).symm)
  have observed := history.2
  rw [same, lateOpeningPublicAnswerHistory_info] at observed
  have reported := congrArg (fun info => info.1.2.2.map Prod.fst) observed
  change some actual = some resolution at reported
  have equal := Option.some.inj reported
  subst actual
  refine ⟨secret, state, ?_⟩
  intro emitted
  have transmitted := congrArg (fun info => info.1.2.2.bind Prod.snd) observed
  change (if resolution = .withheld then none else some secret.1) =
    (if resolution = .withheld then none else some bit) at transmitted
  rw [ite_eq_right emitted, ite_eq_right emitted] at transmitted
  exact Option.some.inj transmitted

/-- An emitted public packet's listener fiber contains just the three labels
at its observed bit and recorded resolution. -/
theorem lateOpeningPublic_emitted_fiber_members (bit : Bool)
    (resolution : LateLeakResolution) (emitted : resolution ≠ .withheld)
    (history : (lateOpeningPublicModel G).InformationHistory .listener
      (lateOpeningPublicListenerInfo (G := G) bit resolution)) :
    ∃ label, history = lateOpeningPublicAnswerMember G bit resolution label := by
  obtain ⟨⟨actualBit, label⟩, state, known⟩ :=
    lateOpeningPublic_listener_fiber_state bit resolution history
  have equal := known emitted
  dsimp only at equal
  subst actualBit
  refine ⟨label, Subtype.ext ?_⟩
  exact lateLeak_history_eq_of_state_eq (state.trans
    (lateOpeningPublicAnswerHistory_state G (bit, label) resolution).symm)

/-- Public emitted-packet information retains exactly the undisclosed label. -/
def lateOpeningPublicEmittedFiberEquiv (bit : Bool)
    (resolution : LateLeakResolution) (emitted : resolution ≠ .withheld) :
    LateLeakLabel ≃ (lateOpeningPublicModel G).InformationHistory .listener
      (lateOpeningPublicListenerInfo (G := G) bit resolution) :=
  Equiv.ofBijective (lateOpeningPublicAnswerMember G bit resolution) ⟨by
    intro first second equal
    have states := congrArg (fun history => history.1.state) equal
    change (lateOpeningPublicAnswerHistory G (bit, first) resolution).state =
      (lateOpeningPublicAnswerHistory G (bit, second) resolution).state at states
    rw [lateOpeningPublicAnswerHistory_state, lateOpeningPublicAnswerHistory_state] at states
    cases states
    rfl,
    fun history => by
      obtain ⟨label, same⟩ := lateOpeningPublic_emitted_fiber_members bit resolution emitted history
      exact ⟨label, same.symm⟩⟩

/-- Withholding leaves both private type components undisclosed. -/
def lateOpeningPublicWithheldMember (G : LateLeakParameters) (secret : LateLeakType) :
    (lateOpeningPublicModel G).InformationHistory .listener
      (lateOpeningPublicListenerInfo (G := G) false .withheld) :=
  ⟨lateOpeningPublicAnswerHistory G secret .withheld, by
    rw [lateOpeningPublicAnswerHistory_info]
    rfl⟩

def lateOpeningPublicWithheldFiberEquiv (G : LateLeakParameters) :
    LateLeakType ≃ (lateOpeningPublicModel G).InformationHistory .listener
      (lateOpeningPublicListenerInfo (G := G) false .withheld) :=
  Equiv.ofBijective (lateOpeningPublicWithheldMember G) ⟨by
    intro first second equal
    have states := congrArg (fun history => history.1.state) equal
    change LateLeakState.answering first .withheld = .answering second .withheld at states
    cases states
    rfl,
    fun history => by
      obtain ⟨secret, state, _⟩ := lateOpeningPublic_listener_fiber_state false .withheld history
      refine ⟨secret, Subtype.ext ?_⟩
      exact lateLeak_history_eq_of_state_eq
        ((lateOpeningPublicAnswerHistory_state G secret .withheld).trans state.symm)⟩

private theorem kernel_second_withheld (profile : LateLeakProfile G true)
    (secret : LateLeakType) :
    lateLeakKernel profile (.secondLate secret) (.answering secret .withheld) =
      lateLeakOpeningLaw profile (.secondLate secret) (some (.opening false)) := by
  change ((lateLeakOpeningLaw profile (.secondLate secret)).bind
    (lateLeakAdvance G (.secondLate secret))) _ = _
  rw [bind_apply_of_unique_branch _ _ _ (some (.opening false)) (by
    intro choice supported reached
    obtain ⟨now, rfl⟩ := lateLeakOpeningLaw_support profile _ rfl choice supported
    cases now
    · rfl
    · simp only [lateLeakAdvance, ite_true, PMF.support_map] at reached
      obtain ⟨included, _, impossible⟩ := reached
      cases included <;> cases impossible)]
  simp [lateLeakAdvance]

private theorem reference_weight_withheld (G : LateLeakParameters) (n : ℕ)
    (secret : LateLeakType) :
    (lateLeakModel G true).historyReachWeight (lateOpeningPublicPrefixReference G n)
        (lateOpeningPublicAnswerHistory G secret .withheld) =
      lateLeakPrior secret *
        lateLeakOpeningLaw (lateOpeningPublicPrefixReference G n)
          (.protectedTurn secret) (some (.opening false)) *
        lateLeakOpeningLaw (lateOpeningPublicPrefixReference G n)
          (.firstLate secret) (some (.opening false)) *
        lateLeakOpeningLaw (lateOpeningPublicPrefixReference G n)
          (.secondLate secret) (some (.opening false)) := by
  rw [lateLeak_reachWeight_step _ _ (by change 0 < 4; decide)]
  change (lateLeakModel G true).historyReachWeight _ (lateLeakSecondHistory G secret) *
    lateLeakKernel _ (.secondLate secret) (.answering secret .withheld) = _
  rw [lateLeak_weight_second, kernel_second_withheld]

/-- Each fixed observed bit and resolution has the same prefix weight for
every hidden label. Even late histories are computed from the explicit
primitive type-independent sender perturbations. -/
theorem lateOpeningPublic_answer_weight_label_eq (G : LateLeakParameters) (n : ℕ)
    (bit : Bool) (resolution : LateLeakResolution) (first second : LateLeakLabel) :
    (lateOpeningPublicModel G).historyReachWeight (lateOpeningPublicTrembleProfile G n)
        (lateOpeningPublicAnswerHistory G (bit, first) resolution) =
      (lateOpeningPublicModel G).historyReachWeight (lateOpeningPublicTrembleProfile G n)
        (lateOpeningPublicAnswerHistory G (bit, second) resolution) := by
  rw [lateOpeningPublic_prefix_reach G n _ (by
      rw [lateOpeningPublicAnswerHistory_state]; simp [LateLeakState.IsFinished]),
    lateOpeningPublic_prefix_reach G n _ (by
      rw [lateOpeningPublicAnswerHistory_state]; simp [LateLeakState.IsFinished])]
  cases resolution with
  | protectedOpen =>
      change (lateLeakModel G true).historyReachWeight _ (lateLeakOpenedHistory G true _) =
        (lateLeakModel G true).historyReachWeight _ (lateLeakOpenedHistory G true _)
      rw [lateLeak_weight_opened, lateLeak_weight_opened]
      rfl
  | firstIncluded =>
      change (lateLeakModel G true).historyReachWeight _ (lateLeakFirstSentHistory G _ true) =
        (lateLeakModel G true).historyReachWeight _ (lateLeakFirstSentHistory G _ true)
      rw [lateLeak_weight_first_sent, lateLeak_weight_first_sent]
      rfl
  | firstDropped =>
      change (lateLeakModel G true).historyReachWeight _ (lateLeakFirstSentHistory G _ false) =
        (lateLeakModel G true).historyReachWeight _ (lateLeakFirstSentHistory G _ false)
      rw [lateLeak_weight_first_sent, lateLeak_weight_first_sent]
      rfl
  | secondIncluded =>
      change (lateLeakModel G true).historyReachWeight _ (lateLeakSecondSentHistory G _ true) =
        (lateLeakModel G true).historyReachWeight _ (lateLeakSecondSentHistory G _ true)
      rw [lateLeak_weight_second_sent, lateLeak_weight_second_sent]
      rfl
  | secondDropped =>
      change (lateLeakModel G true).historyReachWeight _ (lateLeakSecondSentHistory G _ false) =
        (lateLeakModel G true).historyReachWeight _ (lateLeakSecondSentHistory G _ false)
      rw [lateLeak_weight_second_sent, lateLeak_weight_second_sent]
      rfl
  | withheld =>
      rw [reference_weight_withheld, reference_weight_withheld]
      rfl

/-- Every public resolution admits the ordinary final listener decision. -/
def lateOpeningPublicListenerSite (G : LateLeakParameters) (bit : Bool)
    (resolution : LateLeakResolution) : (lateOpeningPublicModel G).InformationSite .listener := by
  let answer : LateLeakAnswer := if resolution.succeeded then .safe else .failure false
  refine ⟨lateOpeningPublicListenerInfo (G := G) bit resolution,
    ⟨lateOpeningPublicAnswerMember G bit resolution .a, ?_, .reply answer, ?_⟩⟩
  · change ¬ (lateOpeningPublicAnswerHistory G (bit, .a) resolution).state.IsFinished
    rw [lateOpeningPublicAnswerHistory_state]
    simp [LateLeakState.IsFinished]
  · exact ⟨answer, rfl, by cases resolution <;> rfl⟩

/-- The explicit fully mixed Bayes assessments assign equal weight to every
label in every fixed public resolution fiber, including failed late sends. -/
theorem lateOpeningPublic_tremble_belief_label_eq (G : LateLeakParameters) (n : ℕ)
    (bit : Bool) (resolution : LateLeakResolution) (first second : LateLeakLabel) :
    (lateOpeningPublicTrembleAssessment G n).belief .listener
        (lateOpeningPublicListenerSite G bit resolution)
        (lateOpeningPublicAnswerMember G bit resolution first) =
      (lateOpeningPublicTrembleAssessment G n).belief .listener
        (lateOpeningPublicListenerSite G bit resolution)
        (lateOpeningPublicAnswerMember G bit resolution second) := by
  simp only [lateOpeningPublicTrembleAssessment, InformationModel.bayesAssessment,
    InformationModel.bayesBelief_apply]
  exact congrArg (fun weight => weight / _) (lateOpeningPublic_answer_weight_label_eq
    G n bit resolution first second)

/-- Equal label weights normalize to one third at every emitted-packet site. -/
theorem lateOpeningPublic_emitted_belief_uniform
    (A : (lateOpeningPublicModel G).BehavioralAssessment) (bit : Bool)
    (resolution : LateLeakResolution) (emitted : resolution ≠ .withheld)
    (uniform : ∀ first second,
      A.belief .listener (lateOpeningPublicListenerSite G bit resolution)
          (lateOpeningPublicAnswerMember G bit resolution first) =
        A.belief .listener (lateOpeningPublicListenerSite G bit resolution)
          (lateOpeningPublicAnswerMember G bit resolution second))
    (label : LateLeakLabel) :
    (A.belief .listener (lateOpeningPublicListenerSite G bit resolution)
      (lateOpeningPublicAnswerMember G bit resolution label)).toReal = 1 / 3 := by
  classical
  let e := lateOpeningPublicEmittedFiberEquiv (G := G) bit resolution emitted
  let μ : PMF ((lateOpeningPublicModel G).InformationHistory .listener
      (lateOpeningPublicListenerInfo (G := G) bit resolution)) :=
    A.belief .listener (lateOpeningPublicListenerSite G bit resolution)
  let : Fintype ((lateOpeningPublicModel G).InformationHistory .listener
      (lateOpeningPublicListenerInfo (G := G) bit resolution)) := Fintype.ofFinite _
  have total : ∑ other : LateLeakLabel,
      (μ (lateOpeningPublicAnswerMember G bit resolution other)).toReal = 1 := by
    calc
      _ = ∑ history, (μ history).toReal := Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = 1 := pmf_sum_toReal_eq_one μ
  have each (other : LateLeakLabel) :
      (μ (lateOpeningPublicAnswerMember G bit resolution other)).toReal =
        (μ (lateOpeningPublicAnswerMember G bit resolution label)).toReal :=
    congrArg ENNReal.toReal (uniform other label)
  simp_rw [each] at total
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at total
  have card : Fintype.card LateLeakLabel = 3 := rfl
  rw [card] at total
  change (μ (lateOpeningPublicAnswerMember G bit resolution label)).toReal = 1 / 3
  norm_num at total ⊢
  linarith

private def withheldEmissionFactor (G : LateLeakParameters) (n : ℕ) : ℝ≥0∞ :=
  lateLeakOpeningLaw (lateOpeningPublicPrefixReference G n)
      (.protectedTurn (false, .a)) (some (.opening false)) *
    lateLeakOpeningLaw (lateOpeningPublicPrefixReference G n)
      (.firstLate (false, .a)) (some (.opening false)) *
    lateLeakOpeningLaw (lateOpeningPublicPrefixReference G n)
      (.secondLate (false, .a)) (some (.opening false))

private theorem withheld_weight_factor (G : LateLeakParameters) (n : ℕ)
    (secret : LateLeakType) :
    (lateOpeningPublicModel G).historyReachWeight (lateOpeningPublicTrembleProfile G n)
        (lateOpeningPublicWithheldMember G secret).1 =
      lateLeakPrior secret * withheldEmissionFactor G n := by
  change (lateOpeningPublicModel G).historyReachWeight (lateOpeningPublicTrembleProfile G n)
      (lateOpeningPublicAnswerHistory G secret .withheld) = _
  rw [lateOpeningPublic_prefix_reach G n _ (by
    rw [lateOpeningPublicAnswerHistory_state]; simp [LateLeakState.IsFinished])]
  change (lateLeakModel G true).historyReachWeight (lateOpeningPublicPrefixReference G n)
      (lateOpeningPublicAnswerHistory G secret .withheld) = _
  rw [reference_weight_withheld]
  rw [lateOpeningPublic_protected_law_type_independent G n secret (false, .a),
    lateOpeningPublic_first_law_type_independent G n secret (false, .a),
    lateOpeningPublic_second_law_type_independent G n secret (false, .a)]
  simp only [withheldEmissionFactor, mul_assoc]

private theorem withheld_informationMass (G : LateLeakParameters) (n : ℕ) :
    (lateOpeningPublicModel G).informationMass (lateOpeningPublicTrembleProfile G n)
      .listener (lateOpeningPublicListenerSite G false .withheld) =
      withheldEmissionFactor G n := by
  unfold InformationModel.informationMass
  change (∑' history : (lateOpeningPublicModel G).InformationHistory .listener
      (lateOpeningPublicListenerInfo (G := G) false .withheld),
    (lateOpeningPublicModel G).historyReachWeight (lateOpeningPublicTrembleProfile G n)
      history.1) = _
  rw [← (lateOpeningPublicWithheldFiberEquiv G).tsum_eq]
  simp only [lateOpeningPublicWithheldFiberEquiv, Equiv.ofBijective_apply,
    withheld_weight_factor]
  rw [ENNReal.tsum_mul_right, lateLeakPrior.tsum_coe, one_mul]

/-- Withholding has exactly the original type prior in every explicit Bayes
perturbation: all three waits have the same likelihood at every type. -/
theorem lateOpeningPublic_tremble_belief_withheld (G : LateLeakParameters) (n : ℕ)
    (secret : LateLeakType) :
    (lateOpeningPublicTrembleAssessment G n).belief .listener
      (lateOpeningPublicListenerSite G false .withheld)
      (lateOpeningPublicWithheldMember G secret) = lateLeakPrior secret := by
  have positive := (lateOpeningPublicModel G).informationMass_pos_of_fullSupport
    (lateOpeningPublicTrembleProfile G n) (lateOpeningPublicTrembleProfile_full G n)
    .listener (lateOpeningPublicListenerSite G false .withheld)
  have finite := (lateOpeningPublicModel G).informationMass_le_one
    (lateOpeningPublicTrembleProfile G n) .listener
    (lateOpeningPublicListenerSite G false .withheld)
    ((lateOpeningPublicModel_decisionRecall G).decisionInformationAntichain _ _)
  rw [withheld_informationMass] at positive finite
  simp only [lateOpeningPublicTrembleAssessment, InformationModel.bayesAssessment,
    InformationModel.bayesBelief_apply, withheld_weight_factor, withheld_informationMass]
  exact ENNReal.mul_div_cancel_right (ne_of_gt positive)
    (ne_of_lt (lt_of_le_of_lt finite ENNReal.one_lt_top))

/-- The canonical assessment can be chosen consistently with equal label
weights at every public resolution, including its unreached late decisions. -/
theorem lateOpeningPublicCanonical_consistent_label_uniform (G : LateLeakParameters) :
    ∃ A : (lateOpeningPublicModel G).BehavioralAssessment,
      A.IsSequentiallyConsistent
        (lateOpeningPublicModel_decisionRecall G).decisionInformationAntichain ∧
      (∀ who (site : (lateOpeningPublicModel G).InformationSite who),
        A.strategy who site.1 = lateOpeningPublicCanonical G who site.1) ∧
      ∀ bit resolution first second,
        A.belief .listener (lateOpeningPublicListenerSite G bit resolution)
            (lateOpeningPublicAnswerMember G bit resolution first) =
          A.belief .listener (lateOpeningPublicListenerSite G bit resolution)
            (lateOpeningPublicAnswerMember G bit resolution second) := by
  obtain ⟨A, index, _increasing, converges, agrees⟩ :=
    lateOpeningPublicCanonical_consistent_witness G
  let M := lateOpeningPublicModel G
  let anti := (lateOpeningPublicModel_decisionRecall G).decisionInformationAntichain
  refine ⟨A, converges.isSequentiallyConsistent anti
    (fun n => lateOpeningPublicTrembleProfile_full G (index n))
    (fun n => M.bayesAssessment_isBayesConsistent (lateOpeningPublicTrembleProfile G (index n))
      (lateOpeningPublicTrembleProfile_full G (index n)) anti), agrees, ?_⟩
  intro bit resolution first second
  have firstLimit := converges.belief .listener (lateOpeningPublicListenerSite G bit resolution)
    (lateOpeningPublicAnswerMember G bit resolution first)
  have secondLimit := converges.belief .listener (lateOpeningPublicListenerSite G bit resolution)
    (lateOpeningPublicAnswerMember G bit resolution second)
  exact tendsto_nhds_unique firstLimit (secondLimit.congr
    (fun n => lateOpeningPublic_tremble_belief_label_eq G (index n) bit resolution second first))

/-- One consistent canonical assessment has the original label posterior
after every public packet and the original full prior after withholding. -/
theorem lateOpeningPublicCanonical_consistent_public_beliefs (G : LateLeakParameters) :
    ∃ A : (lateOpeningPublicModel G).BehavioralAssessment,
      A.IsSequentiallyConsistent
        (lateOpeningPublicModel_decisionRecall G).decisionInformationAntichain ∧
      (∀ who (site : (lateOpeningPublicModel G).InformationSite who),
        A.strategy who site.1 = lateOpeningPublicCanonical G who site.1) ∧
      (∀ bit resolution first second,
        A.belief .listener (lateOpeningPublicListenerSite G bit resolution)
            (lateOpeningPublicAnswerMember G bit resolution first) =
          A.belief .listener (lateOpeningPublicListenerSite G bit resolution)
            (lateOpeningPublicAnswerMember G bit resolution second)) ∧
      (∀ secret,
        A.belief .listener (lateOpeningPublicListenerSite G false .withheld)
          (lateOpeningPublicWithheldMember G secret) = lateLeakPrior secret) := by
  obtain ⟨A, index, _increasing, converges, agrees⟩ :=
    lateOpeningPublicCanonical_consistent_witness G
  let M := lateOpeningPublicModel G
  let anti := (lateOpeningPublicModel_decisionRecall G).decisionInformationAntichain
  refine ⟨A, converges.isSequentiallyConsistent anti
    (fun n => lateOpeningPublicTrembleProfile_full G (index n))
    (fun n => M.bayesAssessment_isBayesConsistent (lateOpeningPublicTrembleProfile G (index n))
      (lateOpeningPublicTrembleProfile_full G (index n)) anti), agrees, ?_, ?_⟩
  · intro bit resolution first second
    have firstLimit := converges.belief .listener (lateOpeningPublicListenerSite G bit resolution)
      (lateOpeningPublicAnswerMember G bit resolution first)
    have secondLimit := converges.belief .listener (lateOpeningPublicListenerSite G bit resolution)
      (lateOpeningPublicAnswerMember G bit resolution second)
    exact tendsto_nhds_unique firstLimit (secondLimit.congr
      (fun n => lateOpeningPublic_tremble_belief_label_eq G (index n) bit resolution second first))
  · intro secret
    have limit : Tendsto (fun _ : ℕ => lateLeakPrior secret) atTop
        (nhds (A.belief .listener (lateOpeningPublicListenerSite G false .withheld)
          (lateOpeningPublicWithheldMember G secret))) := by
      simpa only [lateOpeningPublic_tremble_belief_withheld] using
        converges.belief .listener (lateOpeningPublicListenerSite G false .withheld)
          (lateOpeningPublicWithheldMember G secret)
    exact tendsto_nhds_unique limit tendsto_const_nhds

end Vegas
