/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateLeak.Listener

/-! # Consistent beliefs after late inclusions

Take two types of one class that strictly prefer opposite late turns. Along any
fully mixed approximation, Bayes' rule gives beliefs at the first-turn and
second-turn inclusion sets whose cross ratio between the two types is a product
of the types' late-turn choice probabilities. The ratio of their protected-turn
deferral probabilities, however tilted, cancels. In the limit the cross ratio
vanishes, so one of the two limit beliefs gives one of the two types
probability zero.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter
open scoped ENNReal

variable {G : LateLeakParameters}

/-! ## Reach weights of the late histories -/

theorem lateLeak_weight_type (G : LateLeakParameters) (late : Bool)
    (profile : LateLeakProfile G late)
    (secret : LateLeakType) :
    (lateLeakModel G late).historyReachWeight profile (lateLeakTypeHistory G late secret) =
      lateLeakPrior secret := by
  rw [lateLeak_reachWeight_step profile (lateLeakTypeHistory G late secret) (Nat.succ_pos _)]
  change (lateLeakModel G late).historyReachWeight profile (lateLeakExecution G late).initHistory *
    lateLeakKernel profile .initial (.protectedTurn secret) = _
  rw [lateLeak_reachWeight_init, lateLeakKernel_initial, one_mul]

theorem lateLeak_weight_opened (G : LateLeakParameters) (late : Bool)
    (profile : LateLeakProfile G late)
    (secret : LateLeakType) :
    (lateLeakModel G late).historyReachWeight profile (lateLeakOpenedHistory G late secret) =
      lateLeakPrior secret *
        lateLeakOpeningLaw profile (.protectedTurn secret) (some (.opening true)) := by
  rw [lateLeak_reachWeight_step profile (lateLeakOpenedHistory G late secret) (Nat.succ_pos _)]
  change (lateLeakModel G late).historyReachWeight profile (lateLeakTypeHistory G late secret) *
    lateLeakKernel profile (.protectedTurn secret) (.answering secret .protectedOpen) = _
  rw [lateLeak_weight_type, lateLeakKernel_protected_open]

theorem lateLeak_weight_first (profile : LateLeakProfile G true) (secret : LateLeakType) :
    (lateLeakModel G true).historyReachWeight profile (lateLeakFirstHistory G secret) =
      lateLeakPrior secret *
        lateLeakOpeningLaw profile (.protectedTurn secret) (some (.opening false)) := by
  rw [lateLeak_reachWeight_step profile (lateLeakFirstHistory G secret) (Nat.succ_pos _)]
  change (lateLeakModel G true).historyReachWeight profile (lateLeakTypeHistory G true secret) *
    lateLeakKernel profile (.protectedTurn secret) (.firstLate secret) = _
  rw [lateLeak_weight_type, lateLeakKernel_protected_wait]

theorem lateLeak_weight_first_sent (profile : LateLeakProfile G true) (secret : LateLeakType)
    (included : Bool) :
    (lateLeakModel G true).historyReachWeight profile (lateLeakFirstSentHistory G secret included) =
      lateLeakPrior secret *
          lateLeakOpeningLaw profile (.protectedTurn secret) (some (.opening false)) *
        (lateLeakOpeningLaw profile (.firstLate secret) (some (.opening true)) *
          lateLeakInclusion G included) := by
  rw [lateLeak_reachWeight_step profile (lateLeakFirstSentHistory G secret included)
    (Nat.succ_pos _)]
  change (lateLeakModel G true).historyReachWeight profile (lateLeakFirstHistory G secret) *
    lateLeakKernel profile (.firstLate secret)
      (.answering secret (if included then .firstIncluded else .firstDropped)) = _
  rw [lateLeak_weight_first, lateLeakKernel_first_send]

theorem lateLeak_weight_second (profile : LateLeakProfile G true) (secret : LateLeakType) :
    (lateLeakModel G true).historyReachWeight profile (lateLeakSecondHistory G secret) =
      lateLeakPrior secret *
          lateLeakOpeningLaw profile (.protectedTurn secret) (some (.opening false)) *
        lateLeakOpeningLaw profile (.firstLate secret) (some (.opening false)) := by
  rw [lateLeak_reachWeight_step profile (lateLeakSecondHistory G secret) (Nat.succ_pos _)]
  change (lateLeakModel G true).historyReachWeight profile (lateLeakFirstHistory G secret) *
    lateLeakKernel profile (.firstLate secret) (.secondLate secret) = _
  rw [lateLeak_weight_first, lateLeakKernel_first_hold]

theorem lateLeak_weight_second_sent (profile : LateLeakProfile G true) (secret : LateLeakType)
    (included : Bool) :
    (lateLeakModel G true).historyReachWeight profile
      (lateLeakSecondSentHistory G secret included) =
      lateLeakPrior secret *
          lateLeakOpeningLaw profile (.protectedTurn secret) (some (.opening false)) *
          lateLeakOpeningLaw profile (.firstLate secret) (some (.opening false)) *
        (lateLeakOpeningLaw profile (.secondLate secret) (some (.opening true)) *
          lateLeakInclusion G included) := by
  rw [lateLeak_reachWeight_step profile (lateLeakSecondSentHistory G secret included)
    (Nat.succ_pos _)]
  change (lateLeakModel G true).historyReachWeight profile (lateLeakSecondHistory G secret) *
    lateLeakKernel profile (.secondLate secret)
      (.answering secret (if included then .secondIncluded else .secondDropped)) = _
  rw [lateLeak_weight_second, lateLeakKernel_second_send]

/-! ## Listener information sets -/

theorem lateLeak_not_finished_of_asked {state : LateLeakState} {signal : LateLeakSignal}
    (view : lateLeakView .listener state = .asked signal) : ¬ state.IsFinished := by
  cases state <;> simp_all [lateLeakView, LateLeakState.IsFinished]

/-- A history of the listener's information set after a signal. -/
def lateLeakListenerMember (G : LateLeakParameters) (late : Bool) (history :
    (lateLeakExecution G late).History)
    (signal : LateLeakSignal) (view : lateLeakView .listener history.state = .asked signal) :
    (lateLeakModel G late).InformationHistory .listener (.asked signal) :=
  ⟨history, (lateLeak_infoOf G late .listener history.trace).trans view⟩

/-- The listener's information set after a signal, reached by a history. -/
def lateLeakListenerSite (G : LateLeakParameters) (late : Bool) (history :
    (lateLeakExecution G late).History)
    (signal : LateLeakSignal) (view : lateLeakView .listener history.state = .asked signal)
    (answer : LateLeakAnswer) (fits : answer.fits signal) :
    (lateLeakModel G late).InformationSite .listener :=
  ⟨.asked signal, ⟨lateLeakListenerMember G late history signal view,
    lateLeak_not_finished_of_asked view, .reply answer, ⟨answer, rfl, fits⟩⟩⟩

/-- The listener's information set after an inclusion at the first late turn. -/
def lateLeakFirstSuccessSite (G : LateLeakParameters) (bit : Bool) :
    (lateLeakModel G true).InformationSite .listener :=
  lateLeakListenerSite G true (lateLeakFirstSentHistory G (bit, .a) true) (.firstSuccess bit) rfl
    .safe rfl

/-- The listener's information set after an inclusion at the second late turn. -/
def lateLeakSecondSuccessSite (G : LateLeakParameters) (bit : Bool) :
    (lateLeakModel G true).InformationSite .listener :=
  lateLeakListenerSite G true (lateLeakSecondSentHistory G (bit, .a) true) (.secondSuccess bit) rfl
    .safe rfl

/-- The listener's information set after a first-turn opening it saw was
dropped. -/
def lateLeakLeakedFailureSite (G : LateLeakParameters) (bit : Bool) :
    (lateLeakModel G true).InformationSite .listener :=
  lateLeakListenerSite G true (lateLeakFirstSentHistory G (bit, .a) false) (.leakedFailure bit) rfl
    (.failure true) rfl

/-! ## The cross ratio -/

private theorem cross_identity (p0 p1 w0 w1 x0 x1 h0 h1 y0 y1 q m1 m2 : ℝ≥0∞) :
    p0 * w0 * (x0 * q) / m1 * (p1 * w1 * h1 * (y1 * q) / m2) * (x1 * h0 * y0) =
      p1 * w1 * (x1 * q) / m1 * (p0 * w0 * h0 * (y0 * q) / m2) * (x0 * h1 * y1) := by
  simp only [div_eq_mul_inv]
  ring

private theorem opening_ne_zero {A : (lateLeakModel G true).BehavioralAssessment}
    (mixed : A.IsFullyMixed) (history : (lateLeakExecution G true).History)
    (acting : history.state.actor = some .sender) (now : Bool)
    (allowed : some (LateLeakMove.opening now) ∈ lateLeakMenu true (.full history.state)) :
    lateLeakOpeningLaw A.strategy history.state (some (.opening now)) ≠ 0 := by
  rw [lateLeakOpeningLaw_apply _ _ _ allowed]
  exact (PMF.mem_support_iff _ _).mp
    (mixed .sender (lateLeakSenderSite G true history acting) ⟨_, allowed⟩)

private theorem opening_tendsto {sequence : ℕ → (lateLeakModel G true).BehavioralAssessment}
    {A : (lateLeakModel G true).BehavioralAssessment}
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence A)
    (history : (lateLeakExecution G true).History) (acting : history.state.actor = some .sender)
    (now : Bool)
    (allowed : some (LateLeakMove.opening now) ∈ lateLeakMenu true (.full history.state)) :
    Tendsto (fun n =>
        (lateLeakOpeningLaw (sequence n).strategy history.state (some (.opening now))).toReal)
      atTop (nhds (lateLeakOpeningLaw A.strategy history.state (some (.opening now))).toReal) := by
  have limit := (converges.strategy .sender (lateLeakSenderSite G true history acting)).toReal
    ⟨_, allowed⟩
  simp only [lateLeakOpeningLaw_apply _ _ _ allowed]
  exact limit

/-- **Cross ratio.** If one type of a class sends at the first late turn and
another holds there and sends at the second, then every consistent assessment
gives the holding type probability zero after a first-turn inclusion, or the
sending type probability zero after a second-turn inclusion. -/
theorem lateLeak_consistent_face {A : (lateLeakModel G true).BehavioralAssessment}
    (consistent : A.IsSequentiallyConsistent (lateLeak_antichain G true)) (bit : Bool)
    (sender holder : LateLeakLabel)
    (sends : lateLeakOpenProb A.strategy (.firstLate (bit, sender)) = 1)
    (holds : lateLeakOpenProb A.strategy (.firstLate (bit, holder)) = 0)
    (holderSends : lateLeakOpenProb A.strategy (.secondLate (bit, holder)) = 1) :
    A.belief .listener (lateLeakFirstSuccessSite G bit)
        (lateLeakListenerMember G true (lateLeakFirstSentHistory G (bit, holder) true)
          (.firstSuccess bit) rfl) = 0 ∨
      A.belief .listener (lateLeakSecondSuccessSite G bit)
        (lateLeakListenerMember G true (lateLeakSecondSentHistory G (bit, sender) true)
          (.secondSuccess bit) rfl) = 0 := by
  obtain ⟨sequence, approximate, converges⟩ := consistent
  let first := lateLeakFirstSuccessSite G bit
  let second := lateLeakSecondSuccessSite G bit
  let firstMember (label : LateLeakLabel) :
      (lateLeakModel G true).InformationHistory .listener first.1 :=
    lateLeakListenerMember G true (lateLeakFirstSentHistory G (bit, label) true) (.firstSuccess bit)
      rfl
  let secondMember (label : LateLeakLabel) :
      (lateLeakModel G true).InformationHistory .listener second.1 :=
    lateLeakListenerMember G true (lateLeakSecondSentHistory G (bit, label) true)
      (.secondSuccess bit)
      rfl
  /- Opening probabilities along the sequence. -/
  let opening (n : ℕ) (state : LateLeakState) (now : Bool) : ℝ≥0∞ :=
    lateLeakOpeningLaw (sequence n).strategy state (some (.opening now))
  have identity (n : ℕ) :
      (sequence n).belief .listener first (firstMember holder) *
          (sequence n).belief .listener second (secondMember sender) *
          (opening n (.firstLate (bit, sender)) true * opening n (.firstLate (bit, holder)) false *
            opening n (.secondLate (bit, holder)) true) =
        (sequence n).belief .listener first (firstMember sender) *
          (sequence n).belief .listener second (secondMember holder) *
          (opening n (.firstLate (bit, holder)) true * opening n (.firstLate (bit, sender)) false *
            opening n (.secondLate (bit, sender)) true) := by
    obtain ⟨mixed, bayes⟩ := approximate n
    have ne (history : (lateLeakExecution G true).History)
        (acting : history.state.actor = some .sender) (now : Bool)
        (allowed : some (LateLeakMove.opening now) ∈ lateLeakMenu true (.full history.state)) :
        lateLeakOpeningLaw (sequence n).strategy history.state (some (.opening now)) ≠ 0 :=
      opening_ne_zero mixed history acting now allowed
    have firstMass : 0 < (lateLeakModel G true).informationMass (sequence n).strategy .listener
        first := by
      refine ((lateLeakModel G true).informationMass_pos_iff _ _ _).mpr ⟨firstMember sender, ?_⟩
      change 0 < (lateLeakModel G true).historyReachWeight (sequence n).strategy
        (lateLeakFirstSentHistory G (bit, sender) true)
      rw [lateLeak_weight_first_sent]
      exact pos_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero (lateLeakPrior_ne_zero _)
        (ne (lateLeakTypeHistory G true (bit, sender)) rfl false ⟨false, rfl, rfl⟩))
        (mul_ne_zero (ne (lateLeakFirstHistory G (bit, sender)) rfl true ⟨true, rfl⟩)
          (lateLeakInclusion_ne_zero true)))
    have secondMass : 0 < (lateLeakModel G true).informationMass (sequence n).strategy .listener
        second := by
      refine ((lateLeakModel G true).informationMass_pos_iff _ _ _).mpr ⟨secondMember sender, ?_⟩
      change 0 < (lateLeakModel G true).historyReachWeight (sequence n).strategy
        (lateLeakSecondSentHistory G (bit, sender) true)
      rw [lateLeak_weight_second_sent]
      exact pos_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero (lateLeakPrior_ne_zero _)
        (ne (lateLeakTypeHistory G true (bit, sender)) rfl false ⟨false, rfl, rfl⟩))
        (ne (lateLeakFirstHistory G (bit, sender)) rfl false ⟨false, rfl⟩))
        (mul_ne_zero (ne (lateLeakSecondHistory G (bit, sender)) rfl true ⟨true, rfl⟩)
          (lateLeakInclusion_ne_zero true)))
    have firstBayes := bayes .listener first firstMass
    have secondBayes := bayes .listener second secondMass
    rw [firstBayes (firstMember holder), firstBayes (firstMember sender),
      secondBayes (secondMember sender), secondBayes (secondMember holder)]
    change (lateLeakModel G true).historyReachWeight (sequence n).strategy
          (lateLeakFirstSentHistory G (bit, holder) true) / _ *
        ((lateLeakModel G true).historyReachWeight (sequence n).strategy
          (lateLeakSecondSentHistory G (bit, sender) true) / _) * _ =
      (lateLeakModel G true).historyReachWeight (sequence n).strategy
          (lateLeakFirstSentHistory G (bit, sender) true) / _ *
        ((lateLeakModel G true).historyReachWeight (sequence n).strategy
          (lateLeakSecondSentHistory G (bit, holder) true) / _) * _
    rw [lateLeak_weight_first_sent, lateLeak_weight_first_sent, lateLeak_weight_second_sent,
      lateLeak_weight_second_sent]
    exact cross_identity _ _ _ _ _ _ _ _ _ _ _ _ _
  /- Real coordinates and their limits. -/
  have realIdentity (n : ℕ) :
      ((sequence n).belief .listener first (firstMember holder)).toReal *
          ((sequence n).belief .listener second (secondMember sender)).toReal *
          ((opening n (.firstLate (bit, sender)) true).toReal *
            (opening n (.firstLate (bit, holder)) false).toReal *
            (opening n (.secondLate (bit, holder)) true).toReal) =
        ((sequence n).belief .listener first (firstMember sender)).toReal *
          ((sequence n).belief .listener second (secondMember holder)).toReal *
          ((opening n (.firstLate (bit, holder)) true).toReal *
            (opening n (.firstLate (bit, sender)) false).toReal *
            (opening n (.secondLate (bit, sender)) true).toReal) := by
    have := congrArg ENNReal.toReal (identity n)
    simpa only [ENNReal.toReal_mul] using this
  have beliefFirst (label : LateLeakLabel) :=
    (converges.belief .listener first).toReal (firstMember label)
  have beliefSecond (label : LateLeakLabel) :=
    (converges.belief .listener second).toReal (secondMember label)
  have openFirst (label : LateLeakLabel) (now : Bool) :
      Tendsto (fun n => (opening n (.firstLate (bit, label)) now).toReal) atTop
        (nhds (lateLeakOpeningLaw A.strategy (.firstLate (bit, label))
          (some (.opening now))).toReal) :=
    opening_tendsto converges (lateLeakFirstHistory G (bit, label)) rfl now ⟨now, rfl⟩
  have openSecond (label : LateLeakLabel) :
      Tendsto (fun n => (opening n (.secondLate (bit, label)) true).toReal) atTop
        (nhds (lateLeakOpeningLaw A.strategy (.secondLate (bit, label))
          (some (.opening true))).toReal) :=
    opening_tendsto converges (lateLeakSecondHistory G (bit, label)) rfl true ⟨true, rfl⟩
  have senderOpen : (lateLeakOpeningLaw A.strategy (.firstLate (bit, sender))
      (some (.opening true))).toReal = 1 := sends
  have senderWait : (lateLeakOpeningLaw A.strategy (.firstLate (bit, sender))
      (some (.opening false))).toReal = 0 := by
    rw [lateLeakOpeningLaw_wait _ _ rfl, sends, sub_self]
  have holderOpen : (lateLeakOpeningLaw A.strategy (.firstLate (bit, holder))
      (some (.opening true))).toReal = 0 := holds
  have holderWait : (lateLeakOpeningLaw A.strategy (.firstLate (bit, holder))
      (some (.opening false))).toReal = 1 := by
    rw [lateLeakOpeningLaw_wait _ _ rfl, holds, sub_zero]
  have holderSecond : (lateLeakOpeningLaw A.strategy (.secondLate (bit, holder))
      (some (.opening true))).toReal = 1 := holderSends
  have left := ((beliefFirst holder).mul (beliefSecond sender)).mul
    (((openFirst sender true).mul (openFirst holder false)).mul (openSecond holder))
  have right := ((beliefFirst sender).mul (beliefSecond holder)).mul
    (((openFirst holder true).mul (openFirst sender false)).mul (openSecond sender))
  change Tendsto (fun n =>
      ((sequence n).belief .listener first (firstMember holder)).toReal *
          ((sequence n).belief .listener second (secondMember sender)).toReal *
          ((opening n (.firstLate (bit, sender)) true).toReal *
            (opening n (.firstLate (bit, holder)) false).toReal *
            (opening n (.secondLate (bit, holder)) true).toReal)) atTop _ at left
  simp only [realIdentity] at left
  have limits := tendsto_nhds_unique left right
  rw [senderOpen, holderWait, holderSecond, holderOpen, senderWait] at limits
  simp only [mul_one, zero_mul, mul_zero] at limits
  rcases mul_eq_zero.mp limits with zero | zero
  · left
    exact ((ENNReal.toReal_eq_zero_iff _).mp zero).resolve_right (PMF.apply_ne_top _ _)
  · right
    exact ((ENNReal.toReal_eq_zero_iff _).mp zero).resolve_right (PMF.apply_ne_top _ _)

end Vegas
