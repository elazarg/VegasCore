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

/-! ## Reach weights of the late histories -/

theorem lateLeak_weight_type (late : Bool) (profile : LateLeakProfile late)
    (secret : LateLeakType) :
    (lateLeakModel late).historyReachWeight profile (lateLeakTypeHistory late secret) =
      lateLeakPrior secret := by
  rw [lateLeak_reachWeight_step profile (lateLeakTypeHistory late secret) (Nat.succ_pos _)]
  change (lateLeakModel late).historyReachWeight profile (lateLeakExecution late).initHistory *
    lateLeakKernel profile .initial (.protectedTurn secret) = _
  rw [lateLeak_reachWeight_init, lateLeakKernel_initial, one_mul]

theorem lateLeak_weight_opened (late : Bool) (profile : LateLeakProfile late)
    (secret : LateLeakType) :
    (lateLeakModel late).historyReachWeight profile (lateLeakOpenedHistory late secret) =
      lateLeakPrior secret *
        lateLeakOpeningLaw profile (.protectedTurn secret) (some (.opening true)) := by
  rw [lateLeak_reachWeight_step profile (lateLeakOpenedHistory late secret) (Nat.succ_pos _)]
  change (lateLeakModel late).historyReachWeight profile (lateLeakTypeHistory late secret) *
    lateLeakKernel profile (.protectedTurn secret) (.answering secret .protectedOpen) = _
  rw [lateLeak_weight_type, lateLeakKernel_protected_open]

theorem lateLeak_weight_first (profile : LateLeakProfile true) (secret : LateLeakType) :
    (lateLeakModel true).historyReachWeight profile (lateLeakFirstHistory secret) =
      lateLeakPrior secret *
        lateLeakOpeningLaw profile (.protectedTurn secret) (some (.opening false)) := by
  rw [lateLeak_reachWeight_step profile (lateLeakFirstHistory secret) (Nat.succ_pos _)]
  change (lateLeakModel true).historyReachWeight profile (lateLeakTypeHistory true secret) *
    lateLeakKernel profile (.protectedTurn secret) (.firstLate secret) = _
  rw [lateLeak_weight_type, lateLeakKernel_protected_wait]

theorem lateLeak_weight_first_sent (profile : LateLeakProfile true) (secret : LateLeakType)
    (included : Bool) :
    (lateLeakModel true).historyReachWeight profile (lateLeakFirstSentHistory secret included) =
      lateLeakPrior secret *
          lateLeakOpeningLaw profile (.protectedTurn secret) (some (.opening false)) *
        (lateLeakOpeningLaw profile (.firstLate secret) (some (.opening true)) *
          lateLeakInclusion included) := by
  rw [lateLeak_reachWeight_step profile (lateLeakFirstSentHistory secret included) (Nat.succ_pos _)]
  change (lateLeakModel true).historyReachWeight profile (lateLeakFirstHistory secret) *
    lateLeakKernel profile (.firstLate secret)
      (.answering secret (if included then .firstIncluded else .firstDropped)) = _
  rw [lateLeak_weight_first, lateLeakKernel_first_send]

theorem lateLeak_weight_second (profile : LateLeakProfile true) (secret : LateLeakType) :
    (lateLeakModel true).historyReachWeight profile (lateLeakSecondHistory secret) =
      lateLeakPrior secret *
          lateLeakOpeningLaw profile (.protectedTurn secret) (some (.opening false)) *
        lateLeakOpeningLaw profile (.firstLate secret) (some (.opening false)) := by
  rw [lateLeak_reachWeight_step profile (lateLeakSecondHistory secret) (Nat.succ_pos _)]
  change (lateLeakModel true).historyReachWeight profile (lateLeakFirstHistory secret) *
    lateLeakKernel profile (.firstLate secret) (.secondLate secret) = _
  rw [lateLeak_weight_first, lateLeakKernel_first_hold]

theorem lateLeak_weight_second_sent (profile : LateLeakProfile true) (secret : LateLeakType)
    (included : Bool) :
    (lateLeakModel true).historyReachWeight profile (lateLeakSecondSentHistory secret included) =
      lateLeakPrior secret *
          lateLeakOpeningLaw profile (.protectedTurn secret) (some (.opening false)) *
          lateLeakOpeningLaw profile (.firstLate secret) (some (.opening false)) *
        (lateLeakOpeningLaw profile (.secondLate secret) (some (.opening true)) *
          lateLeakInclusion included) := by
  rw [lateLeak_reachWeight_step profile (lateLeakSecondSentHistory secret included)
    (Nat.succ_pos _)]
  change (lateLeakModel true).historyReachWeight profile (lateLeakSecondHistory secret) *
    lateLeakKernel profile (.secondLate secret)
      (.answering secret (if included then .secondIncluded else .secondDropped)) = _
  rw [lateLeak_weight_second, lateLeakKernel_second_send]

/-! ## Listener information sets -/

theorem lateLeak_not_finished_of_asked {state : LateLeakState} {signal : LateLeakSignal}
    (view : lateLeakView .listener state = .asked signal) : ¬ state.IsFinished := by
  cases state <;> simp_all [lateLeakView, LateLeakState.IsFinished]

/-- A history of the listener's information set after a signal. -/
def lateLeakListenerMember (late : Bool) (history : (lateLeakExecution late).History)
    (signal : LateLeakSignal) (view : lateLeakView .listener history.state = .asked signal) :
    (lateLeakModel late).InformationHistory .listener (.asked signal) :=
  ⟨history, (lateLeak_infoOf late .listener history.trace).trans view⟩

/-- The listener's information set after a signal, reached by a history. -/
def lateLeakListenerSite (late : Bool) (history : (lateLeakExecution late).History)
    (signal : LateLeakSignal) (view : lateLeakView .listener history.state = .asked signal)
    (answer : LateLeakAnswer) (fits : answer.fits signal) :
    (lateLeakModel late).InformationSite .listener :=
  ⟨.asked signal, ⟨lateLeakListenerMember late history signal view,
    lateLeak_not_finished_of_asked view, .reply answer, ⟨answer, rfl, fits⟩⟩⟩

/-- The listener's information set after an inclusion at the first late turn. -/
def lateLeakFirstSuccessSite (bit : Bool) : (lateLeakModel true).InformationSite .listener :=
  lateLeakListenerSite true (lateLeakFirstSentHistory (bit, .a) true) (.firstSuccess bit) rfl
    .safe rfl

/-- The listener's information set after an inclusion at the second late turn. -/
def lateLeakSecondSuccessSite (bit : Bool) : (lateLeakModel true).InformationSite .listener :=
  lateLeakListenerSite true (lateLeakSecondSentHistory (bit, .a) true) (.secondSuccess bit) rfl
    .safe rfl

/-- The listener's information set after a first-turn opening it saw was
dropped. -/
def lateLeakLeakedFailureSite (bit : Bool) : (lateLeakModel true).InformationSite .listener :=
  lateLeakListenerSite true (lateLeakFirstSentHistory (bit, .a) false) (.leakedFailure bit) rfl
    (.failure true) rfl

/-! ## The cross ratio -/

private theorem cross_identity (p0 p1 w0 w1 x0 x1 h0 h1 y0 y1 q m1 m2 : ℝ≥0∞) :
    p0 * w0 * (x0 * q) / m1 * (p1 * w1 * h1 * (y1 * q) / m2) * (x1 * h0 * y0) =
      p1 * w1 * (x1 * q) / m1 * (p0 * w0 * h0 * (y0 * q) / m2) * (x0 * h1 * y1) := by
  simp only [div_eq_mul_inv]
  ring

private theorem opening_ne_zero {A : (lateLeakModel true).BehavioralAssessment}
    (mixed : A.IsFullyMixed) (history : (lateLeakExecution true).History)
    (acting : history.state.actor = some .sender) (now : Bool)
    (allowed : some (LateLeakMove.opening now) ∈ lateLeakMenu true (.full history.state)) :
    lateLeakOpeningLaw A.strategy history.state (some (.opening now)) ≠ 0 := by
  rw [lateLeakOpeningLaw_apply _ _ _ allowed]
  exact (PMF.mem_support_iff _ _).mp
    (mixed .sender (lateLeakSenderSite true history acting) ⟨_, allowed⟩)

private theorem opening_tendsto {sequence : ℕ → (lateLeakModel true).BehavioralAssessment}
    {A : (lateLeakModel true).BehavioralAssessment}
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence A)
    (history : (lateLeakExecution true).History) (acting : history.state.actor = some .sender)
    (now : Bool)
    (allowed : some (LateLeakMove.opening now) ∈ lateLeakMenu true (.full history.state)) :
    Tendsto (fun n =>
        (lateLeakOpeningLaw (sequence n).strategy history.state (some (.opening now))).toReal)
      atTop (nhds (lateLeakOpeningLaw A.strategy history.state (some (.opening now))).toReal) := by
  have limit := (converges.strategy .sender (lateLeakSenderSite true history acting)).toReal
    ⟨_, allowed⟩
  simp only [lateLeakOpeningLaw_apply _ _ _ allowed]
  exact limit

/-- **Cross ratio.** If one type of a class sends at the first late turn and
another holds there and sends at the second, then every consistent assessment
gives the holding type probability zero after a first-turn inclusion, or the
sending type probability zero after a second-turn inclusion. -/
theorem lateLeak_consistent_face {A : (lateLeakModel true).BehavioralAssessment}
    (consistent : A.IsSequentiallyConsistent (lateLeak_antichain true)) (bit : Bool)
    (sender holder : LateLeakLabel)
    (sends : lateLeakOpenProb A.strategy (.firstLate (bit, sender)) = 1)
    (holds : lateLeakOpenProb A.strategy (.firstLate (bit, holder)) = 0)
    (holderSends : lateLeakOpenProb A.strategy (.secondLate (bit, holder)) = 1) :
    A.belief .listener (lateLeakFirstSuccessSite bit)
        (lateLeakListenerMember true (lateLeakFirstSentHistory (bit, holder) true)
          (.firstSuccess bit) rfl) = 0 ∨
      A.belief .listener (lateLeakSecondSuccessSite bit)
        (lateLeakListenerMember true (lateLeakSecondSentHistory (bit, sender) true)
          (.secondSuccess bit) rfl) = 0 := by
  obtain ⟨sequence, approximate, converges⟩ := consistent
  let first := lateLeakFirstSuccessSite bit
  let second := lateLeakSecondSuccessSite bit
  let firstMember (label : LateLeakLabel) :
      (lateLeakModel true).InformationHistory .listener first.1 :=
    lateLeakListenerMember true (lateLeakFirstSentHistory (bit, label) true) (.firstSuccess bit)
      rfl
  let secondMember (label : LateLeakLabel) :
      (lateLeakModel true).InformationHistory .listener second.1 :=
    lateLeakListenerMember true (lateLeakSecondSentHistory (bit, label) true) (.secondSuccess bit)
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
    have ne (history : (lateLeakExecution true).History)
        (acting : history.state.actor = some .sender) (now : Bool)
        (allowed : some (LateLeakMove.opening now) ∈ lateLeakMenu true (.full history.state)) :
        lateLeakOpeningLaw (sequence n).strategy history.state (some (.opening now)) ≠ 0 :=
      opening_ne_zero mixed history acting now allowed
    have firstMass : 0 < (lateLeakModel true).informationMass (sequence n).strategy .listener
        first := by
      refine ((lateLeakModel true).informationMass_pos_iff _ _ _).mpr ⟨firstMember sender, ?_⟩
      change 0 < (lateLeakModel true).historyReachWeight (sequence n).strategy
        (lateLeakFirstSentHistory (bit, sender) true)
      rw [lateLeak_weight_first_sent]
      exact pos_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero (lateLeakPrior_ne_zero _)
        (ne (lateLeakTypeHistory true (bit, sender)) rfl false ⟨false, rfl, rfl⟩))
        (mul_ne_zero (ne (lateLeakFirstHistory (bit, sender)) rfl true ⟨true, rfl⟩)
          (lateLeakInclusion_ne_zero true)))
    have secondMass : 0 < (lateLeakModel true).informationMass (sequence n).strategy .listener
        second := by
      refine ((lateLeakModel true).informationMass_pos_iff _ _ _).mpr ⟨secondMember sender, ?_⟩
      change 0 < (lateLeakModel true).historyReachWeight (sequence n).strategy
        (lateLeakSecondSentHistory (bit, sender) true)
      rw [lateLeak_weight_second_sent]
      exact pos_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero (lateLeakPrior_ne_zero _)
        (ne (lateLeakTypeHistory true (bit, sender)) rfl false ⟨false, rfl, rfl⟩))
        (ne (lateLeakFirstHistory (bit, sender)) rfl false ⟨false, rfl⟩))
        (mul_ne_zero (ne (lateLeakSecondHistory (bit, sender)) rfl true ⟨true, rfl⟩)
          (lateLeakInclusion_ne_zero true)))
    have firstBayes := bayes .listener first firstMass
    have secondBayes := bayes .listener second secondMass
    rw [firstBayes (firstMember holder), firstBayes (firstMember sender),
      secondBayes (secondMember sender), secondBayes (secondMember holder)]
    change (lateLeakModel true).historyReachWeight (sequence n).strategy
          (lateLeakFirstSentHistory (bit, holder) true) / _ *
        ((lateLeakModel true).historyReachWeight (sequence n).strategy
          (lateLeakSecondSentHistory (bit, sender) true) / _) * _ =
      (lateLeakModel true).historyReachWeight (sequence n).strategy
          (lateLeakFirstSentHistory (bit, sender) true) / _ *
        ((lateLeakModel true).historyReachWeight (sequence n).strategy
          (lateLeakSecondSentHistory (bit, holder) true) / _) * _
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
    opening_tendsto converges (lateLeakFirstHistory (bit, label)) rfl now ⟨now, rfl⟩
  have openSecond (label : LateLeakLabel) :
      Tendsto (fun n => (opening n (.secondLate (bit, label)) true).toReal) atTop
        (nhds (lateLeakOpeningLaw A.strategy (.secondLate (bit, label))
          (some (.opening true))).toReal) :=
    opening_tendsto converges (lateLeakSecondHistory (bit, label)) rfl true ⟨true, rfl⟩
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
