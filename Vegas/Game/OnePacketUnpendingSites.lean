/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketValueTransport
import Vegas.Game.OnePacketSilenceMasses

/-! # Sites without a pending event

At a decision site of who with no pending event of who, either who has no turn,
or its turn's event was already submitted for, so the as-if-honest choice and
the slot tier are silence, and so is every compared choice: a compared choice
sends only for the event at who's own turn, and the one-packet menu offers no
second packet for an event (`Vegas.compared_eq_silence_of_unpending`). So the
slot-trembled prescribed component is silence up to the uniform tier, and every
compared choice has the successful value of the prescribed component, up to
twice the cube of the scale times the payoff range
(`Vegas.abs_siteSuccess_sub_prescribed_le_of_unpending`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

variable {setup leaks bounds horizon scheduler} in
omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **The state of an unpending site.** A history of a decision site of who
with no pending event of who ends at a control with who's recall and view,
where who has no turn, or has a turn whose event its recall has submitted for. -/
theorem unpending_cases {who : Player} {site : (onePacketN).InformationSite who}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (unpending : pendingEvent setup leaks who site.1 = none)
    (history : (onePacketN).InformationHistory who site.1) :
    ∃ control : (application setup leaks).Control, history.1.state = some control ∧
      control.execution.recall who = past ∧
      control.execution.observe (application setup leaks) who = view ∧
      (view.application.publicView.ownTurn? who = none ∨
        ∃ event, view.application.publicView.ownTurn? who = some event ∧
          (runtime setup).eventRecorded leaks past event = true) := by
  obtain ⟨⟨state, trace⟩, info⟩ := history
  have seen := info.trans atSite
  rw [onePacket_infoOf] at seen
  cases state with
  | none => cases seen
  | some control =>
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at seen
        obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj (Option.some.inj seen)
        refine ⟨control, rfl, pastEq, viewEq, ?_⟩
        rw [atSite] at unpending
        cases turn : view.application.publicView.ownTurn? who with
        | none => exact Or.inl rfl
        | some event =>
            refine Or.inr ⟨event, rfl, ?_⟩
            simp only [pendingEvent, turn, Option.filter_some] at unpending
            cases recorded : (runtime setup).eventRecorded leaks past event with
            | true => rfl
            | false => simp [recorded] at unpending
      · simp [ReactiveApplication.observe, active] at seen

variable {setup leaks bounds horizon scheduler} in
omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **Compared choices are silence at an unpending site.** At a decision site of
who with no pending event of who, every compared choice is silence. -/
theorem compared_eq_silence_of_unpending {who : Player} {site : (onePacketN).InformationSite who}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (unpending : pendingEvent setup leaks who site.1 = none)
    (history : (onePacketN).InformationHistory who site.1)
    (choice : (onePacketN).Choice who site.1)
    (marked : onePacketCompared setup leaks bounds horizon scheduler who site choice) :
    choice.1 = some ⟨none⟩ := by
  obtain ⟨control, state, pastEq, viewEq, cases⟩ := unpending_cases atSite unpending history
  obtain ⟨response, chosen, member⟩ := choice_response setup leaks bounds horizon scheduler site
    atSite choice
  rw [chosen]
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material =>
      exfalso
      obtain ⟨event, submitted⟩ := submittedEvent_of_transmits setup leaks bounds member
        (material := material) rfl
      obtain ⟨turnPast, turnView, turnSite, turn⟩ := (marked.2 _ chosen).2 event submitted
      rw [atSite] at turnSite
      obtain ⟨_, turnViewEq⟩ := Prod.mk.inj (Option.some.inj turnSite)
      subst turnViewEq
      rcases cases with noTurn | ⟨namedEvent, turnSome, recorded⟩
      · rw [noTurn] at turn
        cases turn
      · rw [turnSome] at turn
        cases Option.some.inj turn
        have trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
            horizon scheduler).Trace (some control) := state ▸ history.1.trace
        subst pastEq viewEq
        exact onePacket_recorded_not_offered trace who _ recorded _ submitted member

/-- **Compared choices succeed like the prescribed component at an unpending
site.** With bounded utilities, at a decision site of who with no pending event
of who, every compared choice has, under every assessment, the successful value
of the slot-trembled prescribed component up to twice the cube of the scale
times the payoff range. -/
theorem abs_siteSuccess_sub_prescribed_le_of_unpending
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1) (n : ℕ)
    (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (unpending : pendingEvent setup leaks who site.1 = none)
    (history : (onePacketN).InformationHistory who site.1)
    (choice : (onePacketN).Choice who site.1)
    (marked : onePacketCompared setup leaks bounds horizon scheduler who site choice) :
    |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment site (PMF.pure choice) -
      onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment site (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale
          scale_pos scale_le_one n ((onePacketN).agentAt site))| ≤
      2 * scale n ^ 3 * (max 0 (max (excludedPayoff who) (upperUtility who)) -
        min 0 (min (excludedPayoff who) (lowerUtility who))) := by
  classical
  let menu := bounds.onePacketMenu (runtime setup) leaks
  have bounded := menu.bounded (initialLaw setup) horizon scheduler
  have actsOnce := (menu.decisionRecall (initialLaw setup) horizon
    scheduler).actsOnceWhereItMatters
  let range := max 0 (max (excludedPayoff who) (upperUtility who)) -
    min 0 (min (excludedPayoff who) (lowerUtility who))
  have silent := compared_eq_silence_of_unpending atSite unpending history choice marked
  obtain ⟨control, controlState, pastEq, viewEq, cases⟩ :=
    unpending_cases atSite unpending history
  -- The success of any law is bounded by the range.
  have successBounded : ∀ law, |onePacketSiteSuccess setup leaks bounds horizon scheduler
      parameter utility excludedPayoff assessment site law| ≤ range := by
    intro law
    have rangeNonneg : 0 ≤ range := by
      have := le_max_left 0 (max (excludedPayoff who) (upperUtility who))
      have := min_le_left 0 (min (excludedPayoff who) (lowerUtility who))
      simp only [range]
      linarith
    unfold onePacketSiteSuccess localSuccessValue
    refine expect_abs_le_of_bounded rangeNonneg fun final => ?_
    split
    · simpa using rangeNonneg
    · exact abs_exclusionReadoutUtility_le setup parameter utility excludedPayoff lowerUtility
        upperUtility lower_le le_upper _ who
  -- Every compared choice is silence, and the prescribed law is silence up to the
  -- uniform tier.
  obtain ⟨info, decision⟩ := site
  change info = some (past, view) at atSite
  subst atSite
  have choiceEq : choice = silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler
      who (some (past, view)) := by
    apply Subtype.ext
    rw [silent]
    unfold silenceChoice responseChoice
    dsimp only
    split <;> rfl
  have honestSilent : honestChoice setup leaks bounds (initialLaw setup) horizon scheduler
      (sequence n) who (some (past, view)) = PMF.pure (silenceChoice setup leaks bounds
        (initialLaw setup) horizon scheduler who (some (past, view))) ∧
      slotChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who
        (some (past, view)) = PMF.pure (silenceChoice setup leaks bounds
        (initialLaw setup) horizon scheduler who (some (past, view))) := by
    rcases cases with noTurn | ⟨event, turn, recorded⟩
    · exact ⟨honestChoice_silence_of_noTurn (sequence n) who past view noTurn,
        slotChoice_silence_of_noTurn (sequence n) who past view noTurn⟩
    · have trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
          horizon scheduler).Trace (some control) := controlState ▸ history.1.trace
      subst pastEq viewEq
      exact ⟨honestChoice_silence_of_recorded (sequence n) trace who event turn recorded,
        slotChoice_silence_of_recorded (sequence n) trace who event turn recorded⟩
  have prescribedEq : onePacketPrescribed setup leaks bounds horizon scheduler sequence scale
      scale_pos scale_le_one n ((onePacketN).agentAt ⟨some (past, view), decision⟩) =
      mix (scale n ^ 3) (pow_nonneg (scale_pos n).le 3) (pow_le_one₀ (scale_pos n).le
        (scale_le_one n))
        ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy (initialLaw setup) horizon
          scheduler who (some (past, view)))
        (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
          (some (past, view)))) := by
    change slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler (scale n)
      (scale_pos n).le (scale_le_one n) who (some (past, view))
      (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who
        (some (past, view)))
      (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        (some (past, view))))
      (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who
        (some (past, view))) = _
    rw [honestSilent.1, honestSilent.2]
    unfold slotTrembledChoice
    rw [mix_self, mix_self]
  rw [prescribedEq, choiceEq]
  have linear : onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
      excludedPayoff assessment ⟨some (past, view), decision⟩
      (mix (scale n ^ 3) (pow_nonneg (scale_pos n).le 3) (pow_le_one₀ (scale_pos n).le
        (scale_le_one n))
        ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy (initialLaw setup) horizon
          scheduler who (some (past, view)))
        (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
          (some (past, view))))) =
      scale n ^ 3 * onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
          excludedPayoff assessment ⟨some (past, view), decision⟩
          ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy (initialLaw setup) horizon
            scheduler who (some (past, view))) +
        (1 - scale n ^ 3) * onePacketSiteSuccess setup leaks bounds horizon scheduler parameter
          utility excludedPayoff assessment ⟨some (past, view), decision⟩
          (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
            (some (past, view)))) := by
    have asValue : ∀ law, onePacketSiteSuccess setup leaks bounds horizon scheduler parameter
        utility excludedPayoff assessment ⟨some (past, view), decision⟩ law =
        localValue (2 * horizon + 1) id (fun history (_ : Player) =>
          if history ∈ onePacketFailed setup leaks bounds horizon scheduler
            ((onePacketN).agentAt ⟨some (past, view), decision⟩) then 0 else
          payoffComponent setup (readoutExclusion setup leaks bounds (initialLaw setup) horizon
            scheduler parameter utility excludedPayoff history) who) assessment
          ⟨some (past, view), decision⟩ law := fun law => by
      unfold onePacketSiteSuccess localSuccessValue
      rw [localValue_eq_expect_localRun]
      congr 1
    rw [asValue, asValue, asValue]
    exact localValue_mix _ _ _ _ _ bounded actsOnce _ _ _ _ _
  rw [linear]
  have uniformBound := abs_le.mp (successBounded ((bounds.onePacketMenu (runtime setup)
    leaks).uniformPolicy (initialLaw setup) horizon scheduler who (some (past, view))))
  have silenceBound := abs_le.mp (successBounded (PMF.pure (silenceChoice setup leaks bounds
    (initialLaw setup) horizon scheduler who (some (past, view)))))
  have cubeNonneg : 0 ≤ scale n ^ 3 := pow_nonneg (scale_pos n).le 3
  rw [show ∀ a b : ℝ, b - (scale n ^ 3 * a + (1 - scale n ^ 3) * b) = scale n ^ 3 * (b - a)
    from fun a b => by ring, abs_mul, abs_of_nonneg cubeNonneg]
  have difference : |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
      excludedPayoff assessment ⟨some (past, view), decision⟩ (PMF.pure (silenceChoice setup
        leaks bounds (initialLaw setup) horizon scheduler who (some (past, view)))) -
      onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment ⟨some (past, view), decision⟩ ((bounds.onePacketMenu (runtime setup)
          leaks).uniformPolicy (initialLaw setup) horizon scheduler who (some (past, view)))| ≤
      2 * range := abs_le.mpr ⟨by linarith, by linarith⟩
  calc _ ≤ scale n ^ 3 * (2 * range) := mul_le_mul_of_nonneg_left difference cubeNonneg
    _ = _ := by ring

end Vegas
