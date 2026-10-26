/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDelivery

/-! # Value-free sending of a slot-trembled late component

At a player's turn, every response of a slot-trembled mixture of late options,
outside its uniform tier, keeps silence or commits an as-if-honest source
choice at a slot. Let a function of responses vanish at silence, and at each
slot the component can draw be, up to `ε`, a factor depending on the slot alone times a function of
the committed choice that is centered under the as-if-honest law. Then the
expectation of the function under the component is at most the cube of the
scale times its bound plus `ε`
(`Vegas.abs_expect_slotTrembled_lateChoice_le`): silence contributes nothing,
and at every slot the value of the committed choice is drawn from the
as-if-honest law independently of the slot.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {initial : PMF (application setup runtime leaks).State}
  {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
/-- A function within `ε` of a factor times a centered bounded function has
expectation at most `ε`. -/
private theorem abs_expect_le_of_centered {α : Type*} (law : PMF α) (value centered : α → ℝ)
    (factor : ℝ) {bound ε : ℝ} (valueBounded : ∀ a, |value a| ≤ bound)
    (centeredBounded : ∀ a, |centered a| ≤ bound) (mean : expect law centered = 0)
    (near : ∀ a ∈ law.support, |value a - factor * centered a| ≤ ε) :
    |expect law value| ≤ ε := by
  classical
  obtain ⟨witness, witnessed⟩ := law.support_nonempty
  have nonnegative : 0 ≤ ε := (abs_nonneg _).trans (near witness witnessed)
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans (valueBounded witness)
  have valueIntegrable : PayoffIntegrable law value :=
    payoffIntegrable_of_bounded law value valueBounded
  have scaledIntegrable : PayoffIntegrable law fun a => factor * centered a :=
    payoffIntegrable_of_bounded law _ (C := |factor| * bound) fun a => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (centeredBounded a) (abs_nonneg _)
  have split : expect law value =
      expect law (fun a => value a - factor * centered a) + factor * expect law centered := by
    rw [← expect_const_mul, ← expect_add (payoffIntegrable_sub valueIntegrable scaledIntegrable)
      scaledIntegrable]
    congr 1
    funext a
    ring
  rw [split, mean, mul_zero, add_zero, expect_congr_on_support (g := fun a =>
    if a ∈ law.support then value a - factor * centered a else 0)
    (fun a member => by rw [ite_eq_left member ..])]
  apply expect_abs_le_of_bounded nonnegative
  intro a
  split
  · rename_i member
    exact near a member
  · rw [abs_zero]
    exact nonnegative

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
/-- A function at most `ε` in absolute value on the support has expectation at
most `ε`. -/
private theorem abs_expect_le_of_support {α : Type*} (law : PMF α) (value : α → ℝ) {ε : ℝ}
    (near : ∀ a ∈ law.support, |value a| ≤ ε) : |expect law value| ≤ ε := by
  classical
  obtain ⟨witness, witnessed⟩ := law.support_nonempty
  have nonnegative : 0 ≤ ε := (abs_nonneg _).trans (near witness witnessed)
  rw [expect_congr_on_support (g := fun a => if a ∈ law.support then value a else 0)
    (fun a member => by rw [ite_eq_left member ..])]
  apply expect_abs_le_of_bounded nonnegative
  intro a
  split
  · rename_i member
    exact near a member
  · rw [abs_zero]
    exact nonnegative

/-- The response a one-packet choice performs. -/
abbrev choiceResponse {who : Player} {info : (application setup runtime leaks).Info}
    (choice : (onePacketModel setup runtime leaks bounds initial horizon scheduler).Choice who
      info) :
    (application setup runtime leaks).Action :=
  choice.1.getD ⟨none⟩

/-- **Value-free sending of a late component.** At the player's turn `event`
at a player view, let a function of responses bounded by `bound` vanish at
silence, and let it be, at each slot below a limit that bounds the slot tier and
the options, within `ε` of a factor depending on the
slot alone times `centered` of the committed as-if-honest choice, where
`centered` is bounded and has mean zero under the as-if-honest law. Then the
slot-trembled mixture of late options, with silence as its alternative and the
slot tier, gives the function an expectation at most the cube of the scale
times `bound` plus `ε`. -/
theorem abs_expect_slotTrembled_lateChoice_le
    (assessment : setup.intendedModel.BehavioralAssessment) {scale : ℝ} (nonnegative : 0 ≤ scale)
    (le_one : scale ≤ 1) {slots : Nat} (options : PMF (LateOption slots)) (who : Player)
    (past : List (application setup runtime leaks).PlayerEntry)
    (view : (application setup runtime leaks).PlayerView) (event : (graph setup).EventId)
    (turn : view.application.publicView.ownTurn? who = some event)
    (value : (application setup runtime leaks).Action → ℝ) (centered : Option (OwnAction Player L)
      → ℝ)
    {bound ε : ℝ} (valueBounded : ∀ response, |value response| ≤ bound)
    (centeredBounded : ∀ choice, |centered choice| ≤ bound)
    (mean : expect (asIfHonestProfile setup runtime leaks assessment who (some (past, view)))
      centered = 0)
    (silent : value ⟨none⟩ = 0) (slotLimit : Nat)
    (tierBelow : ∀ slot ∈ trembleSlots setup bounds, slot < slotLimit)
    (optionsBelow : ∀ slot : Fin slots, some slot ∈ options.support → slot.val < slotLimit)
    (sending : ∀ slot < slotLimit, ∃ factor : ℝ, ∀ choice ∈ (asIfHonestProfile setup runtime leaks
        assessment who (some (past, view))).support,
      |value (choiceResponse (runtime := runtime) (responseChoice setup runtime leaks bounds
        initial horizon scheduler who
          (some (past, view)) (slotResponse setup runtime leaks who past view event slot choice))) -
        factor * centered choice| ≤ ε) :
    |expect (slotTrembledChoice setup runtime leaks bounds initial horizon scheduler scale
      nonnegative
        le_one who (some (past, view))
        (options.bind (lateChoice setup runtime leaks bounds initial horizon scheduler assessment
          who
          (some (past, view))))
        (PMF.pure (silenceChoice setup runtime leaks bounds initial horizon scheduler who
          (some (past, view))))
        (slotChoice setup runtime leaks bounds initial horizon scheduler assessment who
          (some (past, view))))
      (fun choice => value (choiceResponse (runtime := runtime) choice))| ≤ scale ^ 3 * bound + ε
        := by
  let honest := asIfHonestProfile setup runtime leaks assessment who (some (past, view))
  let committed := fun (slot : Nat) (choice : Option (OwnAction Player L)) =>
    value (choiceResponse (runtime := runtime) (responseChoice setup runtime leaks bounds initial
      horizon scheduler who
      (some (past, view)) (slotResponse setup runtime leaks who past view event slot choice)))
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans (valueBounded ⟨none⟩)
  have εNonneg : 0 ≤ ε := by
    obtain ⟨factor, near⟩ := sending 0 (tierBelow 0 (Finset.mem_range.mpr
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _))))
    obtain ⟨witness, witnessed⟩ := honest.support_nonempty
    exact (abs_nonneg _).trans (near witness witnessed)
  have choiceBounded : ∀ choice : (onePacketModel setup runtime leaks bounds initial horizon
      scheduler).Choice who (some (past, view)), |value (choiceResponse (runtime := runtime)
        choice)| ≤ bound :=
    fun choice => valueBounded _
  have perSlot : ∀ slot < slotLimit, |expect honest (committed slot)| ≤ ε := by
    intro slot below
    obtain ⟨factor, near⟩ := sending slot below
    exact abs_expect_le_of_centered honest (committed slot) centered factor
      (fun choice => valueBounded _) centeredBounded mean near
  have silentChoice : ∀ response, response = (⟨none⟩ : (application setup runtime leaks).Action) →
      value (choiceResponse (runtime := runtime) (responseChoice setup runtime leaks bounds
        initial horizon scheduler who
        (some (past, view)) response)) = 0 := by
    intro response same
    subst same
    by_cases member : (⟨none⟩ : (application setup runtime leaks).Action) ∈
      bounds.onePacketActions runtime leaks who past view
    · simp only [responseChoice, member, ↓reduceDIte, choiceResponse, Option.getD_some, silent]
    · simp only [responseChoice, member, ↓reduceDIte, choiceResponse, Option.getD_some, silent]
  -- The late options.
  have mainBound : |expect (options.bind (lateChoice setup runtime leaks bounds initial horizon
      scheduler assessment who (some (past, view)))) (fun choice => value (choiceResponse (runtime
        := runtime) choice))|
      ≤ ε := by
    rw [expect_bind_tower_bounded _ _ _ choiceBounded]
    apply abs_expect_le_of_support
    intro option member
    cases option with
    | none =>
        simp only [lateChoice, lateResponse, PMF.pure_map, expect_pure]
        rw [silentChoice _ rfl, abs_zero]
        exact εNonneg
    | some slot =>
        simp only [lateChoice, lateResponse, turn]
        rw [PMF.map_comp, expect_map]
        exact perSlot slot.val (optionsBelow slot member)
  -- The slot tier.
  have slotBound : |expect (slotChoice setup runtime leaks bounds initial horizon scheduler
    assessment
      who (some (past, view))) (fun choice => value (choiceResponse (runtime := runtime) choice))|
        ≤ ε := by
    change |expect ((slotTierResponse setup runtime leaks bounds assessment who past view).map _)
      _| ≤ ε
    unfold slotTierResponse
    rw [turn]
    dsimp only
    rw [PMF.map_comp, expect_map, slotPairs]
    simp only [Function.comp_def]
    rw [expect_bind_tower_bounded _ _ _ (fun pair => valueBounded _)]
    apply abs_expect_le_of_support
    intro slot member
    rw [expect_map]
    exact perSlot slot (tierBelow slot ((PMF.mem_support_uniformOfFinset_iff _ _).mp member))
  have silenceZero : value (choiceResponse (runtime := runtime) (silenceChoice setup runtime leaks
    bounds initial horizon
      scheduler who (some (past, view)))) = 0 := silentChoice _ rfl
  have uniformBound := expect_abs_le_of_bounded (μ := (bounds.onePacketMenu runtime
    leaks).uniformPolicy initial horizon scheduler who (some (past, view))) boundNonneg
    choiceBounded
  unfold slotTrembledChoice
  rw [expect_mix_of_finite, expect_mix_of_finite, expect_mix_of_finite, expect_pure, silenceZero]
  set uniform := expect ((bounds.onePacketMenu runtime leaks).uniformPolicy initial
    horizon scheduler who (some (past, view))) fun choice => value (choiceResponse (runtime :=
      runtime) choice)
  set main := expect (options.bind (lateChoice setup runtime leaks bounds initial horizon scheduler
    assessment who (some (past, view)))) fun choice => value (choiceResponse (runtime := runtime)
      choice)
  set tier := expect (slotChoice setup runtime leaks bounds initial horizon scheduler assessment who
    (some (past, view))) fun choice => value (choiceResponse (runtime := runtime) choice)
  have cube : 0 ≤ scale ^ 3 := pow_nonneg nonnegative 3
  have cubeLe : scale ^ 3 ≤ 1 := pow_le_one₀ nonnegative le_one
  have square : 0 ≤ scale ^ 2 := sq_nonneg scale
  have squareLe : scale ^ 2 ≤ 1 := pow_le_one₀ nonnegative le_one
  have inner : |scale ^ 2 * tier + (1 - scale ^ 2) * (scale * 0 + (1 - scale) * main)| ≤ ε := by
    rw [mul_zero, zero_add]
    calc _ ≤ |scale ^ 2 * tier| + |(1 - scale ^ 2) * ((1 - scale) * main)| := abs_add_le _ _
      _ = scale ^ 2 * |tier| + (1 - scale ^ 2) * ((1 - scale) * |main|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg square,
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - scale ^ 2),
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - scale)]
      _ ≤ scale ^ 2 * ε + (1 - scale ^ 2) * ((1 - scale) * ε) :=
          add_le_add (mul_le_mul_of_nonneg_left slotBound square)
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left mainBound (by linarith))
              (by linarith))
      _ ≤ ε := by
          have shrink : (1 - scale ^ 2) * ((1 - scale) * ε) ≤ (1 - scale ^ 2) * ε :=
            mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
          linarith
  calc _ ≤ |scale ^ 3 * uniform| + |(1 - scale ^ 3) *
        (scale ^ 2 * tier + (1 - scale ^ 2) * (scale * 0 + (1 - scale) * main))| := abs_add_le _ _
    _ = scale ^ 3 * |uniform| + (1 - scale ^ 3) *
        |scale ^ 2 * tier + (1 - scale ^ 2) * (scale * 0 + (1 - scale) * main)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg cube,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - scale ^ 3)]
    _ ≤ scale ^ 3 * bound + (1 - scale ^ 3) * ε :=
        add_le_add (mul_le_mul_of_nonneg_left uniformBound cube)
          (mul_le_mul_of_nonneg_left inner (by linarith))
    _ ≤ scale ^ 3 * bound + ε := by nlinarith

end Vegas
