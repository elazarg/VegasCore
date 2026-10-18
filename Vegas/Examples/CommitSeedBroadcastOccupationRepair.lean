/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastNativeRepair
import Interaction.ReactiveFiniteAssessment
import Interaction.ReactiveControlOccupation

/-! # Forty-eight-to-one domination of original native first-late occupation -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

abbrev SeededInputHistory (owner : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) :=
  Σ seed : Seeds, (rawMenu.information initial horizon (family seed)).InformationHistory
    owner (some (past, view))

instance fixedInputHistoryFintype (seed : Seeds) (owner : Player)
    (past : List app.PlayerEntry) (view : app.PlayerView) :
    Fintype ((rawMenu.information initial horizon (family seed)).InformationHistory
      owner (some (past, view))) := Fintype.ofFinite _

instance seededInputHistoryFintype (owner : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) : Fintype (SeededInputHistory owner past view) := by
  unfold SeededInputHistory
  infer_instance

def fixedSeedProfile (seed : Seeds)
    (profile : ∀ owner, rawModel.BehavioralPolicy owner) :
    ∀ owner, (rawMenu.information initial horizon (family seed)).BehavioralPolicy owner :=
  fun owner => rawMenu.restrictPolicy initial horizon (family seed) owner
    (rawMenu.decodeProfile initial horizon scheduler profile owner)

theorem fixedSeedProfile_decode (seed : Seeds)
    (profile : ∀ owner, rawModel.BehavioralPolicy owner) :
    rawMenu.decodeProfile initial horizon (family seed) (fixedSeedProfile seed profile) =
      rawMenu.decodeProfile initial horizon scheduler profile := by
  funext owner
  exact rawMenu.decode_restrictPolicy_of_covered initial horizon (family seed) owner _
    (rawMenu.decode_embedPolicy_covered initial horizon scheduler owner (profile owner))

theorem fixedSeedProfile_history_factor (seed : Seeds)
    (profile : ∀ owner, rawModel.BehavioralPolicy owner) (control : app.Control)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace (some control)) :
    ((rawMenu.information initial horizon (family seed)).historyReachWeight
      (fixedSeedProfile seed profile) ⟨some control, trace⟩).toReal =
        nativeResponseLikelihood (rawMenu.decodeProfile initial horizon scheduler profile)
          control.execution := by
  have factor := family_menu_history_response_factor seed (fixedSeedProfile seed profile)
    control trace
  rw [fixedSeedProfile_decode] at factor
  exact factor

def seededInputWeight (profile : ∀ owner, rawModel.BehavioralPolicy owner)
    {owner : Player} {past : List app.PlayerEntry} {view : app.PlayerView}
    (history : SeededInputHistory owner past view) : ℝ :=
  (nativeSeedLaw history.1).toReal *
    ((rawMenu.information initial horizon (family history.1)).historyReachWeight
      (fixedSeedProfile history.1 profile) history.2.1).toReal

def regularFirstLateControl (seed : Seeds) (state : app.ProtocolState) : Prop :=
  (∀ who, seed.2 who = true) ∧
    match state with
    | none => False
    | some control => ∀ who, (control.execution.recall who).length = 1 ∨
        ((control.execution.recall who).getLast?).map ReactiveApplication.PlayerEntry.action ≠
          some (⟨none⟩ : app.Action)

def regularSeededInput {owner : Player} {past : List app.PlayerEntry} {view : app.PlayerView}
    (history : SeededInputHistory owner past view) : Prop :=
  regularFirstLateControl history.1 history.2.1.state

private def repairedRecords {owner : Player} {past : List app.PlayerEntry}
    {view : app.PlayerView} (source target : SeededInputHistory owner past view) : Prop :=
  match source.2.1.state, target.2.1.state with
  | some first, some second => ∀ who,
      first.execution.recall who = second.execution.recall who ∨
        ∃ entry : app.PlayerEntry, entry.action = (⟨none⟩ : app.Action) ∧
          first.execution.recall who = second.execution.recall who ++ [entry]
  | _, _ => False

private theorem seededInput_control {owner : Player} {past : List app.PlayerEntry}
    {view : app.PlayerView} (original : SeededInputHistory owner past view) :
    ∃ remaining execution,
      ∃ trace : (rawMenu.protocol initial horizon (family original.1)).Trace
        (some ⟨remaining, some owner, execution⟩),
        original.2.1 = ⟨some ⟨remaining, some owner, execution⟩, trace⟩ ∧
          (execution.recall owner, execution.observe app owner) = (past, view) := by
  rcases original with ⟨seed, ⟨⟨state, trace⟩, informed⟩⟩
  have physical : app.observe owner state = some (past, view) :=
    (rawMenu.info initial horizon (family seed) owner trace).symm.trans informed
  cases state with
  | none => simp only [ReactiveApplication.observe, reduceCtorEq] at physical
  | some current =>
      have active : current.actor = some owner := by
        by_contra inactive
        simp only [ReactiveApplication.observe, inactive, ite_false] at physical
        cases physical
      rcases current with ⟨remaining, actor, execution⟩
      change actor = some owner at active
      subst actor
      simp only [ReactiveApplication.observe, ite_true] at physical
      exact ⟨remaining, execution, trace, rfl, Option.some.inj physical⟩

private theorem seededInputWeight_nonnegative
    (profile : ∀ owner, rawModel.BehavioralPolicy owner)
    {owner : Player} {past : List app.PlayerEntry} {view : app.PlayerView}
    (history : SeededInputHistory owner past view) : 0 ≤ seededInputWeight profile history :=
  mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

private theorem seededInput_repair_exists
    (profile : ∀ owner, rawModel.BehavioralPolicy owner)
    (owner : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (original : view.application.2.attempt = originalAttempt)
    (clock : view.application.2.native.clock = 2) (empty : view.receipts = [])
    (source : SeededInputHistory owner past view) :
    ∃ target : SeededInputHistory owner past view,
      regularSeededInput target ∧ repairedRecords source target ∧
        seededInputWeight profile source ≤ seededInputWeight profile target := by
  obtain ⟨remaining, execution, sourceTrace, sourceEq, input⟩ := seededInput_control source
  have sameView := congrArg Prod.snd input
  have originalHere : execution.application.attempt = originalAttempt :=
    (congrArg (fun localView : app.PlayerView => localView.application.2.attempt) sameView).trans
      original
  have clockHere : execution.application.current.native.clock = 2 :=
    (congrArg (fun localView : app.PlayerView => localView.application.2.native.clock)
      sameView).trans clock
  have emptyHere : execution.receipts = [] :=
    (congrArg ReactiveApplication.PlayerView.receipts sameView).trans empty
  let players := rawMenu.decodeProfile initial horizon scheduler profile
  obtain ⟨order, count, bound, actual, targetTrace, targetInput, regular, records, weight⟩ :=
    original_first_late_native_repair source.1 players remaining execution owner sourceTrace
      originalHere clockHere emptyHere
  let target : SeededInputHistory owner past view := ⟨allGoodSeed order,
    ⟨⟨some ⟨horizon - (5 + count) - 1, some owner, completeActivation actual owner⟩,
      targetTrace⟩, by
      change (rawMenu.signals initial horizon (family (allGoodSeed order))).infoOf owner
        targetTrace = some (past, view)
      rw [rawMenu.info]
      simp only [ReactiveApplication.observe, ite_true]
      exact congrArg some (targetInput.trans input)⟩⟩
  refine ⟨target, ?_, ?_, ?_⟩
  · exact ⟨fun _ => rfl, regular⟩
  · unfold repairedRecords
    rw [show source.2.1.state = some ⟨remaining, some owner, execution⟩ from
      congrArg History.state sourceEq]
    exact records
  · have sourceFactor := fixedSeedProfile_history_factor source.1 profile
      ⟨remaining, some owner, execution⟩ sourceTrace
    have targetFactor := fixedSeedProfile_history_factor (allGoodSeed order) profile
      ⟨horizon - (5 + count) - 1, some owner, completeActivation actual owner⟩ targetTrace
    change (nativeSeedLaw source.1).toReal *
        ((rawMenu.information initial horizon (family source.1)).historyReachWeight
          (fixedSeedProfile source.1 profile) source.2.1).toReal ≤
      (nativeSeedLaw (allGoodSeed order)).toReal *
        ((rawMenu.information initial horizon (family (allGoodSeed order))).historyReachWeight
          (fixedSeedProfile (allGoodSeed order) profile)
          ⟨some ⟨horizon - (5 + count) - 1, some owner, completeActivation actual owner⟩,
            targetTrace⟩).toReal
    rw [sourceEq, sourceFactor, targetFactor]
    exact weight

private theorem repaired_source_unique {owner : Player} {past : List app.PlayerEntry}
    {view : app.PlayerView} (first second target : SeededInputHistory owner past view)
    (sameSeed : first.1 = second.1)
    (firstRecords : repairedRecords first target)
    (secondRecords : repairedRecords second target) : first = second := by
  obtain ⟨firstRemaining, firstExecution, firstTrace, firstEq, firstInput⟩ :=
    seededInput_control first
  obtain ⟨secondRemaining, secondExecution, secondTrace, secondEq, secondInput⟩ :=
    seededInput_control second
  obtain ⟨targetRemaining, targetExecution, _targetTrace, targetEq, _targetInput⟩ :=
    seededInput_control target
  have firstState := congrArg History.state firstEq
  have secondState := congrArg History.state secondEq
  have targetState := congrArg History.state targetEq
  unfold repairedRecords at firstRecords secondRecords
  rw [firstState, targetState] at firstRecords
  rw [secondState, targetState] at secondRecords
  rcases first with ⟨seed, first⟩
  rcases second with ⟨other, second⟩
  change seed = other at sameSeed
  subst other
  have histories := family_replay_preimage_unique seed owner targetExecution firstExecution
    secondExecution firstRemaining secondRemaining
    (rawMenu.toRawTrace initial horizon (family seed) firstTrace)
    (rawMenu.toRawTrace initial horizon (family seed) secondTrace)
    (firstInput.trans secondInput.symm) firstRecords secondRecords
  have nativeEq : rawMenu.toRawHistory initial horizon (family seed) first.1 =
      rawMenu.toRawHistory initial horizon (family seed) second.1 := by
    rw [firstEq, secondEq]
    exact histories
  have originalEq := rawMenu.toRawHistory_injective initial horizon (family seed) nativeEq
  have subtypeEq : first = second := Subtype.ext originalEq
  cases subtypeEq
  rfl

open Classical in
/-- The actual source mass at a full input is at most forty-eight times the
mass of regular all-good prefixes at that same input, for every raw profile. -/
theorem firstLate_regular_reach_domination
    (profile : ∀ owner, rawModel.BehavioralPolicy owner)
    (owner : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (original : view.application.2.attempt = originalAttempt)
    (clock : view.application.2.native.clock = 2) (empty : view.receipts = []) :
    (∑ history : SeededInputHistory owner past view, seededInputWeight profile history) ≤
      48 * ∑ history : SeededInputHistory owner past view,
        if regularSeededInput history then seededInputWeight profile history else 0 := by
  classical
  let repair : SeededInputHistory owner past view → SeededInputHistory owner past view :=
    fun history => (seededInput_repair_exists profile owner past view original clock empty
      history).choose
  have specification (history : SeededInputHistory owner past view) :
      regularSeededInput (repair history) ∧ repairedRecords history (repair history) ∧
        seededInputWeight profile history ≤ seededInputWeight profile (repair history) :=
    (seededInput_repair_exists profile owner past view original clock empty history).choose_spec
  let tagged := fun history : SeededInputHistory owner past view => (repair history, history.1)
  have injective : Function.Injective tagged := by
    intro first second same
    have sameTarget : repair first = repair second := (Prod.mk.inj same).1
    have sameSeed : first.1 = second.1 := (Prod.mk.inj same).2
    exact repaired_source_unique first second (repair first) sameSeed
      (specification first).2.1 (sameTarget.symm ▸ (specification second).2.1)
  let targetWeight := fun history : SeededInputHistory owner past view =>
    if regularSeededInput history then seededInputWeight profile history else 0
  have nonnegative (history : SeededInputHistory owner past view) : 0 ≤ targetWeight history := by
    dsimp only [targetWeight]
    split_ifs
    · exact seededInputWeight_nonnegative profile history
    · exact le_refl _
  calc
    _ ≤ ∑ history : SeededInputHistory owner past view, targetWeight (repair history) := by
      apply Finset.sum_le_sum
      intro history _member
      simpa only [targetWeight, ite_eq_left (specification history).1] using
        (specification history).2.2
    _ = ∑ pair ∈ Finset.univ.image tagged, targetWeight pair.1 := by
      rw [Finset.sum_image (fun first _ second _ same => injective same)]
    _ ≤ ∑ pair : SeededInputHistory owner past view × Seeds, targetWeight pair.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun pair _ _ => nonnegative pair.1)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, native_seed_card, nsmul_eq_mul]
      rw [Finset.mul_sum]
      simp only [targetWeight, Nat.cast_ofNat]

open Classical in
private theorem family_input_occupation_eq (seed : Seeds)
    (profile : ∀ who, rawModel.BehavioralPolicy who)
    (owner : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (value : app.ProtocolState → ℝ) (bounded : ∀ state, |value state| ≤ 1) :
    expect (app.occupationControlLaw (family seed)
        (rawMenu.decodeProfile initial horizon scheduler profile) initial horizon)
      (fun state => if app.observe owner state = some (past, view) then value state else 0) =
      (∑ history : (rawMenu.information initial horizon (family seed)).InformationHistory
        owner (some (past, view)),
        ((rawMenu.information initial horizon (family seed)).historyReachWeight
          (fixedSeedProfile seed profile) history.1).toReal *
            value history.1.state) / horizon := by
  classical
  let gated := fun state =>
    if app.observe owner state = some (past, view) then value state else 0
  have gateBounded : ∀ state, |gated state| ≤ 1 := by
    intro state
    dsimp only [gated]
    split_ifs
    · exact bounded state
    · norm_num
  have idle : ∀ remaining execution, gated (some ⟨remaining, none, execution⟩) = 0 := by
    intro remaining execution
    simp only [gated, ReactiveApplication.observe, reduceCtorEq, ite_false]
  have unstarted : gated none = 0 := by
    simp only [gated, ReactiveApplication.observe, reduceCtorEq, ite_false]
  have occupied := rawMenu.expect_occupationControlLaw_eq_reach initial horizon (family seed)
    (fixedSeedProfile seed profile) gated (by norm_num) gateBounded idle unstarted
  rw [fixedSeedProfile_decode] at occupied
  change expect (app.occupationControlLaw (family seed)
    (rawMenu.decodeProfile initial horizon scheduler profile)
      initial horizon) gated = _
  rw [occupied]
  congr 1
  calc
    _ = ∑ history : (rawMenu.protocol initial horizon (family seed)).History,
        if (rawMenu.information initial horizon (family seed)).infoOf owner history.trace =
            some (past, view) then
          ((rawMenu.information initial horizon (family seed)).historyReachWeight
            (fixedSeedProfile seed profile) history).toReal * value history.state else 0 := by
      apply Finset.sum_congr rfl
      intro history _member
      have observed := rawMenu.info initial horizon (family seed) owner history.trace
      change (rawMenu.information initial horizon (family seed)).infoOf owner history.trace =
        app.observe owner history.state at observed
      dsimp only [gated]
      rw [← observed]
      split_ifs <;> simp only [mul_zero]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _

open Classical in
/-- Both sides use the same original joint experiment: draw the immutable
seed once, then observe a uniformly chosen genuine native command decision. -/
theorem firstLate_regular_occupation_domination
    (profile : ∀ who, rawModel.BehavioralPolicy who)
    (owner : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (original : view.application.2.attempt = originalAttempt)
    (clock : view.application.2.native.clock = 2) (empty : view.receipts = []) :
    expect nativeSeedLaw (fun seed =>
      expect (app.occupationControlLaw (family seed)
        (rawMenu.decodeProfile initial horizon scheduler profile) initial horizon)
        (fun state => if app.observe owner state = some (past, view) then (1 : ℝ) else 0)) ≤
      48 * expect nativeSeedLaw (fun seed =>
        expect (app.occupationControlLaw (family seed)
          (rawMenu.decodeProfile initial horizon scheduler profile) initial horizon)
          (fun state => if app.observe owner state = some (past, view) then
            if regularFirstLateControl seed state then (1 : ℝ) else 0 else 0)) := by
  classical
  have sourceEq : expect nativeSeedLaw (fun seed =>
      expect (app.occupationControlLaw (family seed)
        (rawMenu.decodeProfile initial horizon scheduler profile) initial horizon)
        (fun state => if app.observe owner state = some (past, view) then (1 : ℝ) else 0)) =
      (∑ history : SeededInputHistory owner past view, seededInputWeight profile history) /
        horizon := by
    change (∑' seed, (nativeSeedLaw seed).toReal *
      expect (app.occupationControlLaw (family seed)
        (rawMenu.decodeProfile initial horizon scheduler profile) initial horizon)
        (fun state => if app.observe owner state = some (past, view) then (1 : ℝ) else 0)) = _
    rw [tsum_fintype]
    have pointwise (seed : Seeds) := family_input_occupation_eq seed profile owner past view
      (fun _ => (1 : ℝ)) (by intro state; norm_num)
    simp_rw [pointwise]
    simp only [mul_one]
    rw [Fintype.sum_sigma, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro seed _member
    have sums : (nativeSeedLaw seed).toReal *
        (∑ history : (rawMenu.information initial horizon (family seed)).InformationHistory
          owner (some (past, view)),
          ((rawMenu.information initial horizon (family seed)).historyReachWeight
            (fixedSeedProfile seed profile) history.1).toReal) =
        ∑ history : (rawMenu.information initial horizon (family seed)).InformationHistory
          owner (some (past, view)),
          (nativeSeedLaw seed).toReal *
            ((rawMenu.information initial horizon (family seed)).historyReachWeight
              (fixedSeedProfile seed profile) history.1).toReal := Finset.mul_sum ..
    exact (mul_div_assoc _ _ _).symm.trans
      (congrArg (fun value : ℝ => value / (horizon : ℝ)) sums)
  have targetEq : expect nativeSeedLaw (fun seed =>
      expect (app.occupationControlLaw (family seed)
        (rawMenu.decodeProfile initial horizon scheduler profile) initial horizon)
        (fun state => if app.observe owner state = some (past, view) then
          if regularFirstLateControl seed state then (1 : ℝ) else 0 else 0)) =
      (∑ history : SeededInputHistory owner past view,
        if regularSeededInput history then seededInputWeight profile history else 0) / horizon := by
    change (∑' seed, (nativeSeedLaw seed).toReal *
      expect (app.occupationControlLaw (family seed)
        (rawMenu.decodeProfile initial horizon scheduler profile) initial horizon)
        (fun state => if app.observe owner state = some (past, view) then
          if regularFirstLateControl seed state then (1 : ℝ) else 0 else 0)) = _
    rw [tsum_fintype]
    have pointwise (seed : Seeds) := family_input_occupation_eq seed profile owner past view
      (fun state => if regularFirstLateControl seed state then (1 : ℝ) else 0)
        (by intro state; split_ifs <;> norm_num)
    simp_rw [pointwise]
    rw [Fintype.sum_sigma, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro seed _member
    have factors : (∑ history :
        (rawMenu.information initial horizon (family seed)).InformationHistory
          owner (some (past, view)),
        if regularFirstLateControl seed history.1.state then
          (nativeSeedLaw seed).toReal *
            ((rawMenu.information initial horizon (family seed)).historyReachWeight
              (fixedSeedProfile seed profile) history.1).toReal else 0) =
        (nativeSeedLaw seed).toReal * ∑ history :
          (rawMenu.information initial horizon (family seed)).InformationHistory
            owner (some (past, view)),
          ((rawMenu.information initial horizon (family seed)).historyReachWeight
            (fixedSeedProfile seed profile) history.1).toReal *
              (if regularFirstLateControl seed history.1.state then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro history _member
      split_ifs <;> ring
    simp only [seededInputWeight, regularSeededInput]
    rw [factors]
    ring
  rw [sourceEq, targetEq]
  calc
    _ ≤ (48 * ∑ history : SeededInputHistory owner past view,
        if regularSeededInput history then seededInputWeight profile history else 0) / horizon :=
      div_le_div_of_nonneg_right
        (firstLate_regular_reach_domination profile owner past view original clock empty)
        (Nat.cast_nonneg _)
    _ = _ := by ring

end Vegas.Examples.CommitSeedBroadcast
