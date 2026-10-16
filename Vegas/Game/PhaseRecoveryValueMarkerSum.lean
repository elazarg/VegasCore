/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueNativeMark
import Vegas.Game.PhaseContinuationMarker
import Interaction.ReactiveRecallEntries
import Mathlib.Data.List.Perm.Basic
import Interaction.ReactiveMarkedReach

/-! # Averaging the actual new binding-send marker positions -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

private theorem ownPlayFrom_origin {Principal : Type} (app : ReactiveApplication Principal)
    (past records : List app.PlayerEntry) (record : app.Info × app.Action)
    (member : record ∈ app.ownPlayFrom past records) :
    ∃ before entry after, records = before ++ entry :: after ∧
      record = (some (past ++ before, entry.beforeView), entry.action) := by
  induction records generalizing past with
  | nil => cases member
  | cons head rest ih =>
      simp only [ReactiveApplication.ownPlayFrom, List.mem_append, List.mem_singleton] at member
      rcases member with member | same
      · obtain ⟨before, entry, after, split, recordEq⟩ := ih (past ++ [head]) member
        refine ⟨head :: before, entry, after, ?_, ?_⟩
        · simp only [List.cons_append, split]
        · simpa only [List.append_assoc, List.singleton_append] using recordEq
      · exact ⟨[], head, rest, rfl, by simpa only [List.append_nil] using same⟩

private theorem ownPlayFrom_probability {Principal : Type}
    (app : ReactiveApplication Principal) (past records : List app.PlayerEntry)
    (law : app.Info → app.Action → ℝ) :
    ((app.ownPlayFrom past records).map (fun record => law record.1 record.2)).prod =
      ((app.privateTranscriptFrom past records).map (fun record =>
        law (some record.1) record.2)).prod := by
  induction records generalizing past with
  | nil => rfl
  | cons head rest ih =>
      simp only [ReactiveApplication.ownPlayFrom, ReactiveApplication.privateTranscriptFrom,
        List.map_append, List.prod_append, ih, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one]

private theorem fin_product_without {α : Type} (records : List α) (index : Fin records.length)
    (law : α → ℝ) :
    (∏ other : Fin records.length, if other = index then 1 else law records[other.val]) =
      ((records.eraseIdx index.val).map law).prod := by
  induction records with
  | nil => exact Fin.elim0 index
  | cons head rest ih =>
      simp only [List.length_cons]
      cases index using Fin.cases with
      | zero =>
          rw [Fin.prod_univ_succ]
          simp only [Fin.val_zero, ↓reduceIte, one_mul,
            Fin.succ_ne_zero, Fin.val_succ, List.getElem_cons_succ,
            List.eraseIdx_zero]
          have product :=
            (List.prod_ofFn (f := fun other : Fin rest.length => law rest[other.val])).symm
          simpa only [List.ofFn_comp', List.ofFn_getElem, List.tail_cons] using product
      | succ index =>
          have different : (0 : Fin (rest.length + 1)) ≠ index.succ :=
            Ne.symm (Fin.succ_ne_zero _)
          rw [Fin.prod_univ_succ]
          simp only [Fin.val_zero, List.getElem_cons_zero, ite_eq_right different,
            Fin.succ_inj, Fin.val_succ, List.getElem_cons_succ,
            List.eraseIdx_cons_succ, List.map_cons, List.prod_cons]
          rw [ih index]

private theorem erased_product_of_split {α : Type} (records : List α)
    (index : Fin records.length) (before after : List α) (marked : α)
    (split : records = before ++ marked :: after) (named : records[index.val] = marked)
    (law : α → ℝ) :
    (∏ other ∈ Finset.univ.erase index, law records[other.val]) =
      (before.map law).prod * (after.map law).prod := by
  classical
  let modified := fun other : Fin records.length =>
    if other = index then (1 : ℝ) else law records[other.val]
  have omitted : (∏ other ∈ Finset.univ.erase index, law records[other.val]) =
      ∏ other : Fin records.length, modified other := by
    rw [← Finset.prod_erase Finset.univ (f := modified) (a := index)
      (by simp only [modified, ↓reduceIte])]
    apply Finset.prod_congr rfl
    intro other member
    exact (ite_eq_right (Finset.mem_erase.mp member).1).symm
  rw [omitted, fin_product_without]
  have inside : before.length < records.length := by
    rw [split, List.length_append, List.length_cons]
    omega
  have nth : records[before.length] = marked := by simp [split]
  have same : records[index.val]? = records[before.length]? := by
    rw [List.getElem?_eq_getElem index.isLt, List.getElem?_eq_getElem inside, named, nth]
  have perm : List.Perm (records.eraseIdx index.val) (records.eraseIdx before.length) :=
    (List.Perm.refl records).eraseIdx_of_getElem?_eq same
  have deletion (prior : List α) :
      (prior ++ marked :: after).eraseIdx prior.length = prior ++ after := by
    induction prior with
    | nil => rfl
    | cons head rest ih =>
        simp only [List.cons_append, List.length_cons, List.eraseIdx_cons_succ, ih]
  rw [(perm.map law).prod_eq, split, deletion before, List.map_append, List.prod_append]

private theorem sigma_erased_product {Owner : Type} [Fintype Owner] [DecidableEq Owner]
    (count : Owner → Nat) (selected : Σ owner, Fin (count owner))
    (atom : (Σ owner, Fin (count owner)) → ℝ) (raw : ℝ) :
    raw * (∏ other ∈ Finset.univ.erase selected, atom other) =
      (raw * ∏ other ∈ Finset.univ.erase selected.2, atom ⟨selected.1, other⟩) *
        ∏ owner ∈ Finset.univ.erase selected.1, ∏ index, atom ⟨owner, index⟩ := by
  classical
  let changed := fun other => if other = selected then raw else atom other
  have whole : raw * (∏ other ∈ Finset.univ.erase selected, atom other) =
      ∏ other, changed other := by
    rw [← Finset.mul_prod_erase Finset.univ changed (Finset.mem_univ selected)]
    congr 1
    · exact (ite_eq_left rfl).symm
    · apply Finset.prod_congr rfl
      intro other member
      exact (ite_eq_right (Finset.mem_erase.mp member).1).symm
  rw [whole, Fintype.prod_sigma]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun owner => ∏ index, changed ⟨owner, index⟩) (Finset.mem_univ selected.1)]
  congr 1
  · rw [← Finset.mul_prod_erase Finset.univ
      (fun index => changed ⟨selected.1, index⟩) (Finset.mem_univ selected.2)]
    congr 1
    · simp only [changed, Sigma.eta, ↓reduceIte]
    · apply Finset.prod_congr rfl
      intro other member
      have different : (⟨selected.1, other⟩ : Σ owner, Fin (count owner)) ≠ selected := by
        intro same
        cases selected with
        | mk owner index =>
            have equal : other = index := by
              simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using same
            exact (Finset.mem_erase.mp member).1 equal
      exact ite_eq_right different
  · apply Finset.prod_congr rfl
    intro owner member
    apply Finset.prod_congr rfl
    intro index _inside
    have different : (⟨owner, index⟩ : Σ owner, Fin (count owner)) ≠ selected := by
      intro same
      exact (Finset.mem_erase.mp member).1 (congrArg Sigma.fst same)
    exact ite_eq_right different

private theorem marker_integrable {Memory Index : Type} [Fintype Index] [DecidableEq Index]
    (prior : PMF Memory) (selected : Index) (raw : ℝ) (rawNonnegative : 0 ≤ raw)
    (rawBounded : raw ≤ 1) (law : Memory → Index → ℝ)
    (nonnegative : ∀ memory index, 0 ≤ law memory index)
    (bounded : ∀ memory index, law memory index ≤ 1) :
    PayoffIntegrable prior (fun memory => raw * ∏ other ∈ Finset.univ.erase selected,
      law memory other) := by
  apply payoffIntegrable_of_bounded _ _ (C := 1)
  intro memory
  rw [abs_of_nonneg (mul_nonneg rawNonnegative
    (Finset.prod_nonneg fun other _ => nonnegative memory other))]
  exact (mul_le_mul_of_nonneg_left
    (Finset.prod_le_one₀ (fun other _ => nonnegative memory other)
      (fun other _ => bounded memory other)) rawNonnegative).trans
        (by simpa only [mul_one] using rawBounded)

private theorem expect_masked_marks {Memory Index : Type} [Fintype Index] [DecidableEq Index]
    (prior : PMF Memory) (good : Index → Prop) (raw : Index → ℝ)
    (atoms : Memory → Index → ℝ) (target : Index → ℝ) (chance : ℝ)
    (rawNonnegative : ∀ index, 0 ≤ raw index) (rawBounded : ∀ index, raw index ≤ 1)
    (nonnegative : ∀ memory index, 0 ≤ atoms memory index)
    (bounded : ∀ memory index, atoms memory index ≤ 1)
    [DecidablePred good]
    (same : ∀ index,
      expect prior (fun memory => if good index then
        raw index * ∏ other ∈ Finset.univ.erase index, atoms memory other else 0) = target index) :
    expect prior (fun memory => chance * ∑ index, if good index then
      raw index * ∏ other ∈ Finset.univ.erase index, atoms memory other else 0) =
        chance * ∑ index, target index := by
  have integrable (index) : PayoffIntegrable prior (fun memory => if good index then
      raw index * ∏ other ∈ Finset.univ.erase index, atoms memory other else 0) := by
    by_cases allowed : good index
    · simp only [ite_eq_left allowed]
      exact marker_integrable prior index (raw index) (rawNonnegative index) (rawBounded index)
        atoms nonnegative bounded
    · simp only [ite_eq_right allowed]
      exact payoffIntegrable_constant _ _
  rw [expect_const_mul, expect_sum prior _ integrable]
  exact congrArg (chance * ·) (Finset.sum_congr rfl fun index _ => same index)

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (runtimePlan : RuntimePhasePlan (serviceGraph setup mode))
  (initial : PMF (PhaseRuntimeState (serviceGraph setup mode)))
  (initialLaw : initial =
    (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs

local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

private theorem raw_marker_bounds (noise : ℝ) (nonnegative : 0 ≤ noise)
    (bounded : noise ≤ 1) (who : Player) (record : (N).InfoState who × (app).Action) :
    0 ≤ phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler noise
      who record ∧
    phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler noise
      who record ≤ 1 := by
  exact ⟨mul_nonneg nonnegative ENNReal.toReal_nonneg,
    (mul_le_mul_of_nonneg_left (pmf_toReal_apply_le_one _ _) nonnegative).trans
      (by simpa only [mul_one] using bounded)⟩

private theorem native_product (who : Player) (policy : (N).BehavioralPolicy who)
    (records : List ((N).InfoState who × (app).Action)) :
    (∏ index : Fin records.length,
      (((policy (records[index.val]).1).map Subtype.val) (some (records[index.val]).2)).toReal) =
        (N).ownPlayReachProbability policy records := by
  have array := (N).ownPlayReachProbability_ofFn who policy
    (fun index : Fin records.length => records[index.val])
  have same : List.ofFn (fun index : Fin records.length => records[index.val]) = records :=
    List.ofFn_get records
  exact array.symm.trans (congrArg ((N).ownPlayReachProbability policy) same)

private theorem native_list_product (who : Player) (policy : (N).BehavioralPolicy who)
    (records : List ((N).InfoState who × (app).Action)) :
    (records.map (fun record => (((policy record.1).map Subtype.val)
      (some record.2)).toReal)).prod = (N).ownPlayReachProbability policy records := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      simp only [List.map_cons, List.prod_cons, ownPlayReachProbability, ih]

private theorem marked_product_grouping
    (profile : ∀ who, (N).BehavioralPolicy who)
    (past suffix : Player → List (app).PlayerEntry)
    (selected : Σ who, Fin ((app).ownPlayFrom (past who) (suffix who)).length)
    (before after : List (app).PlayerEntry) (sent : (app).PlayerEntry)
    (split : suffix selected.1 = before ++ sent :: after)
    (named : ((app).ownPlayFrom (past selected.1) (suffix selected.1))[selected.2.val] =
      (some (past selected.1 ++ before, sent.beforeView), sent.action)) (raw : ℝ) :
    raw * (∏ other ∈ Finset.univ.erase selected,
      (((profile other.1
        (((app).ownPlayFrom (past other.1) (suffix other.1))[other.2.val]).1).map Subtype.val)
          (some (((app).ownPlayFrom (past other.1) (suffix other.1))[other.2.val]).2)).toReal) =
      ∏ who, if who = selected.1 then
        (N).ownPlayReachProbability (profile who) ((app).ownPlayFrom (past who) before) * raw *
          (N).ownPlayReachProbability (profile who)
            ((app).ownPlayFrom ((past selected.1 ++ before) ++ [sent]) after)
        else (N).ownPlayReachProbability (profile who)
          ((app).ownPlayFrom (past who) (suffix who)) := by
  classical
  let records := fun who => (app).ownPlayFrom (past who) (suffix who)
  let atom := fun index : (Σ who, Fin (records who).length) =>
    (((profile index.1 ((records index.1).get index.2).1).map Subtype.val)
      (some ((records index.1).get index.2).2)).toReal
  have grouped := sigma_erased_product (fun who => (records who).length) selected atom raw
  change raw * (∏ other ∈ Finset.univ.erase selected, atom other) = _
  rw [grouped]
  have recordSplit : records selected.1 =
      (app).ownPlayFrom ((past selected.1 ++ before) ++ [sent]) after ++
        (some (past selected.1 ++ before, sent.beforeView), sent.action) ::
          (app).ownPlayFrom (past selected.1) before := by
    have equal := congrArg ((app).ownPlayFrom (past selected.1)) split
    simpa only [ReactiveApplication.ownPlayFrom_concat, ReactiveApplication.ownPlayFrom,
      List.append_assoc, List.singleton_append] using equal
  have erased := erased_product_of_split (records selected.1) selected.2
    ((app).ownPlayFrom ((past selected.1 ++ before) ++ [sent]) after)
      ((app).ownPlayFrom (past selected.1) before)
        (some (past selected.1 ++ before, sent.beforeView), sent.action) recordSplit named
          (fun record => (((profile selected.1 record.1).map Subtype.val)
            (some record.2)).toReal)
  change raw * (∏ other ∈ Finset.univ.erase selected.2,
    (((profile selected.1 (records selected.1)[other.val].1).map Subtype.val)
      (some (records selected.1)[other.val].2)).toReal) * _ = _
  have afterNative := native_list_product setup mode runtime leaks bounds initial horizon
    scheduler selected.1 (profile selected.1)
      ((app).ownPlayFrom ((past selected.1 ++ before) ++ [sent]) after)
  have beforeNative := native_list_product setup mode runtime leaks bounds initial horizon
    scheduler selected.1 (profile selected.1) ((app).ownPlayFrom (past selected.1) before)
  have deleted := erased.trans (congrArg₂ (fun first second : ℝ => first * second)
    afterNative beforeNative)
  have changed := congrArg (fun value => raw * value *
    ∏ owner ∈ Finset.univ.erase selected.1, ∏ index, atom ⟨owner, index⟩) deleted
  apply changed.trans
  rw [← Finset.mul_prod_erase Finset.univ
    (fun who => if who = selected.1 then
      (N).ownPlayReachProbability (profile who) ((app).ownPlayFrom (past who) before) * raw *
        (N).ownPlayReachProbability (profile who)
          ((app).ownPlayFrom ((past selected.1 ++ before) ++ [sent]) after)
      else (N).ownPlayReachProbability (profile who) (records who))
        (Finset.mem_univ selected.1)]
  simp only [↓reduceIte]
  have rest : (∏ who ∈ Finset.univ.erase selected.1,
      ∏ index, atom ⟨who, index⟩) = ∏ who ∈ Finset.univ.erase selected.1,
        if who = selected.1 then
          (N).ownPlayReachProbability (profile who) ((app).ownPlayFrom (past who) before) * raw *
            (N).ownPlayReachProbability (profile who)
              ((app).ownPlayFrom ((past selected.1 ++ before) ++ [sent]) after)
          else (N).ownPlayReachProbability (profile who) (records who) := by
    apply Finset.prod_congr rfl
    intro who member
    rw [ite_eq_right (Finset.mem_erase.mp member).1]
    exact native_product setup mode runtime leaks bounds initial horizon scheduler who
      (profile who) (records who)
  rw [rest]
  ac_rfl

private theorem marked_chance_counterfactual
    (final : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some final))
    (chance : ℝ)
    (factor : ∀ profile : ∀ who, (N).BehavioralPolicy who,
      ((N).historyReachWeight profile ⟨some final, trace⟩).toReal =
        chance * ∏ who, (N).ownPlayReachProbability (profile who) ((N).ownPlay who trace))
    (profile : ∀ who, (N).BehavioralPolicy who) (who : Player)
    (selected : Fin ((N).ownPlay who trace).length) (raw : ℝ) :
    chance * (raw * ∏ other ∈ Finset.univ.erase
        (⟨who, selected⟩ : Σ owner, Fin ((N).ownPlay owner trace).length),
      (((profile other.1 (((N).ownPlay other.1 trace).get other.2).1).map Subtype.val)
        (some (((N).ownPlay other.1 trace).get other.2).2)).toReal) =
      (N).ownPlayReachProbability (profile who) (((N).ownPlay who trace).take selected.val) * raw *
        (N).ownPlayReachProbability (profile who)
          (((N).ownPlay who trace).drop selected.val).tail *
        (N).counterfactualReachProbability profile who trace := by
  classical
  let records := fun owner => (N).ownPlay owner trace
  let atom := fun other : Σ owner, Fin (records owner).length =>
    (((profile other.1 ((records other.1).get other.2).1).map Subtype.val)
      (some ((records other.1).get other.2).2)).toReal
  have cut : records who = (records who).take selected.val ++
      (records who).get selected :: ((records who).drop selected.val).tail := by
    have rest : (records who).drop selected.val =
        (records who).get selected :: ((records who).drop selected.val).tail := by
      rw [List.drop_eq_getElem_cons selected.isLt]
      rfl
    exact (List.take_append_drop selected.val (records who)).symm.trans
      (congrArg ((records who).take selected.val ++ ·) rest)
  have erased := erased_product_of_split (records who) selected
    ((records who).take selected.val) (((records who).drop selected.val).tail)
      ((records who).get selected) cut rfl
        (fun record => (((profile who record.1).map Subtype.val) (some record.2)).toReal)
  have before := native_list_product setup mode runtime leaks bounds initial horizon scheduler
    who (profile who) ((records who).take selected.val)
  have after := native_list_product setup mode runtime leaks bounds initial horizon scheduler
    who (profile who) (((records who).drop selected.val).tail)
  have deleted : (∏ other ∈ Finset.univ.erase selected, atom ⟨who, other⟩) =
      (N).ownPlayReachProbability (profile who) ((records who).take selected.val) *
        (N).ownPlayReachProbability (profile who) (((records who).drop selected.val).tail) :=
    erased.trans (congrArg₂ (fun first second : ℝ => first * second) before after)
  have otherNative : (∏ owner ∈ Finset.univ.erase who, ∏ index, atom ⟨owner, index⟩) =
      ∏ owner ∈ Finset.univ.erase who,
        (N).ownPlayReachProbability (profile owner) (records owner) := by
    apply Finset.prod_congr rfl
    intro owner _member
    exact native_product setup mode runtime leaks bounds initial horizon scheduler owner
      (profile owner) (records owner)
  have grouped := sigma_erased_product (fun owner => (records owner).length)
    ⟨who, selected⟩ atom raw
  have equality := congrArg (chance * ·) grouped
  rw [deleted, otherNative] at equality
  apply equality.trans
  have counter := (menu).counterfactual_of_history_factor initial horizon scheduler final trace
    chance factor profile who
  rw [counter]
  ac_rfl

open Classical in
/-- The same actual path coefficient turns the complete foreign binding
marker sum into REAL counterfactual-weighted own-record marks. No positive
observed response atom is required. -/
theorem phase_binding_marker_sum_counterfactual
    (noise : ℝ) (focal : Player) (final : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some final)) (chance : ℝ)
    (factor : ∀ profile : ∀ who, (N).BehavioralPolicy who,
      ((N).historyReachWeight profile ⟨some final, trace⟩).toReal =
        chance * ∏ who, (N).ownPlayReachProbability (profile who) ((N).ownPlay who trace))
    (profile : ∀ who, (N).BehavioralPolicy who) :
    chance * (∑ index : (Σ who, Fin ((N).ownPlay who trace).length),
      if index.1 ≠ focal ∧ phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan
          horizon scheduler index.1 (((N).ownPlay index.1 trace).get index.2) then
        phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler noise
            index.1 (((N).ownPlay index.1 trace).get index.2) *
          ∏ other ∈ Finset.univ.erase index,
            (((profile other.1 (((N).ownPlay other.1 trace).get other.2).1).map Subtype.val)
              (some (((N).ownPlay other.1 trace).get other.2).2)).toReal
      else 0) =
      ∑ who ∈ Finset.univ.erase focal, ∑ index : Fin ((N).ownPlay who trace).length,
        if phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan horizon scheduler
            who (((N).ownPlay who trace).get index) then
          (N).ownPlayReachProbability (profile who) (((N).ownPlay who trace).take index.val) *
            phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler noise
              who (((N).ownPlay who trace).get index) *
            (N).ownPlayReachProbability (profile who)
              (((N).ownPlay who trace).drop index.val).tail *
            (N).counterfactualReachProbability profile who trace
        else 0 := by
  classical
  rw [Finset.mul_sum, Fintype.sum_sigma]
  have discarded : ∀ who ∈ (Finset.univ : Finset Player), who ∉ Finset.univ.erase focal →
      (∑ index : Fin ((N).ownPlay who trace).length,
        chance * (if who ≠ focal ∧ phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan
            horizon scheduler who (((N).ownPlay who trace).get index) then
          phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler noise
              who (((N).ownPlay who trace).get index) *
            ∏ other ∈ Finset.univ.erase (⟨who, index⟩ :
                Σ owner, Fin ((N).ownPlay owner trace).length),
              (((profile other.1 (((N).ownPlay other.1 trace).get other.2).1).map Subtype.val)
                (some (((N).ownPlay other.1 trace).get other.2).2)).toReal
        else 0)) = 0 := by
    intro who _member outside
    have same : who = focal := by simpa only [Finset.mem_erase, Finset.mem_univ, and_true,
      not_not] using outside
    subst who
    simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, mul_zero, Finset.sum_const_zero]
  rw [← Finset.sum_subset (Finset.erase_subset focal Finset.univ) discarded]
  apply Finset.sum_congr rfl
  intro who member
  have foreign := (Finset.mem_erase.mp member).1
  apply Finset.sum_congr rfl
  intro index _inside
  by_cases raw : phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan horizon scheduler
      who (((N).ownPlay who trace).get index)
  · rw [ite_eq_left ⟨foreign, raw⟩, ite_eq_left raw]
    exact marked_chance_counterfactual setup mode runtime leaks bounds initial horizon scheduler
      final trace chance factor profile who index
        (phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler noise
          who (((N).ownPlay who trace).get index))
  · simp only [raw, and_false, ↓reduceIte, mul_zero]

include initialLaw in
private theorem binding_request_of_commitment
    (remaining : Nat) (who : Player) (physical : (app).Execution)
    (trace : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨remaining, some who, physical⟩))
    (material : WitnessedSubmission (serviceGraph setup mode))
    (event : (serviceGraph setup mode).EventId) (candidate : Handle (serviceGraph setup mode))
    (named : material.call.packet = .commitment event candidate)
    (member : (⟨some material⟩ : (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds
      who (physical.recall who) (physical.observe (app) who)) :
    ∃ payload, (serviceGraph setup mode).outputLayout event = .binding who payload ∧
      physical.application.SeedRequest who ⟨physical.application.attempt, event⟩ ∧
        ∀ message ∈ (app).outputs (physical.recall who),
          PhaseCount.event? message.payload ≠ some ⟨physical.application.attempt, event⟩ := by
  subst initial
  let initial := (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)
  obtain ⟨coordinate, requested⟩ := PhaseCount.onePacket_request_of_nonsilent runtime leaks bounds
    runtimePlan inputs horizon scheduler remaining who physical trace material member
  have namedEvent := PhaseCount.onePacket_event_of_request runtime leaks bounds runtimePlan
    (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining who physical
      trace coordinate requested material member
  rw [named] at namedEvent
  have eventEq : coordinate.event = event := Option.some.inj namedEvent.symm
  have request := requested
  change physical.application.SeedRequest who ⟨coordinate.attempt, coordinate.event⟩ at request
  rw [requested.1, eventEq] at request
  have unsent := PhaseCount.unsent_of_nonsilent runtime leaks bounds runtimePlan
    (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining who physical
      trace ⟨physical.application.attempt, event⟩ request material member
  have permitted : PhaseCount.permits ((app).outputs (physical.recall who))
      (PhaseCount.localEnvelope runtime leaks who (physical.recall who)
        (physical.observe (app) who) material) = true := by
    rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds who _ _ _).mp member).2
      with impossible | ⟨supplied, same, allowed⟩
    · cases impossible
    · cases Option.some.inj same
      exact allowed
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp permitted).2.1
  have actualCall : (PhaseCount.nativeMessage (PhaseCount.localEnvelope runtime leaks who
      (physical.recall who) (physical.observe (app) who) material)).payload.call =
        material.call.packet := PhaseCount.maskPacket_call _ _
  unfold CountCallCorrect at correct
  rw [actualCall, named] at correct
  change bindingOwnedBy (serviceGraph setup mode) who event = true ∧ _ at correct
  have owned := correct.1
  cases node : nodeView (serviceGraph setup mode) event with
  | sample payload law outputEq codeEq =>
      simp only [bindingOwnedBy, outputEq] at owned
      cases owned
  | resolve actor payload binding checks outputEq codeEq =>
      simp only [bindingOwnedBy, outputEq] at owned
      cases owned
  | bind actor payload outputEq codeEq =>
      have same : actor = who := by
        simpa only [bindingOwnedBy, outputEq, decide_eq_true_eq] using owned
      subst actor
      exact ⟨payload, outputEq, request, unsent⟩

include initialLaw in
private theorem binding_record_callback
    (final : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some final))
    (clear : final.execution.application.current.excluded = ∅)
    (who : Player) (past suffix : List (app).PlayerEntry)
    (recalled : final.execution.recall who = past ++ suffix)
    (record : (N).InfoState who × (app).Action)
    (present : record ∈ (app).ownPlayFrom past suffix)
    (raw : phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan horizon scheduler
      who record) :
    ∃ (before : List (app).PlayerEntry) (sent : (app).PlayerEntry)
      (after : List (app).PlayerEntry) (remaining : Nat) (physical : (app).Execution)
      (_prior : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨remaining, some who, physical⟩))
      (event : (serviceGraph setup mode).EventId) (serial : Nat)
      (preparation : Option (Raw L)) (evidence : EvidenceRequest (serviceGraph setup mode))
      (payload : L.Ty),
      suffix = before ++ sent :: after ∧
      record = (some (past ++ before, sent.beforeView), sent.action) ∧
      physical.recall who = past ++ before ∧
      sent.beforeView = physical.observe (app) who ∧
      physical.application.current.excluded = ∅ ∧
      (serviceGraph setup mode).outputLayout event = .binding who payload ∧
      physical.application.SeedRequest who ⟨physical.application.attempt, event⟩ ∧
      (∀ message ∈ (app).outputs (physical.recall who),
        PhaseCount.event? message.payload ≠ some ⟨physical.application.attempt, event⟩) ∧
      sent.action =
        ⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩ := by
  obtain ⟨before, sent, after, tailSplit, recordEq⟩ :=
    ownPlayFrom_origin (app) past suffix
      record present
  have actualRecall : final.execution.recall who =
      (past ++ before) ++ sent :: after := by
    rw [recalled, tailSplit, List.append_assoc]
  obtain ⟨current, prior, isPrefix, active, pastEq, viewed, allowed⟩ :=
    (menu).recorded_response_at initial horizon scheduler final trace who
      (past ++ before) sent after actualRecall
  have currentClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial
    horizon scheduler current final prior trace isPrefix clear).1
  obtain ⟨event, serial, preparation, evidence, sentEq⟩ := raw
  have actionEq : sent.action =
      (⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩ :
        (app).Action) := (congrArg Prod.snd recordEq).symm.trans sentEq
  rcases current with ⟨remaining, actor, physical⟩
  change actor = some who at active
  subst actor
  let material : WitnessedSubmission (serviceGraph setup mode) :=
    ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩
  have member : (⟨some material⟩ : (app).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds who (physical.recall who)
        (physical.observe (app) who) := by
    simpa only [PhaseCount.onePacketMenu, material, actionEq, ← pastEq] using allowed
  obtain ⟨payload, binding, request, unsent⟩ := binding_request_of_commitment setup mode runtime
    leaks bounds runtimePlan initial initialLaw horizon scheduler remaining who physical prior
      material event (who, .prepared serial) rfl member
  exact ⟨before, sent, after, remaining, physical, prior, event, serial, preparation, evidence,
    payload, tailSplit, recordEq, pastEq, viewed, currentClear, binding, request, unsent, actionEq⟩

variable (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    initial horizon
      scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    initial horizon
      scheduler).InfoState who)]

local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
  (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent => PhaseUnprotected runtime leaks bound
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound

local instance markerSumPoolFintype : Fintype Pool := Fintype.ofFinite _

open Classical in
include initialLaw in
private theorem marker_position_expect
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (mixed : assessment.IsFullyMixed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (focal : Player) (replay : (app).Policy)
    (replayCovered : ∀ past view response, response ∈ (replay past view).support →
      response ∈ (menu).actions focal past view)
    (final : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some final))
    (clear : final.execution.application.current.excluded = ∅)
    (past suffix : Player → List (app).PlayerEntry)
    (recalled : ∀ who, final.execution.recall who = past who ++ suffix who)
    (index : Σ who, Fin ((app).ownPlayFrom (past who) (suffix who)).length) :
    let original := fun observer => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy observer).map
        (Prod.mk plan)
    let family := fun observer memory => if observer = focal then replay else
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed
          (setup.commitRecoveryValueAssessment wellFormed assessment observer memory.2)
            noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
              memory.1 observer
    let members := fun memories observer => (menu).restrictPolicy initial horizon scheduler
      observer (family observer (memories observer))
    let behavior := fun observer => (menu).restrictPolicy initial horizon scheduler observer
      ((app).policyMixture (original observer) (family observer)).policy
    let records := fun who => (app).ownPlayFrom (past who) (suffix who)
    let term := fun (profile : ∀ who, (N).BehavioralPolicy who)
      (index : Σ who, Fin (records who).length) =>
    if index.1 ≠ focal ∧ phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan horizon
        scheduler index.1 ((records index.1).get index.2) then
      phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler noise
          index.1 ((records index.1).get index.2) *
        ∏ other ∈ Finset.univ.erase index,
          (((profile other.1 ((records other.1).get other.2).1).map Subtype.val)
            (some ((records other.1).get other.2).2)).toReal
    else 0
    expect (independentProduct fun who =>
      ((app).policyMixture (original who) (family who)).posterior (past who))
        (fun memories => term (members memories) index) = term behavior index := by
  intro original family members behavior records term
  let posterior := independentProduct fun who =>
    ((app).policyMixture (original who) (family who)).posterior (past who)
  by_cases good : index.1 ≠ focal ∧ phaseRawBindingRecord setup mode runtime leaks bounds
      runtimePlan horizon scheduler index.1 ((records index.1).get index.2)
  · obtain ⟨before, sent, after, remaining, physical, prior, event, serial, preparation, evidence,
      payload, tailSplit, recordEq, pastEq, viewed, currentClear, binding, request, unsent,
      actionEq⟩ :=
      binding_record_callback setup mode runtime leaks bounds runtimePlan initial initialLaw horizon
        scheduler final
        trace clear index.1 (past index.1) (suffix index.1) (recalled index.1)
          ((records index.1).get index.2) (List.getElem_mem index.2.isLt) good.2
    have actualRecall : final.execution.recall index.1 =
        (past index.1 ++ before) ++ sent :: after := by
      rw [recalled, tailSplit, List.append_assoc]
    let material : WitnessedSubmission (serviceGraph setup mode) :=
      ⟨⟨.commitment event (index.1, .prepared serial), preparation⟩, evidence⟩
    have finalRecall : final.execution.recall index.1 =
        physical.recall index.1 ++ sent :: after :=
      pastEq.symm ▸ actualRecall
    have exactRecord : ((records index.1).get index.2) =
        (some (physical.recall index.1, physical.observe (app) index.1), sent.action) := by
      simpa only [← pastEq, viewed] using recordEq
    let raw := phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler
      noise index.1 ((records index.1).get index.2)
    have average := phaseTimingPlanPolicy_native_mark_expect_of_history setup mode runtime leaks
      bounds runtimePlan initial initialLaw horizon scheduler bound maximal fallback wellFormed
        assessment mixed
        finite weights noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
          index.1 ⟨remaining, some index.1, physical⟩ prior rfl currentClear event payload binding
            request unsent final trace clear sent after finalRecall viewed material
              (by rw [actionEq]) (index.1, .prepared serial) rfl past before pastEq focal
                good.1 replay suffix replayCovered 1
    have grouped (profile : ∀ who, (N).BehavioralPolicy who) :=
      marked_product_grouping setup mode runtime leaks bounds initial horizon scheduler
        profile past suffix index before after sent tailSplit recordEq raw
    have termEq (profile : ∀ who, (N).BehavioralPolicy who) :
        term profile index = ∏ who, if who = index.1 then
          (N).ownPlayReachProbability (profile who) ((app).ownPlayFrom (past who) before) * raw *
            (N).ownPlayReachProbability (profile who)
              ((app).ownPlayFrom ((past index.1 ++ before) ++ [sent]) after)
          else (N).ownPlayReachProbability (profile who) (records who) := by
      dsimp only [term]
      rw [ite_eq_left good]
      exact grouped profile
    rw [show (fun memories => term (members memories) index) =
      (fun memories => ∏ who, if who = index.1 then
        (N).ownPlayReachProbability (members memories who)
            ((app).ownPlayFrom (past who) before) * raw *
          (N).ownPlayReachProbability (members memories who)
            ((app).ownPlayFrom ((past index.1 ++ before) ++ [sent]) after)
        else (N).ownPlayReachProbability (members memories who) (records who)) by
          funext memories; exact termEq _, termEq behavior]
    simp only [one_mul, ← exactRecord] at average
    simpa only [pastEq] using average
  · simp only [term, ite_eq_right good, expect_constant]

include initialLaw in
open Classical in
/-- Averaging ALL actual foreign binding-SEND marks over the original owner
posteriors gives exactly the intrinsic native marked path sum. Only binding
SEND atoms are marked: original omissions, RAW opening waits and all other
noisy factors remain unchanged. Arbitrary full entry recall is retained. -/
theorem phaseTimingPlanPolicy_marker_sum_expect_of_history
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (mixed : assessment.IsFullyMixed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (weights : (p : Pool) → PMF (Parts p))
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (focal : Player) (replay : (app).Policy)
    (replayCovered : ∀ past view response, response ∈ (replay past view).support →
      response ∈ (menu).actions focal past view)
    (final : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some final))
    (clear : final.execution.application.current.excluded = ∅)
    (past suffix : Player → List (app).PlayerEntry)
    (recalled : ∀ who, final.execution.recall who = past who ++ suffix who) (chance : ℝ) :
    let original := fun observer => (independentProduct weights).bind fun plan =>
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy observer).map
        (Prod.mk plan)
    let family := fun observer memory => if observer = focal then replay else
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed
          (setup.commitRecoveryValueAssessment wellFormed assessment observer memory.2)
            noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded
              memory.1 observer
    let members := fun memories observer => (menu).restrictPolicy initial horizon scheduler
      observer (family observer (memories observer))
    let behavior := fun observer => (menu).restrictPolicy initial horizon scheduler observer
      ((app).policyMixture (original observer) (family observer)).policy
    let records := fun who => (app).ownPlayFrom (past who) (suffix who)
    let marker := fun profile : ∀ who, (N).BehavioralPolicy who =>
      chance * ∑ index : (Σ who, Fin (records who).length),
        if index.1 ≠ focal ∧ phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan
            horizon scheduler index.1 ((records index.1).get index.2) then
          phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler noise
              index.1 ((records index.1).get index.2) *
            ∏ other ∈ Finset.univ.erase index,
              (((profile other.1 ((records other.1).get other.2).1).map Subtype.val)
                (some ((records other.1).get other.2).2)).toReal
        else 0
    expect (independentProduct fun who =>
      ((app).policyMixture (original who) (family who)).posterior (past who))
        (fun memories => marker (members memories)) = marker behavior := by
  intro original family members behavior records marker
  let posterior := independentProduct fun who =>
    ((app).policyMixture (original who) (family who)).posterior (past who)
  let term := fun (profile : ∀ who, (N).BehavioralPolicy who)
      (index : Σ who, Fin (records who).length) =>
    if index.1 ≠ focal ∧ phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan horizon
        scheduler index.1 ((records index.1).get index.2) then
      phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler noise
          index.1 ((records index.1).get index.2) *
        ∏ other ∈ Finset.univ.erase index,
          (((profile other.1 ((records other.1).get other.2).1).map Subtype.val)
            (some ((records other.1).get other.2).2)).toReal
    else 0
  have averaged := expect_masked_marks (Index := Σ who, Fin (records who).length) posterior
    (fun index => index.1 ≠ focal ∧ phaseRawBindingRecord setup mode runtime leaks bounds
      runtimePlan horizon scheduler index.1 ((records index.1).get index.2))
    (fun index => phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler
      noise index.1 ((records index.1).get index.2))
    (fun memories other =>
      (((members memories other.1 ((records other.1).get other.2).1).map Subtype.val)
        (some ((records other.1).get other.2).2)).toReal)
    (term behavior) chance
    (fun index => (raw_marker_bounds setup mode runtime leaks bounds runtimePlan initial horizon
      scheduler
      noise noiseNonnegative noiseBounded index.1 ((records index.1).get index.2)).1)
    (fun index => (raw_marker_bounds setup mode runtime leaks bounds runtimePlan initial horizon
      scheduler
      noise noiseNonnegative noiseBounded index.1 ((records index.1).get index.2)).2)
    (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => pmf_toReal_apply_le_one _ _)
    (fun index => marker_position_expect setup mode runtime leaks bounds runtimePlan initial
      initialLaw horizon
      scheduler bound maximal fallback wellFormed assessment mixed finite weights noise
        noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded focal replay
          replayCovered final trace clear past suffix recalled index)
  exact averaged

end Vegas
