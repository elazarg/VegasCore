/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ScheduledOpeningSupport
import GameTheoryExtensions.Math.Probability.DeferredChoice
import GameTheoryExtensions.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Support

/-! # The exact posterior after waiting for an opening

All modes still waiting use the same response law. Its likelihood therefore
cancels, even when that law depends on earlier observations and replay choices.
The remaining posterior is the original timing law restricted to unpassed
slots. This is a calculation on actual response recall, not extra private state.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

private theorem response_pair_prob {Index : Type} (prior : PMF Index)
    (responses : Index → PMF app.Action) (action : app.Action) (index : Index) :
    ((prior.bind fun selected => (responses selected).map fun reply => (reply, selected))
      (action, index)).toReal = (prior index).toReal * ((responses index) action).toReal := by
  rw [bind_map_tag_apply, ENNReal.toReal_mul]

open Classical in
/-- An observed waiting response removes precisely the opening modes.
Its particular replay likelihood cancels from the posterior. -/
theorem policyMixture_posterior_wait {Index : Type} (initial : PMF Index)
    (policies : Index → app.Policy) (past : List app.PlayerEntry) (entry : app.PlayerEntry)
    (opening : app.Action) (waiting : PMF app.Action) (kept : Set Index)
    (meets : ∃ index ∈ kept,
      index ∈ ((app.policyMixture initial policies).posterior past).support)
    (branches : ∀ index ∈ ((app.policyMixture initial policies).posterior past).support,
      policies index past entry.beforeView = if index ∈ kept then waiting else PMF.pure opening)
    (different : entry.action ≠ opening) (possible : entry.action ∈ waiting.support) :
    (app.policyMixture initial policies).posterior (past ++ [entry]) =
      ((app.policyMixture initial policies).posterior past).filter kept meets := by
  classical
  let prior := (app.policyMixture initial policies).posterior past
  let responses := fun index => policies index past entry.beforeView
  let joint := prior.bind fun index => (responses index).map fun reply => (reply, index)
  have actionMass : ((joint.map Prod.fst) entry.action).toReal =
      (waiting entry.action).toReal * (prior.toOuterMeasure kept).toReal := by
    have marginal : joint.map Prod.fst = prior.bind responses := by
      simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
      apply bind_congr_on_support _
      intro index _
      exact PMF.map_id _
    rw [marginal, toReal_bind_apply]
    calc
      _ = expect prior (fun index =>
          (waiting entry.action).toReal * (if index ∈ kept then 1 else 0)) := by
        apply expect_congr_on_support
        intro index supported
        change ((policies index past entry.beforeView) entry.action).toReal = _
        rw [branches index supported]
        by_cases remains : index ∈ kept
        · simp only [remains, ↓reduceIte, mul_one]
        · simp only [remains, ↓reduceIte, PMF.pure_apply_of_ne _ _ different,
            ENNReal.toReal_zero, mul_zero]
      _ = _ := by rw [expect_const_mul, expect_indicator]
  have actionPositive : 0 < ((joint.map Prod.fst) entry.action).toReal := by
    rw [actionMass]
    exact mul_pos (pmf_toReal_pos_iff.mpr possible) (toOuterMeasure_toReal_pos _ meets)
  have actionMeet : ∃ pair ∈ Prod.fst ⁻¹' {entry.action}, pair ∈ joint.support := by
    obtain ⟨pair, supported, equal⟩ := PMF.support_map .. ▸
      pmf_toReal_pos_iff.mp actionPositive
    exact ⟨pair, equal, supported⟩
  have mass : (joint.toOuterMeasure (Prod.fst ⁻¹' {entry.action})).toReal =
      (waiting entry.action).toReal * (prior.toOuterMeasure kept).toReal := by
    rw [← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton]
    exact actionMass
  have conditioned : joint.filter (Prod.fst ⁻¹' {entry.action}) actionMeet =
      (prior.filter kept meets).map (fun index => (entry.action, index)) := by
    apply pmf_ext_toReal
    rintro ⟨reply, index⟩
    rw [toReal_filter_apply, mass]
    by_cases equal : reply = entry.action
    · subst reply
      rw [ite_eq_left (show (entry.action, index) ∈ Prod.fst ⁻¹' {entry.action} from rfl),
        app.response_pair_prob prior responses,
        pmf_map_apply_of_injective _ (fun _ _ same => (Prod.mk.inj same).2),
        toReal_filter_apply]
      by_cases supported : index ∈ prior.support
      · change (prior index).toReal * ((policies index past entry.beforeView) entry.action).toReal /
          ((waiting entry.action).toReal * (prior.toOuterMeasure kept).toReal) = _
        rw [branches index supported]
        by_cases remains : index ∈ kept
        · rw [ite_eq_left remains, ite_eq_left remains]
          rw [mul_comm ((waiting entry.action).toReal), mul_div_mul_right _ _
            (ne_of_gt (pmf_toReal_pos_iff.mpr possible))]
        · simp only [remains, ↓reduceIte, PMF.pure_apply_of_ne _ _ different,
            ENNReal.toReal_zero, mul_zero, zero_div]
      · simp only [pmf_toReal_eq_zero_iff.mpr supported, zero_mul, zero_div, ite_self]
    · rw [ite_eq_right (show (reply, index) ∉ Prod.fst ⁻¹' {entry.action} from equal)]
      symm
      apply pmf_toReal_eq_zero_iff.mpr
      intro member
      obtain ⟨old, _, equality⟩ := PMF.support_map .. ▸ member
      exact equal (congrArg Prod.fst equality).symm
  rw [Implementation.posterior_snoc]
  change (fiberConditional joint Prod.fst entry.action).map Prod.snd = _
  rw [fiberConditional, dite_eq_left actionMeet, conditioned, PMF.map_comp]
  exact PMF.map_id _

/-- Slots still available after `count` waiting responses. Never opening is
always retained. -/
def remainingOpeningSlots {slots : Nat} (count : Nat) : Set (Option (Fin slots)) :=
  {selected | match selected with
    | none => True
    | some slot => count ≤ slot.val}

/-- A single lawful waiting response advances an already conditioned timing
posterior. The earlier recall need not be supplied as an explicit word. -/
theorem scheduledMixture_waiting_step {slots : Nat}
    (initial : PMF (Option (Fin slots))) (never : none ∈ initial.support) (offset : Nat)
    (opening : app.Action) (waiting : app.Policy)
    (different : ∀ past view, opening ∉ (waiting past view).support)
    (past : List app.PlayerEntry) (entry : app.PlayerEntry) (count : Nat)
    (atCount : past.length = offset + count)
    (old : (app.policyMixture initial (fun selected => app.scheduledPolicy offset selected
      (fun _ _ => PMF.pure opening) waiting)).posterior past =
        initial.filter (remainingOpeningSlots count) ⟨none, True.intro, never⟩)
    (possible : entry.action ∈ (waiting past entry.beforeView).support) :
    (app.policyMixture initial (fun selected => app.scheduledPolicy offset selected
      (fun _ _ => PMF.pure opening) waiting)).posterior (past ++ [entry]) =
        initial.filter (remainingOpeningSlots (count + 1)) ⟨none, True.intro, never⟩ := by
  classical
  let policies := fun selected : Option (Fin slots) =>
    app.scheduledPolicy offset selected (fun _ _ => PMF.pure opening) waiting
  let mixture := app.policyMixture initial policies
  change mixture.posterior past =
    initial.filter (remainingOpeningSlots count) ⟨none, True.intro, never⟩ at old
  have meets (next : Nat) : ∃ selected ∈ remainingOpeningSlots next,
      selected ∈ initial.support := ⟨none, True.intro, never⟩
  have nextMeets : ∃ selected ∈ remainingOpeningSlots (count + 1),
      selected ∈ (mixture.posterior past).support := by
    refine ⟨none, True.intro, ?_⟩
    rw [old]
    exact (PMF.mem_support_filter_iff _).mpr ⟨True.intro, never⟩
  have branches (selected : Option (Fin slots))
      (supported : selected ∈ (mixture.posterior past).support) :
      policies selected past entry.beforeView =
        if selected ∈ remainingOpeningSlots (count + 1) then
          waiting past entry.beforeView else PMF.pure opening := by
    rw [old] at supported
    have retained := ((PMF.mem_support_filter_iff _).mp supported).1
    cases selected with
    | none => simp [policies, scheduledPolicy, remainingOpeningSlots]
    | some slot =>
        change count ≤ slot.val at retained
        by_cases later : count + 1 ≤ slot.val
        · have unequal : offset + slot.val ≠ past.length := by rw [atCount]; omega
          simp only [policies, scheduledPolicy, Option.map_some,
            Option.some.injEq, ite_eq_right unequal, remainingOpeningSlots,
            Set.mem_ofPred_eq, later, ↓reduceIte]
        · have equal : slot.val = count := by omega
          simp only [policies, scheduledPolicy, Option.map_some, equal,
            atCount, ↓reduceIte, remainingOpeningSlots,
            Set.mem_ofPred_eq, Nat.add_one_le_iff, lt_self_iff_false]
  have update := app.policyMixture_posterior_wait initial policies past entry
    opening (waiting past entry.beforeView) (remainingOpeningSlots (count + 1))
      nextMeets branches (fun equal => different _ _ (equal ▸ possible)) possible
  rw [update]
  have nested := filter_filter_of_subset initial _ _ (meets count)
    (by simpa only [old] using nextMeets) (by
    intro selected remaining
    cases selected with
    | none => exact True.intro
    | some slot =>
        change count + 1 ≤ slot.val at remaining
        change count ≤ slot.val
        omega)
  change (mixture.posterior past).filter _ nextMeets = _
  simpa only [old] using nested

/-- Every observed replay/silence likelihood cancels. After a lawful waiting
prefix, the actual latent posterior is exactly the original timing law
conditioned on not selecting an earlier slot. -/
theorem scheduledMixture_waiting_posterior {slots : Nat}
    (initial : PMF (Option (Fin slots))) (never : none ∈ initial.support) (offset : Nat)
    (opening : app.Action) (waiting : app.Policy)
    (different : ∀ past view, opening ∉ (waiting past view).support)
    (past suffix : List app.PlayerEntry) (atStart : past.length = offset)
    (lawful : ∀ before entry after, suffix = before ++ entry :: after →
      entry.action ∈ (waiting (past ++ before) entry.beforeView).support) :
    (app.policyMixture initial (fun selected => app.scheduledPolicy offset selected
      (fun _ _ => PMF.pure opening) waiting)).posterior (past ++ suffix) =
        initial.filter (remainingOpeningSlots suffix.length) ⟨none, True.intro, never⟩ := by
  classical
  let policies := fun selected : Option (Fin slots) =>
    app.scheduledPolicy offset selected (fun _ _ => PMF.pure opening) waiting
  let mixture := app.policyMixture initial policies
  have meets (count : Nat) : ∃ selected ∈ remainingOpeningSlots count,
      selected ∈ initial.support := ⟨none, True.intro, never⟩
  change mixture.posterior (past ++ suffix) =
    initial.filter (remainingOpeningSlots suffix.length) (meets suffix.length)
  induction suffix using List.reverseRecOn with
  | nil =>
      have dormant := app.policyMixture_posterior_dormant initial policies waiting offset
        (fun selected before view earlier =>
          app.scheduledPolicy_before offset selected _ waiting before view earlier)
        past atStart.le
      have all : remainingOpeningSlots (slots := slots) 0 = Set.univ := by
        ext selected
        cases selected <;> simp [remainingOpeningSlots]
      have whole : initial.filter (remainingOpeningSlots 0) (meets 0) = initial := by
        ext selected
        simp only [PMF.filter_apply, all, Set.indicator_univ, PMF.tsum_coe, inv_one, mul_one]
      simp only [List.append_nil, List.length_nil, whole]
      exact dormant
  | append_singleton suffix entry ih =>
      have earlierLawful : ∀ before next after, suffix = before ++ next :: after →
          next.action ∈ (waiting (past ++ before) next.beforeView).support := by
        intro before next after split
        exact lawful before next (after ++ [entry]) (by simp [split, List.append_assoc])
      have old := ih earlierLawful
      have update := app.scheduledMixture_waiting_step initial never offset opening waiting
        different (past ++ suffix) entry suffix.length
        (by simp only [List.length_append, atStart]) old (lawful suffix entry [] (by simp))
      simpa only [List.append_assoc, List.length_append, List.length_singleton] using update

private theorem remainingOpeningSlots_mass {slots : Nat} (probability : ℝ)
    (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    (timing : PMF (Fin slots)) (count : Nat) :
    ((mix probability nonnegative bounded (timing.map some) (PMF.pure none)).toOuterMeasure
      (remainingOpeningSlots count)).toReal = PMF.deferredSurvival probability timing count := by
  classical
  rw [← expect_indicator, expect_mix_of_finite, expect_map, Function.comp_def,
    expect_pure]
  have retained : expect timing (fun slot =>
      if some slot ∈ remainingOpeningSlots count then (1 : ℝ) else 0) =
        1 - timing.timingPrefix count := by
    rw [expect_eq_sum, ← pmf_sum_toReal_eq_one timing]
    unfold PMF.timingPrefix
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro slot _
    by_cases before : slot.val < count
    · simp [remainingOpeningSlots, Nat.not_le.mpr before, before]
    · simp [remainingOpeningSlots, Nat.le_of_not_gt before, before, pmf_sum_toReal_eq_one]
  rw [retained]
  simp only [remainingOpeningSlots, Set.mem_ofPred_eq, ↓reduceIte, mul_one,
    PMF.deferredSurvival]
  ring

/-- The eventual binary value under the actual waiting posterior. Past
waiting changes the binary probability; it does not simply leave it equal
to the source probability. -/
theorem remainingOpeningSlots_value {slots : Nat} (probability : ℝ)
    (nonnegative : 0 ≤ probability) (small : probability < 1)
    (timing : PMF (Fin slots)) (count : Nat) (whenTrue whenFalse : ℝ) :
    let initial := mix probability nonnegative small.le
      (timing.map some) (PMF.pure none)
    expect (initial.filter (remainingOpeningSlots count) ⟨none, True.intro,
      mem_support_mix_right probability nonnegative small.le small (by simp)⟩)
        (fun selected => if selected.isSome then whenTrue else whenFalse) =
      PMF.deferredRemaining probability timing count * whenTrue +
        (1 - PMF.deferredRemaining probability timing count) * whenFalse := by
  classical
  intro initial
  let post := initial.filter (remainingOpeningSlots count) ⟨none, True.intro,
    mem_support_mix_right probability nonnegative small.le small (by simp)⟩
  have absent : ((timing.map some) none).toReal = 0 := by
    apply pmf_toReal_eq_zero_iff.mpr
    simp only [PMF.support_map, Set.mem_image, not_exists, not_and]
    intro slot _
    simp
  have noneMass : (post none).toReal =
      (1 - probability) / PMF.deferredSurvival probability timing count := by
    change ((initial.filter _ _) none).toReal = _
    rw [toReal_filter_apply,
      ite_eq_left (show none ∈ remainingOpeningSlots count from True.intro)]
    dsimp only [initial]
    rw [remainingOpeningSlots_mass, mix_apply_toReal, absent, toReal_pure_apply, ite_eq_left rfl]
    ring
  have values (selected : Option (Fin slots)) :
      (if selected.isSome then whenTrue else whenFalse) =
        whenTrue + if none = selected then whenFalse - whenTrue else 0 := by
    cases selected <;> simp
  change expect post _ = _
  simp_rw [values]
  rw [expect_add_of_finite, expect_constant, expect_ite_eq, noneMass,
    PMF.deferredRemaining_eq probability nonnegative small timing count]
  ring

/-- The exact recall-conditioned waiting law has a uniform vanishing value
error. Its bound is independent of how small either source tremble becomes. -/
theorem remainingOpeningSlots_value_error {slots : Nat} (probability : ℝ)
    (nonnegative : 0 ≤ probability) (small : probability < 1)
    (timing : PMF (Fin slots)) (count : Nat) (whenTrue whenFalse : ℝ) :
    let initial := mix probability nonnegative small.le
      (timing.map some) (PMF.pure none)
    |expect (initial.filter (remainingOpeningSlots count) ⟨none, True.intro,
      mem_support_mix_right probability nonnegative small.le small (by simp)⟩)
        (fun selected => if selected.isSome then whenTrue else whenFalse) -
      (probability * whenTrue + (1 - probability) * whenFalse)| ≤
        timing.timingPrefix count * |whenTrue - whenFalse| := by
  dsimp only
  rw [remainingOpeningSlots_value probability nonnegative small timing count whenTrue whenFalse]
  exact PMF.deferredRemaining_value_error probability nonnegative small timing count
    whenTrue whenFalse

/-- The real probability of each response under the actual recall-conditioned
policy is its deferred hazard mixture. All replay likelihoods have cancelled. -/
theorem scheduledMixture_probability_of_posterior {slots : Nat}
    (probability : ℝ) (nonnegative : 0 ≤ probability) (small : probability < 1)
    (timing : PMF (Fin slots)) (offset : Nat) (opening : app.Action) (waiting : app.Policy)
    (past : List app.PlayerEntry) (slot : Fin slots)
    (atSlot : past.length = offset + slot.val)
    (posterior :
      (app.policyMixture
        (mix probability nonnegative small.le (timing.map some) (PMF.pure none))
        (fun selected => app.scheduledPolicy offset selected
          (fun _ _ => PMF.pure opening) waiting)).posterior past =
        (mix probability nonnegative small.le (timing.map some) (PMF.pure none)).filter
          (remainingOpeningSlots slot.val) ⟨none, True.intro,
            mem_support_mix_right probability nonnegative small.le small (by simp)⟩)
    (view : app.PlayerView) (action : app.Action) :
    let initial := mix probability nonnegative small.le
      (timing.map some) (PMF.pure none)
    let policies := fun selected => app.scheduledPolicy offset selected
      (fun _ _ => PMF.pure opening) waiting
    (((app.policyMixture initial policies).policy past view) action).toReal =
      PMF.deferredHazard probability timing slot.val * ((PMF.pure opening) action).toReal +
        (1 - PMF.deferredHazard probability timing slot.val) *
          ((waiting past view) action).toReal := by
  classical
  dsimp only
  let initial := mix probability nonnegative small.le
    (timing.map some) (PMF.pure none)
  let policies := fun selected : Option (Fin slots) => app.scheduledPolicy offset selected
    (fun _ _ => PMF.pure opening) waiting
  have never : none ∈ initial.support :=
    mem_support_mix_right probability nonnegative small.le small (by simp)
  let post := initial.filter (remainingOpeningSlots slot.val) ⟨none, True.intro, never⟩
  change (app.policyMixture initial policies).posterior past = post at posterior
  have mass : (post (some slot)).toReal = PMF.deferredHazard probability timing slot.val := by
    rw [PMF.deferredHazard_at]
    dsimp only [post]
    rw [toReal_filter_apply, ite_eq_left
      (show some slot ∈ remainingOpeningSlots slot.val from by
        change slot.val ≤ slot.val
        exact le_rfl)]
    rw [remainingOpeningSlots_mass, mix_apply_toReal,
      pmf_map_apply_of_injective _ (Option.some_injective _),
      PMF.pure_apply_of_ne _ _ (by simp : some slot ≠ none), ENNReal.toReal_zero, mul_zero,
      add_zero]
  rw [app.policyMixture_policy]
  change ((((app.policyMixture initial policies).posterior past).bind
    (fun selected => policies selected past view)) action).toReal = _
  rw [posterior, toReal_bind_apply]
  have laws (selected : Option (Fin slots)) :
      policies selected past view =
        if selected = some slot then PMF.pure opening else waiting past view := by
    have same : selected.map (fun chosen => offset + chosen.val) =
        some past.length ↔ selected = some slot := by
      cases selected with
      | none => simp
      | some chosen =>
          simp only [Option.map_some, Option.some.injEq, atSlot]
          constructor
          · intro equal
            exact Fin.ext (by omega)
          · intro equal
            rw [equal]
    simp only [policies, scheduledPolicy, same]
  calc
    _ = expect post (fun selected => ((waiting past view) action).toReal +
        if some slot = selected then
          ((PMF.pure opening) action).toReal - ((waiting past view) action).toReal
        else 0) := by
      apply expect_congr_on_support
      intro selected _
      rw [laws]
      by_cases equal : selected = some slot
      · subst selected
        simp only [↓reduceIte]
        ring
      · simp only [equal, Ne.symm equal, ↓reduceIte, add_zero]
    _ = _ := by
      rw [expect_add_of_finite, expect_constant, expect_ite_eq, mass]
      ring

theorem scheduledMixture_waiting_probability {slots : Nat}
    (probability : ℝ) (nonnegative : 0 ≤ probability) (small : probability < 1)
    (timing : PMF (Fin slots)) (offset : Nat) (opening : app.Action) (waiting : app.Policy)
    (different : ∀ past view, opening ∉ (waiting past view).support)
    (past suffix : List app.PlayerEntry) (atStart : past.length = offset)
    (slot : Fin slots) (atSlot : suffix.length = slot.val)
    (lawful : ∀ before entry after, suffix = before ++ entry :: after →
      entry.action ∈ (waiting (past ++ before) entry.beforeView).support)
    (view : app.PlayerView) (action : app.Action) :
    let initial := mix probability nonnegative small.le
      (timing.map some) (PMF.pure none)
    let policies := fun selected => app.scheduledPolicy offset selected
      (fun _ _ => PMF.pure opening) waiting
    (((app.policyMixture initial policies).policy (past ++ suffix) view) action).toReal =
      PMF.deferredHazard probability timing slot.val * ((PMF.pure opening) action).toReal +
        (1 - PMF.deferredHazard probability timing slot.val) *
          ((waiting (past ++ suffix) view) action).toReal := by
  dsimp only
  let initial := mix probability nonnegative small.le
    (timing.map some) (PMF.pure none)
  have never : none ∈ initial.support :=
    mem_support_mix_right probability nonnegative small.le small (by simp)
  have posterior := app.scheduledMixture_waiting_posterior initial never offset opening waiting
    different past suffix atStart lawful
  exact app.scheduledMixture_probability_of_posterior probability nonnegative small timing
    offset opening waiting (past ++ suffix) slot
    (by simp only [List.length_append, atStart, atSlot])
    (by simpa only [atSlot] using posterior) view action

/-- One common sequence converges at every lawful pre-opening history to
waiting at earlier slots and using the original source mixture at the last.
The source opening probability may tend to zero or one. -/
theorem scheduledMixture_waiting_limit {last : Nat}
    (probability : Nat → ℝ) (nonnegative : ∀ n, 0 ≤ probability n)
    (small : ∀ n, probability n < 1) (limit : ℝ)
    (limitNonnegative : 0 ≤ limit) (limitBounded : limit ≤ 1)
    (probabilityConverges : Filter.Tendsto probability Filter.atTop (nhds limit))
    (timing : Nat → PMF (Fin (last + 1)))
    (timingConverges : PMFConvergesPointwise timing (PMF.pure (Fin.last last)))
    (offset : Nat) (opening : app.Action) (waiting : app.Policy)
    (different : ∀ past view, opening ∉ (waiting past view).support)
    (past suffix : List app.PlayerEntry) (atStart : past.length = offset)
    (slot : Fin (last + 1)) (atSlot : suffix.length = slot.val)
    (lawful : ∀ before entry after, suffix = before ++ entry :: after →
      entry.action ∈ (waiting (past ++ before) entry.beforeView).support)
    (view : app.PlayerView) :
    PMFConvergesPointwise (fun n =>
      let initial := mix (probability n) (nonnegative n) (small n).le
        ((timing n).map some) (PMF.pure none)
      let policies := fun selected => app.scheduledPolicy offset selected
        (fun _ _ => PMF.pure opening) waiting
      (app.policyMixture initial policies).policy (past ++ suffix) view)
      (if slot = Fin.last last then
        mix limit limitNonnegative limitBounded (PMF.pure opening)
          (waiting (past ++ suffix) view)
      else waiting (past ++ suffix) view) := by
  rw [pmfConvergesPointwise_iff_toReal]
  intro action
  dsimp only
  have hazard := PMF.deferredHazard_tendsto_last probabilityConverges timingConverges slot
  have one : Filter.Tendsto (fun _ : Nat => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have combined := (hazard.mul_const (((PMF.pure opening) action).toReal)).add
    ((one.sub hazard).mul_const (((waiting (past ++ suffix) view) action).toReal))
  have actual := combined.congr' (Filter.Eventually.of_forall (fun n =>
    (app.scheduledMixture_waiting_probability (probability n) (nonnegative n) (small n)
      (timing n) offset opening waiting different past suffix atStart slot atSlot lawful
        view action).symm))
  by_cases final : slot = Fin.last last
  · simpa only [final, ↓reduceIte, mix_apply_toReal] using actual
  · simpa only [final, ↓reduceIte, zero_mul, sub_zero, one_mul, zero_add] using actual

/-- After any legal opening, the common fully supported sequence is already
constant at the waiting policy. This includes early openings that have zero
probability in the limiting last-slot strategy. -/
theorem scheduledMixture_opened_limit {slots : Nat}
    (initial : Nat → PMF (Option (Fin slots))) (full : ∀ n, FullSupport (initial n))
    (offset : Nat) (opening : app.Action) (waiting : app.Policy)
    (different : ∀ past view, opening ∉ (waiting past view).support)
    (past before : List app.PlayerEntry) (atStart : past.length = offset)
    (slot : Fin slots) (atSlot : before.length = slot.val)
    (lawful : ∀ earlier entry after, before = earlier ++ entry :: after →
      entry.action ∈ (waiting (past ++ earlier) entry.beforeView).support)
    (entry : app.PlayerEntry) (opened : entry.action = opening)
    (after : List app.PlayerEntry) (view : app.PlayerView) :
    PMFConvergesPointwise (fun n =>
      (app.policyMixture (initial n) (fun selected => app.scheduledPolicy offset selected
        (fun _ _ => PMF.pure opening) waiting)).policy
          (past ++ before ++ [entry] ++ after) view)
      (waiting (past ++ before ++ [entry] ++ after) view) := by
  have same (n : Nat) :
      (app.policyMixture (initial n) (fun selected => app.scheduledPolicy offset selected
        (fun _ _ => PMF.pure opening) waiting)).policy
          (past ++ before ++ [entry] ++ after) view =
          waiting (past ++ before ++ [entry] ++ after) view := by
    have supported := (app.scheduledMixture_before_open_full (initial n) (full n) offset
      opening waiting past before atStart (by omega) lawful entry.beforeView).1
    exact app.scheduledMixture_after_open (initial n) offset opening waiting slot
      (past ++ before) entry (by simp only [List.length_append, atStart, atSlot]) opened
        (different _ _) supported after view
  intro action
  simp only [same]
  exact tendsto_const_nhds

end Interaction.ReactiveApplication
