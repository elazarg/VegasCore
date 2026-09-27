/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ScheduledOpeningSupport
import GameTheoryExtensions.Math.Probability.DeferredChoice

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

private theorem response_pair_prob {Index : Type} (prior : FinDist Index)
    (responses : Index → FinDist app.Action) (action : app.Action) (index : Index) :
    (prior.bind fun selected => (responses selected).map fun reply => (reply, selected)).prob
      (action, index) = prior.prob index * (responses index).prob action := by
  classical
  rw [FinDist.prob_bind_of_unique_branch prior
    (fun selected => (responses selected).map fun reply => (reply, selected))
      (action, index) index]
  · rw [FinDist.prob_map_of_injective (fun reply => (reply, index))
      (fun _ _ same => (Prod.mk.inj same).1)]
  · intro selected _ member
    obtain ⟨reply, _, same⟩ := FinDist.support_map .. ▸ member
    exact congrArg Prod.snd same

open Classical in
/-- An observed waiting response removes precisely the opening modes.
Its particular replay likelihood cancels from the posterior. -/
theorem policyMixture_posterior_wait {Index : Type} (initial : FinDist Index)
    (policies : Index → app.Policy) (past : List app.PlayerEntry) (entry : app.PlayerEntry)
    (opening : app.Action) (waiting : FinDist app.Action) (kept : Set Index)
    (meets : ∃ index ∈ kept,
      index ∈ ((app.policyMixture initial policies).posterior past).support)
    (branches : ∀ index ∈ ((app.policyMixture initial policies).posterior past).support,
      policies index past entry.beforeView = if index ∈ kept then waiting else FinDist.pure opening)
    (different : entry.action ≠ opening) (possible : entry.action ∈ waiting.support) :
    (app.policyMixture initial policies).posterior (past ++ [entry]) =
      ((app.policyMixture initial policies).posterior past).condOn kept meets := by
  classical
  let prior := (app.policyMixture initial policies).posterior past
  let responses := fun index => policies index past entry.beforeView
  let joint := prior.bind fun index => (responses index).map fun reply => (reply, index)
  have actionMass : (joint.map Prod.fst).prob entry.action =
      waiting.prob entry.action * prior.probOf kept := by
    have marginal : joint.map Prod.fst = prior.bind responses := by
      simp only [joint, FinDist.map_bind, FinDist.map_comp, Function.comp_def]
      apply FinDist.bind_congr
      intro index _
      exact FinDist.map_id _
    rw [marginal, FinDist.prob_bind]
    calc
      _ = prior.expect (fun index =>
          waiting.prob entry.action * (if index ∈ kept then 1 else 0)) := by
        apply FinDist.expect_congr
        intro index supported
        change (policies index past entry.beforeView).prob entry.action = _
        rw [branches index supported]
        by_cases remains : index ∈ kept
        · simp only [remains, ↓reduceIte, mul_one]
        · simp only [remains, ↓reduceIte, FinDist.prob_pure_of_ne different, mul_zero]
      _ = _ := by rw [FinDist.expect_smul, FinDist.expect_indicator_eq_probOf]
  have actionPositive : 0 < (joint.map Prod.fst).prob entry.action := by
    rw [actionMass]
    exact mul_pos (FinDist.prob_pos_iff.mpr possible) (FinDist.probOf_pos meets)
  have actionMeet : ∃ pair ∈ Prod.fst ⁻¹' {entry.action}, pair ∈ joint.support := by
    obtain ⟨pair, supported, equal⟩ := FinDist.support_map .. ▸
      FinDist.prob_pos_iff.mp actionPositive
    exact ⟨pair, equal, supported⟩
  have mass : joint.probOf (Prod.fst ⁻¹' {entry.action}) =
      waiting.prob entry.action * prior.probOf kept := by
    rw [← FinDist.prob_map_eq_probOf_preimage_singleton]
    exact actionMass
  have conditioned : joint.condOn (Prod.fst ⁻¹' {entry.action}) actionMeet =
      (prior.condOn kept meets).map (fun index => (entry.action, index)) := by
    apply FinDist.ext_of_prob
    rintro ⟨reply, index⟩
    rw [FinDist.prob_condOn, mass]
    by_cases equal : reply = entry.action
    · subst reply
      rw [ite_eq_left (show (entry.action, index) ∈ Prod.fst ⁻¹' {entry.action} from rfl),
        app.response_pair_prob prior responses,
        FinDist.prob_map_of_injective (fun index => (entry.action, index))
          (fun _ _ same => (Prod.mk.inj same).2), FinDist.prob_condOn]
      by_cases supported : index ∈ prior.support
      · change prior.prob index * (policies index past entry.beforeView).prob entry.action /
          (waiting.prob entry.action * prior.probOf kept) = _
        rw [branches index supported]
        by_cases remains : index ∈ kept
        · rw [ite_eq_left remains, ite_eq_left remains]
          rw [mul_comm (waiting.prob entry.action), mul_div_mul_right _ _
            (ne_of_gt (FinDist.prob_pos_iff.mpr possible))]
        · simp only [remains, ↓reduceIte, FinDist.prob_pure_of_ne different, mul_zero, zero_div]
      · simp only [FinDist.prob_eq_zero_iff.mpr supported, zero_mul, zero_div, ite_self]
    · rw [ite_eq_right (show (reply, index) ∉ Prod.fst ⁻¹' {entry.action} from equal)]
      symm
      apply FinDist.prob_eq_zero_iff.mpr
      intro member
      obtain ⟨old, _, equality⟩ := FinDist.support_map .. ▸ member
      exact equal (congrArg Prod.fst equality).symm
  rw [Implementation.posterior_snoc]
  change (joint.condOnFibre Prod.fst entry.action).map Prod.snd = _
  rw [FinDist.condOnFibre, dite_eq_left actionMeet, conditioned, FinDist.map_comp]
  exact FinDist.map_id _

/-- Slots still available after `count` waiting responses. Never opening is
always retained. -/
def remainingOpeningSlots {slots : Nat} (count : Nat) : Set (Option (Fin slots)) :=
  {selected | match selected with
    | none => True
    | some slot => count ≤ slot.val}

/-- A single lawful waiting response advances an already conditioned timing
posterior. The earlier recall need not be supplied as an explicit word. -/
theorem scheduledMixture_waiting_step {slots : Nat}
    (initial : FinDist (Option (Fin slots))) (never : none ∈ initial.support) (offset : Nat)
    (opening : app.Action) (waiting : app.Policy)
    (different : ∀ past view, opening ∉ (waiting past view).support)
    (past : List app.PlayerEntry) (entry : app.PlayerEntry) (count : Nat)
    (atCount : past.length = offset + count)
    (old : (app.policyMixture initial (fun selected => app.scheduledPolicy offset selected
      (fun _ _ => FinDist.pure opening) waiting)).posterior past =
        initial.condOn (remainingOpeningSlots count) ⟨none, True.intro, never⟩)
    (possible : entry.action ∈ (waiting past entry.beforeView).support) :
    (app.policyMixture initial (fun selected => app.scheduledPolicy offset selected
      (fun _ _ => FinDist.pure opening) waiting)).posterior (past ++ [entry]) =
        initial.condOn (remainingOpeningSlots (count + 1)) ⟨none, True.intro, never⟩ := by
  classical
  let policies := fun selected : Option (Fin slots) =>
    app.scheduledPolicy offset selected (fun _ _ => FinDist.pure opening) waiting
  let mixture := app.policyMixture initial policies
  change mixture.posterior past =
    initial.condOn (remainingOpeningSlots count) ⟨none, True.intro, never⟩ at old
  have meets (next : Nat) : ∃ selected ∈ remainingOpeningSlots next,
      selected ∈ initial.support := ⟨none, True.intro, never⟩
  have nextMeets : ∃ selected ∈ remainingOpeningSlots (count + 1),
      selected ∈ (mixture.posterior past).support := by
    refine ⟨none, True.intro, ?_⟩
    rw [old]
    exact FinDist.mem_support_condOn initial _ _ True.intro never
  have branches (selected : Option (Fin slots))
      (supported : selected ∈ (mixture.posterior past).support) :
      policies selected past entry.beforeView =
        if selected ∈ remainingOpeningSlots (count + 1) then
          waiting past entry.beforeView else FinDist.pure opening := by
    rw [old] at supported
    have retained := (FinDist.support_condOn initial _ _ supported).1
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
  have nested := FinDist.condOn_condOn initial (meets count) (meets (count + 1)) (by
    intro selected member
    rcases member with ⟨remaining, _⟩
    cases selected with
    | none => exact True.intro
    | some slot =>
        change count + 1 ≤ slot.val at remaining
        change count ≤ slot.val
        omega) (by simpa only [old] using nextMeets)
  change (mixture.posterior past).condOn _ nextMeets = _
  simpa only [old] using nested

/-- Every observed replay/silence likelihood cancels. After a lawful waiting
prefix, the actual latent posterior is exactly the original timing law
conditioned on not selecting an earlier slot. -/
theorem scheduledMixture_waiting_posterior {slots : Nat}
    (initial : FinDist (Option (Fin slots))) (never : none ∈ initial.support) (offset : Nat)
    (opening : app.Action) (waiting : app.Policy)
    (different : ∀ past view, opening ∉ (waiting past view).support)
    (past suffix : List app.PlayerEntry) (atStart : past.length = offset)
    (lawful : ∀ before entry after, suffix = before ++ entry :: after →
      entry.action ∈ (waiting (past ++ before) entry.beforeView).support) :
    (app.policyMixture initial (fun selected => app.scheduledPolicy offset selected
      (fun _ _ => FinDist.pure opening) waiting)).posterior (past ++ suffix) =
        initial.condOn (remainingOpeningSlots suffix.length) ⟨none, True.intro, never⟩ := by
  classical
  let policies := fun selected : Option (Fin slots) =>
    app.scheduledPolicy offset selected (fun _ _ => FinDist.pure opening) waiting
  let mixture := app.policyMixture initial policies
  have meets (count : Nat) : ∃ selected ∈ remainingOpeningSlots count,
      selected ∈ initial.support := ⟨none, True.intro, never⟩
  change mixture.posterior (past ++ suffix) =
    initial.condOn (remainingOpeningSlots suffix.length) (meets suffix.length)
  induction suffix using List.reverseRecOn with
  | nil =>
      have dormant := app.policyMixture_posterior_dormant initial policies waiting offset
        (fun selected before view earlier =>
          app.scheduledPolicy_before offset selected _ waiting before view earlier)
        past atStart.le
      have all : remainingOpeningSlots (slots := slots) 0 = Set.univ := by
        ext selected
        cases selected <;> simp [remainingOpeningSlots]
      simp only [List.append_nil, List.length_nil]
      simp only [all, FinDist.condOn_univ]
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
    (timing : FinDist (Fin slots)) (count : Nat) :
    (FinDist.mix probability nonnegative bounded (timing.map some) (FinDist.pure none)).probOf
      (remainingOpeningSlots count) = FinDist.deferredSurvival probability timing count := by
  classical
  rw [← FinDist.expect_indicator_eq_probOf, FinDist.expect_mix, FinDist.expect_map,
    FinDist.expect_pure]
  have retained : timing.expect (fun slot =>
      if some slot ∈ remainingOpeningSlots count then (1 : ℝ) else 0) =
        1 - timing.timingPrefix count := by
    rw [FinDist.expect_eq_sum, ← timing.sum_prob]
    unfold FinDist.timingPrefix
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro slot _
    by_cases before : slot.val < count
    · simp [remainingOpeningSlots, Nat.not_le.mpr before, before]
    · simp [remainingOpeningSlots, Nat.le_of_not_gt before, before, FinDist.sum_prob]
  rw [retained]
  simp only [remainingOpeningSlots, Set.mem_ofPred_eq, ↓reduceIte, mul_one,
    FinDist.deferredSurvival]
  ring

/-- The eventual binary value under the actual waiting posterior. Past
waiting changes the binary probability; it does not simply leave it equal
to the source probability. -/
theorem remainingOpeningSlots_value {slots : Nat} (probability : ℝ)
    (nonnegative : 0 ≤ probability) (small : probability < 1)
    (timing : FinDist (Fin slots)) (count : Nat) (whenTrue whenFalse : ℝ) :
    let initial := FinDist.mix probability nonnegative small.le
      (timing.map some) (FinDist.pure none)
    (initial.condOn (remainingOpeningSlots count) ⟨none, True.intro,
      FinDist.mem_support_mix_right probability nonnegative small.le small (by simp)⟩).expect
        (fun selected => if selected.isSome then whenTrue else whenFalse) =
      FinDist.deferredRemaining probability timing count * whenTrue +
        (1 - FinDist.deferredRemaining probability timing count) * whenFalse := by
  classical
  intro initial
  let post := initial.condOn (remainingOpeningSlots count) ⟨none, True.intro,
    FinDist.mem_support_mix_right probability nonnegative small.le small (by simp)⟩
  have absent : (timing.map some).prob none = 0 := by
    apply FinDist.prob_eq_zero_iff.mpr
    simp only [FinDist.support_map, Set.mem_image, not_exists, not_and]
    intro slot _
    simp
  have noneMass : post.prob none =
      (1 - probability) / FinDist.deferredSurvival probability timing count := by
    change (initial.condOn _ _).prob none = _
    rw [FinDist.prob_condOn,
      ite_eq_left (show none ∈ remainingOpeningSlots count from True.intro)]
    dsimp only [initial]
    rw [remainingOpeningSlots_mass, FinDist.prob_mix, absent, FinDist.prob_pure_self]
    ring
  have values (selected : Option (Fin slots)) :
      (if selected.isSome then whenTrue else whenFalse) =
        whenTrue + if none = selected then whenFalse - whenTrue else 0 := by
    cases selected <;> simp
  change post.expect _ = _
  simp_rw [values]
  rw [FinDist.expect_add, FinDist.expect_const, FinDist.expect_ite_eq, noneMass,
    FinDist.deferredRemaining_eq probability nonnegative small timing count]
  ring

/-- The exact recall-conditioned waiting law has a uniform vanishing value
error. Its bound is independent of how small either source tremble becomes. -/
theorem remainingOpeningSlots_value_error {slots : Nat} (probability : ℝ)
    (nonnegative : 0 ≤ probability) (small : probability < 1)
    (timing : FinDist (Fin slots)) (count : Nat) (whenTrue whenFalse : ℝ) :
    let initial := FinDist.mix probability nonnegative small.le
      (timing.map some) (FinDist.pure none)
    |(initial.condOn (remainingOpeningSlots count) ⟨none, True.intro,
      FinDist.mem_support_mix_right probability nonnegative small.le small (by simp)⟩).expect
        (fun selected => if selected.isSome then whenTrue else whenFalse) -
      (probability * whenTrue + (1 - probability) * whenFalse)| ≤
        timing.timingPrefix count * |whenTrue - whenFalse| := by
  dsimp only
  rw [remainingOpeningSlots_value probability nonnegative small timing count whenTrue whenFalse]
  exact FinDist.deferredRemaining_value_error probability nonnegative small timing count
    whenTrue whenFalse

/-- The real probability of each response under the actual recall-conditioned
policy is its deferred hazard mixture. All replay likelihoods have cancelled. -/
theorem scheduledMixture_probability_of_posterior {slots : Nat}
    (probability : ℝ) (nonnegative : 0 ≤ probability) (small : probability < 1)
    (timing : FinDist (Fin slots)) (offset : Nat) (opening : app.Action) (waiting : app.Policy)
    (past : List app.PlayerEntry) (slot : Fin slots)
    (atSlot : past.length = offset + slot.val)
    (posterior :
      (app.policyMixture
        (FinDist.mix probability nonnegative small.le (timing.map some) (FinDist.pure none))
        (fun selected => app.scheduledPolicy offset selected
          (fun _ _ => FinDist.pure opening) waiting)).posterior past =
        (FinDist.mix probability nonnegative small.le (timing.map some) (FinDist.pure none)).condOn
          (remainingOpeningSlots slot.val) ⟨none, True.intro,
            FinDist.mem_support_mix_right probability nonnegative small.le small (by simp)⟩)
    (view : app.PlayerView) (action : app.Action) :
    let initial := FinDist.mix probability nonnegative small.le
      (timing.map some) (FinDist.pure none)
    let policies := fun selected => app.scheduledPolicy offset selected
      (fun _ _ => FinDist.pure opening) waiting
    ((app.policyMixture initial policies).policy past view).prob action =
      FinDist.deferredHazard probability timing slot.val * (FinDist.pure opening).prob action +
        (1 - FinDist.deferredHazard probability timing slot.val) *
          (waiting past view).prob action := by
  classical
  dsimp only
  let initial := FinDist.mix probability nonnegative small.le
    (timing.map some) (FinDist.pure none)
  let policies := fun selected : Option (Fin slots) => app.scheduledPolicy offset selected
    (fun _ _ => FinDist.pure opening) waiting
  have never : none ∈ initial.support :=
    FinDist.mem_support_mix_right probability nonnegative small.le small (by simp)
  let post := initial.condOn (remainingOpeningSlots slot.val) ⟨none, True.intro, never⟩
  change (app.policyMixture initial policies).posterior past = post at posterior
  have mass : post.prob (some slot) = FinDist.deferredHazard probability timing slot.val := by
    rw [FinDist.deferredHazard_at]
    dsimp only [post]
    rw [FinDist.prob_condOn, ite_eq_left
      (show some slot ∈ remainingOpeningSlots slot.val from by
        change slot.val ≤ slot.val
        exact le_rfl)]
    rw [remainingOpeningSlots_mass, FinDist.prob_mix,
      FinDist.prob_map_of_injective some (Option.some_injective _),
      FinDist.prob_pure_of_ne (by simp : some slot ≠ none), mul_zero, add_zero]
  rw [app.policyMixture_policy]
  change (((app.policyMixture initial policies).posterior past).bind
    (fun selected => policies selected past view)).prob action = _
  rw [posterior, FinDist.prob_bind]
  have laws (selected : Option (Fin slots)) :
      policies selected past view =
        if selected = some slot then FinDist.pure opening else waiting past view := by
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
    _ = post.expect (fun selected => (waiting past view).prob action +
        if some slot = selected then
          (FinDist.pure opening).prob action - (waiting past view).prob action
        else 0) := by
      apply FinDist.expect_congr
      intro selected _
      rw [laws]
      by_cases equal : selected = some slot
      · subst selected
        simp only [↓reduceIte]
        ring
      · simp only [equal, Ne.symm equal, ↓reduceIte, add_zero]
    _ = _ := by
      rw [FinDist.expect_add, FinDist.expect_const, FinDist.expect_ite_eq, mass]
      ring

theorem scheduledMixture_waiting_probability {slots : Nat}
    (probability : ℝ) (nonnegative : 0 ≤ probability) (small : probability < 1)
    (timing : FinDist (Fin slots)) (offset : Nat) (opening : app.Action) (waiting : app.Policy)
    (different : ∀ past view, opening ∉ (waiting past view).support)
    (past suffix : List app.PlayerEntry) (atStart : past.length = offset)
    (slot : Fin slots) (atSlot : suffix.length = slot.val)
    (lawful : ∀ before entry after, suffix = before ++ entry :: after →
      entry.action ∈ (waiting (past ++ before) entry.beforeView).support)
    (view : app.PlayerView) (action : app.Action) :
    let initial := FinDist.mix probability nonnegative small.le
      (timing.map some) (FinDist.pure none)
    let policies := fun selected => app.scheduledPolicy offset selected
      (fun _ _ => FinDist.pure opening) waiting
    ((app.policyMixture initial policies).policy (past ++ suffix) view).prob action =
      FinDist.deferredHazard probability timing slot.val * (FinDist.pure opening).prob action +
        (1 - FinDist.deferredHazard probability timing slot.val) *
          (waiting (past ++ suffix) view).prob action := by
  dsimp only
  let initial := FinDist.mix probability nonnegative small.le
    (timing.map some) (FinDist.pure none)
  have never : none ∈ initial.support :=
    FinDist.mem_support_mix_right probability nonnegative small.le small (by simp)
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
    (timing : Nat → FinDist (Fin (last + 1)))
    (timingConverges : FinDistConvergesPointwise timing (FinDist.pure (Fin.last last)))
    (offset : Nat) (opening : app.Action) (waiting : app.Policy)
    (different : ∀ past view, opening ∉ (waiting past view).support)
    (past suffix : List app.PlayerEntry) (atStart : past.length = offset)
    (slot : Fin (last + 1)) (atSlot : suffix.length = slot.val)
    (lawful : ∀ before entry after, suffix = before ++ entry :: after →
      entry.action ∈ (waiting (past ++ before) entry.beforeView).support)
    (view : app.PlayerView) :
    FinDistConvergesPointwise (fun n =>
      let initial := FinDist.mix (probability n) (nonnegative n) (small n).le
        ((timing n).map some) (FinDist.pure none)
      let policies := fun selected => app.scheduledPolicy offset selected
        (fun _ _ => FinDist.pure opening) waiting
      (app.policyMixture initial policies).policy (past ++ suffix) view)
      (if slot = Fin.last last then
        FinDist.mix limit limitNonnegative limitBounded (FinDist.pure opening)
          (waiting (past ++ suffix) view)
      else waiting (past ++ suffix) view) := by
  intro action
  dsimp only
  have hazard := FinDist.deferredHazard_tendsto_last probabilityConverges timingConverges slot
  have one : Filter.Tendsto (fun _ : Nat => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have combined := (hazard.mul_const ((FinDist.pure opening).prob action)).add
    ((one.sub hazard).mul_const ((waiting (past ++ suffix) view).prob action))
  have actual := combined.congr' (Filter.Eventually.of_forall (fun n =>
    (app.scheduledMixture_waiting_probability (probability n) (nonnegative n) (small n)
      (timing n) offset opening waiting different past suffix atStart slot atSlot lawful
        view action).symm))
  by_cases final : slot = Fin.last last
  · simpa only [final, ↓reduceIte, FinDist.prob_mix] using actual
  · simpa only [final, ↓reduceIte, zero_mul, sub_zero, one_mul, zero_add] using actual

/-- After any legal opening, the common fully supported sequence is already
constant at the waiting policy. This includes early openings that have zero
probability in the limiting last-slot strategy. -/
theorem scheduledMixture_opened_limit {slots : Nat}
    (initial : Nat → FinDist (Option (Fin slots))) (full : ∀ n, (initial n).FullSupport)
    (offset : Nat) (opening : app.Action) (waiting : app.Policy)
    (different : ∀ past view, opening ∉ (waiting past view).support)
    (past before : List app.PlayerEntry) (atStart : past.length = offset)
    (slot : Fin slots) (atSlot : before.length = slot.val)
    (lawful : ∀ earlier entry after, before = earlier ++ entry :: after →
      entry.action ∈ (waiting (past ++ earlier) entry.beforeView).support)
    (entry : app.PlayerEntry) (opened : entry.action = opening)
    (after : List app.PlayerEntry) (view : app.PlayerView) :
    FinDistConvergesPointwise (fun n =>
      (app.policyMixture (initial n) (fun selected => app.scheduledPolicy offset selected
        (fun _ _ => FinDist.pure opening) waiting)).policy
          (past ++ before ++ [entry] ++ after) view)
      (waiting (past ++ before ++ [entry] ++ after) view) := by
  have same (n : Nat) :
      (app.policyMixture (initial n) (fun selected => app.scheduledPolicy offset selected
        (fun _ _ => FinDist.pure opening) waiting)).policy
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
