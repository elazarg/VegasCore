/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastFirstLateOccupation
import Interaction.ReactiveServiceRounds
import Interaction.ReactiveMenuOccupation
import Interaction.ReactiveControlOccupation

/-! # Exact occupation of the retained second native response -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

abbrev NativeInput := Option (List app.PlayerEntry × app.PlayerView)

private def clockTwoValue (value : NativeInput → ℝ) (past : List app.PlayerEntry)
    (view : app.PlayerView) : ℝ :=
  if view.application.2.native.clock = 2 then value (some (past, view)) else 0

/-- Only the second own record is counted. Its value stays fixed through every
later raw response, including retries and publication. -/
def secondResponseValue (owner : Player) (value : NativeInput → ℝ)
    (execution : app.Execution) : ℝ :=
  match execution.recall owner with
  | first :: second :: _ => clockTwoValue value [first] second.beforeView
  | _ => 0

/-- The reward is evaluated at the actual pre-response native decision. -/
def secondResponseReward (owner : Player) (value : NativeInput → ℝ) : app.ProtocolState → ℝ
  | none => 0
  | some current =>
      if current.actor = some owner ∧ (current.execution.recall owner).length = 1 then
        clockTwoValue value (current.execution.recall owner)
          (current.execution.observe app owner) else 0

private theorem clockTwoValue_abs_le (value : NativeInput → ℝ)
    {bound : ℝ} (nonnegative : 0 ≤ bound) (bounded : ∀ input, |value input| ≤ bound)
    (past : List app.PlayerEntry) (view : app.PlayerView) :
    |clockTwoValue value past view| ≤ bound := by
  unfold clockTwoValue
  split_ifs
  · exact bounded _
  · simpa only [abs_zero] using nonnegative

theorem secondResponseValue_abs_le (owner : Player) (value : NativeInput → ℝ)
    {bound : ℝ} (nonnegative : 0 ≤ bound) (bounded : ∀ input, |value input| ≤ bound)
    (execution : app.Execution) : |secondResponseValue owner value execution| ≤ bound := by
  unfold secondResponseValue
  cases execution.recall owner with
  | nil => simpa only [abs_zero] using nonnegative
  | cons first later =>
      cases later with
      | nil => simpa only [abs_zero] using nonnegative
      | cons second tail => exact clockTwoValue_abs_le value nonnegative bounded _ second.beforeView

theorem secondResponseReward_abs_le (owner : Player) (value : NativeInput → ℝ)
    {bound : ℝ} (nonnegative : 0 ≤ bound) (bounded : ∀ input, |value input| ≤ bound)
    (state : app.ProtocolState) : |secondResponseReward owner value state| ≤ bound := by
  cases state with
  | none => simpa only [secondResponseReward, abs_zero] using nonnegative
  | some current =>
      dsimp only [secondResponseReward]
      split_ifs
      · exact clockTwoValue_abs_le value nonnegative bounded _ _
      · simpa only [abs_zero] using nonnegative

private theorem secondResponseValue_respond (owner actor : Player) (value : NativeInput → ℝ)
    (execution : app.Execution) (action : app.Action) (remaining : Nat) :
    secondResponseValue owner value (execution.respond app actor action) =
      secondResponseValue owner value execution +
        secondResponseReward owner value (some ⟨remaining, some actor, execution⟩) := by
  by_cases same : owner = actor
  · subst actor
    obtain ⟨emitted, word⟩ := app.respond_recall_entry execution owner action
    unfold secondResponseValue secondResponseReward
    rw [word]
    cases past : execution.recall owner with
    | nil => simp [past]
    | cons first later =>
        cases later with
        | nil => simp [past]
        | cons second tail => simp [past]
  · rw [show secondResponseValue owner value (execution.respond app actor action) =
        secondResponseValue owner value execution by
          unfold secondResponseValue
          rw [app.respond_recall_other execution actor owner same action]]
    simp only [secondResponseReward, Option.some.injEq, Ne.symm same, false_and,
      ite_false, add_zero]

private theorem secondResponseValue_environment (owner : Player) (value : NativeInput → ℝ)
    (execution active : app.Execution) (command : app.Command)
    (reached : active ∈ (execution.environmentStep app command).support) :
    secondResponseValue owner value active = secondResponseValue owner value execution := by
  unfold secondResponseValue
  rw [app.environmentStep_recall execution active command reached]

private theorem resume_secondResponseValue (owner : Player) (value : NativeInput → ℝ)
    (players : Player → app.Policy) (actor : Option Player) (remaining : Nat)
    (execution : app.Execution) :
    expect (app.resume players actor execution) (secondResponseValue owner value) =
      secondResponseValue owner value execution +
        secondResponseReward owner value (some ⟨remaining, actor, execution⟩) := by
  cases actor with
  | none => simp only [ReactiveApplication.resume, expect_pure, secondResponseReward,
      reduceCtorEq, false_and, ite_false, add_zero]
  | some actor =>
      change expect ((players actor (execution.recall actor) (execution.observe app actor)).map
        (execution.respond app actor)) (secondResponseValue owner value) = _
      rw [expect_map]
      calc
        _ = expect (players actor (execution.recall actor) (execution.observe app actor))
            (fun _ => secondResponseValue owner value execution +
              secondResponseReward owner value (some ⟨remaining, some actor, execution⟩)) :=
          expect_congr_on_support fun action _ =>
            secondResponseValue_respond owner actor value execution action remaining
        _ = _ := expect_constant _ _

private theorem round_secondResponseValue (owner : Player) (value : NativeInput → ℝ)
    {bound : ℝ} (nonnegative : 0 ≤ bound) (bounded : ∀ input, |value input| ≤ bound)
    (selected : app.Scheduler) (players : Player → app.Policy) (remaining : Nat)
    (execution : app.Execution) :
    expect (app.round selected players execution) (secondResponseValue owner value) =
      secondResponseValue owner value execution +
        app.roundDecisionReward selected (secondResponseReward owner value) remaining
          execution := by
  unfold ReactiveApplication.round
  rw [expect_bind_tower_bounded _ _ _
    (secondResponseValue_abs_le owner value nonnegative bounded)]
  have inner (command : app.Command) :
      expect (app.dispatch players command execution) (secondResponseValue owner value) =
        secondResponseValue owner value execution +
          expect (execution.environmentStep app command) (fun active =>
            secondResponseReward owner value (some ⟨remaining, command.actor? app, active⟩)) := by
    unfold ReactiveApplication.dispatch
    rw [expect_bind_tower_bounded _ _ _
      (secondResponseValue_abs_le owner value nonnegative bounded)]
    calc
      _ = expect (execution.environmentStep app command) (fun active =>
          secondResponseValue owner value execution +
            secondResponseReward owner value (some ⟨remaining, command.actor? app, active⟩)) := by
        apply expect_congr_on_support
        intro active reached
        rw [resume_secondResponseValue,
          secondResponseValue_environment owner value execution active command reached]
      _ = _ := by
        rw [expect_add (payoffIntegrable_constant _ _) (payoffIntegrable_of_bounded _ _
          fun active => secondResponseReward_abs_le owner value nonnegative bounded _),
          expect_constant]
  simp_rw [inner]
  rw [expect_add (payoffIntegrable_constant _ _) (payoffIntegrable_of_bounded _ _
    fun command => expect_abs_le_of_bounded nonnegative fun active =>
      secondResponseReward_abs_le owner value nonnegative bounded _), expect_constant]
  rfl

/-- This is the exact existing round occupation, with one bounded potential
for the second retained response; it does not reconstruct a decision game. -/
theorem runRounds_secondResponseValue (owner : Player) (value : NativeInput → ℝ)
    {bound : ℝ} (nonnegative : 0 ≤ bound) (bounded : ∀ input, |value input| ≤ bound)
    (selected : app.Scheduler) (players : Player → app.Policy) (count : Nat)
    (execution : app.Execution) :
    expect (app.runRounds selected players count execution) (secondResponseValue owner value) =
      secondResponseValue owner value execution +
        app.roundOccupation selected players (secondResponseReward owner value) count
          execution := by
  induction count generalizing execution with
  | zero => simp only [ReactiveApplication.runRounds, expect_pure,
      ReactiveApplication.roundOccupation, add_zero]
  | succ count ih =>
      rw [ReactiveApplication.runRounds, expect_bind_tower_bounded _ _ _
        (secondResponseValue_abs_le owner value nonnegative bounded)]
      simp_rw [ih]
      rw [expect_add (payoffIntegrable_of_bounded _ _
        (secondResponseValue_abs_le owner value nonnegative bounded))
        (payoffIntegrable_of_bounded _ _
          (app.roundOccupation_abs_le selected players (secondResponseReward owner value)
            nonnegative (secondResponseReward_abs_le owner value nonnegative bounded) count)),
        round_secondResponseValue owner value nonnegative bounded selected players count execution,
        app.roundOccupation_succ selected players (secondResponseReward owner value)
          nonnegative (secondResponseReward_abs_le owner value nonnegative bounded)]
      ring

/-- Selector mass is actual pre-response occupation, for every bounded function
of the full input and every literal raw behavioral response law. -/
theorem initialized_firstLate_occupation (seed : Seeds) (players : Player → app.Policy)
    (waited : ∀ owner, players owner ((initialCallback owner).recall owner)
      ((initialCallback owner).observe app owner) = PMF.pure ⟨none⟩)
    (owner : Player) (value : NativeInput → ℝ) {bound : ℝ} (nonnegative : 0 ≤ bound)
    (bounded : ∀ input, |value input| ≤ bound) :
    expect (app.runRounds (family seed) players 14 initialExecution)
        (fun final => value (firstLateInput owner final)) =
      app.roundOccupation (family seed) players (secondResponseReward owner value)
        14 initialExecution := by
  have actual := runRounds_secondResponseValue owner value nonnegative bounded
    (family seed) players 14 initialExecution
  have initialZero : secondResponseValue owner value initialExecution = 0 := rfl
  rw [initialZero, zero_add] at actual
  refine (expect_congr_on_support fun final reached => ?_).trans actual
  obtain ⟨entry, word, publicView, selected⟩ :=
    initialized_firstLate_own_word seed players waited final reached owner
  have clock : entry.beforeView.application.2.native.clock = 2 :=
    (congrArg (fun view : PhasePublicView graph => view.native.clock) publicView).trans
      quietStart_clock
  rw [selected]
  simp only [secondResponseValue, word, clockTwoValue, clock, ite_true]

/-- Once both records exist their value is invariant under every actual raw
continuation, with the complete old word retained. -/
theorem secondResponseValue_after_two (owner : Player) (value : NativeInput → ℝ)
    (selected : app.Scheduler) (players : Player → app.Policy) (count : Nat)
    (execution final : app.Execution) (first second : app.PlayerEntry)
    (word : execution.recall owner = [first, second])
    (reached : final ∈ (app.runRounds selected players count execution).support) :
    secondResponseValue owner value final = secondResponseValue owner value execution := by
  let valid := fun next : app.Execution => [first, second] <+: next.recall owner
  have invariant : app.ServiceInvariant selected valid := by
    constructor
    · intro before actor action past
      exact past.trans (app.respond_recall_prefix before actor owner action)
    · intro before after command past _selected moved
      change [first, second] <+: after.recall owner
      rw [app.environmentStep_recall before after command moved]
      exact past
  have retained := invariant.runRounds players count execution final
    (by change [first, second] <+: execution.recall owner; rw [word]) reached
  obtain ⟨later, same⟩ := retained
  unfold secondResponseValue
  rw [← same, word]
  rfl

/-- Starting after the actual quiet initial prefix needs no prescription at
the initial callbacks: all remaining behavioral laws are arbitrary. -/
theorem quietStart_firstLate_occupation (seed : Seeds) (players : Player → app.Policy)
    (owner : Player) (value : NativeInput → ℝ) {bound : ℝ} (nonnegative : 0 ≤ bound)
    (bounded : ∀ input, |value input| ≤ bound) :
    expect (app.runRounds (family seed) players 9 quietStart)
        (fun final => value (firstLateInput owner final)) =
      app.roundOccupation (family seed) players (secondResponseReward owner value)
        9 quietStart := by
  have actual := runRounds_secondResponseValue owner value nonnegative bounded
    (family seed) players 9 quietStart
  have initialZero : secondResponseValue owner value quietStart = 0 := by
    unfold secondResponseValue
    rw [quietStart_recall]
  rw [initialZero, zero_add] at actual
  refine (expect_congr_on_support fun final reached => ?_).trans actual
  have projected : physicalExecution final ∈
      ((app.runRounds (family seed) players 9 quietStart).map physicalExecution).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨final, reached, rfl⟩
  rw [nohelper_first_late_physical_kernel] at projected
  obtain ⟨entry, word, publicView⟩ := physicalCallbacks_unique_record players _
    (nativePartitionedOrder_nodup seed) owner (nativePartitionedOrder_mem seed owner)
      quietStart (physicalExecution final) projected
  change final.recall owner = quietStart.recall owner ++ [entry] at word
  rw [quietStart_recall] at word
  have clock : entry.beforeView.application.2.native.clock = 2 :=
    (congrArg (fun view : PhasePublicView graph => view.native.clock) publicView).trans
      quietStart_clock
  rw [firstLateInput, word]
  change value (some ([initialWaitEntry owner], entry.beforeView)) = _
  simp only [secondResponseValue, word, List.singleton_append, clockTwoValue, clock, ite_true]

/-- Later commands have exactly zero additional reward. Thus the input law at
fourteen commands is the occupation of the entire original native horizon. -/
theorem initialized_full_firstLate_occupation (seed : Seeds) (players : Player → app.Policy)
    (waited : ∀ owner, players owner ((initialCallback owner).recall owner)
      ((initialCallback owner).observe app owner) = PMF.pure ⟨none⟩)
    (owner : Player) (value : NativeInput → ℝ) {bound : ℝ} (nonnegative : 0 ≤ bound)
    (bounded : ∀ input, |value input| ≤ bound) :
    expect (app.runRounds (family seed) players 14 initialExecution)
        (fun final => value (firstLateInput owner final)) =
      app.roundOccupation (family seed) players (secondResponseReward owner value)
        horizon initialExecution := by
  have full := runRounds_secondResponseValue owner value nonnegative bounded
    (family seed) players horizon initialExecution
  have initialZero : secondResponseValue owner value initialExecution = 0 := rfl
  rw [initialZero, zero_add] at full
  refine (initialized_firstLate_occupation seed players waited owner value
    nonnegative bounded).trans ?_
  rw [← full, ← initialized_firstLate_occupation seed players waited owner value
    nonnegative bounded]
  rw [show horizon = 14 + (horizon - 14) by decide, app.runRounds_add,
    expect_bind_tower_bounded _ _ _ (secondResponseValue_abs_le owner value nonnegative bounded)]
  apply expect_congr_on_support
  intro execution reached
  obtain ⟨entry, word, publicView, selected⟩ :=
    initialized_firstLate_own_word seed players waited execution reached owner
  have stable : expect (app.runRounds (family seed) players (horizon - 14) execution)
      (secondResponseValue owner value) = secondResponseValue owner value execution := by
    trans expect (app.runRounds (family seed) players (horizon - 14) execution)
      (fun _ => secondResponseValue owner value execution)
    · exact expect_congr_on_support fun final future =>
        secondResponseValue_after_two owner value (family seed) players _ execution final
          (initialWaitEntry owner) entry word future
    · exact expect_constant _ _
  rw [stable, selected]
  have clock : entry.beforeView.application.2.native.clock = 2 :=
    (congrArg (fun view : PhasePublicView graph => view.native.clock) publicView).trans
      quietStart_clock
  simp only [secondResponseValue, word, clockTwoValue, clock, ite_true]

/-- Original seed mixing retains the exact unnormalized decision occupation;
the uniform-command sampling factor has not been inserted. -/
theorem native_firstLate_occupation (players : Player → app.Policy)
    (waited : ∀ owner, players owner ((initialCallback owner).recall owner)
      ((initialCallback owner).observe app owner) = PMF.pure ⟨none⟩)
    (owner : Player) (value : NativeInput → ℝ) {bound : ℝ} (nonnegative : 0 ≤ bound)
    (bounded : ∀ input, |value input| ≤ bound) :
    expect nativeSeedLaw (fun seed =>
      expect (app.runRounds (family seed) players 14 initialExecution)
        (fun final => value (firstLateInput owner final))) =
      app.roundOccupation scheduler players (secondResponseReward owner value)
        horizon initialExecution := by
  have full := runRounds_secondResponseValue owner value nonnegative bounded scheduler players
    horizon initialExecution
  have initialZero : secondResponseValue owner value initialExecution = 0 := rfl
  rw [initialZero, zero_add] at full
  rw [← full]
  have law := app.schedulerMixture_realize nativeSeedLaw family players horizon initialState
  change (nativeSeedLaw.bind fun seed => app.runRounds (family seed) players horizon
    initialExecution) = app.runRounds scheduler players horizon initialExecution at law
  rw [← law, expect_bind_tower_bounded _ _ _
    (secondResponseValue_abs_le owner value nonnegative bounded)]
  apply expect_congr_on_support
  intro seed _supported
  have fixed := runRounds_secondResponseValue owner value nonnegative bounded
    (family seed) players horizon initialExecution
  rw [initialZero, zero_add] at fixed
  exact (initialized_full_firstLate_occupation seed players waited owner value
    nonnegative bounded).trans fixed.symm

/-- The genuine original information-history reach sum equals the retained
first-late input mass. Finiteness here is the existing raw-menu history instance. -/
theorem native_firstLate_historyReach [Fintype rawProtocol.History]
    (profile : ∀ owner, rawModel.BehavioralPolicy owner)
    (waited : ∀ owner,
      rawMenu.decodeProfile initial horizon scheduler profile owner
        ((initialCallback owner).recall owner) ((initialCallback owner).observe app owner) =
          PMF.pure ⟨none⟩)
    (owner : Player) (value : NativeInput → ℝ) {bound : ℝ} (nonnegative : 0 ≤ bound)
    (bounded : ∀ input, |value input| ≤ bound) :
    (∑ history : rawProtocol.History,
      (rawModel.historyReachWeight profile history).toReal *
        secondResponseReward owner value history.state) =
      expect nativeSeedLaw (fun seed =>
        expect (app.runRounds (family seed)
          (rawMenu.decodeProfile initial horizon scheduler profile) 14 initialExecution)
            (fun final => value (firstLateInput owner final))) := by
  have actual := rawMenu.sum_historyReach_reward_eq_roundOccupation initial horizon scheduler
    profile (secondResponseReward owner value) nonnegative
      (secondResponseReward_abs_le owner value nonnegative bounded)
      (fun _ _ => by simp only [secondResponseReward, reduceCtorEq, false_and, ite_false]) rfl
  let players := rawMenu.decodeProfile initial horizon scheduler profile
  have initialized :
      expect initial (fun state => app.roundOccupation scheduler players
        (secondResponseReward owner value) horizon
          (ReactiveApplication.Execution.initial app state)) =
      app.roundOccupation scheduler players (secondResponseReward owner value)
        horizon initialExecution := by
    change expect (PMF.pure initialState) _ = _
    rw [expect_pure]
    rfl
  exact actual.trans (initialized.trans
    (native_firstLate_occupation players waited owner value nonnegative bounded).symm)

/-- The existing command occupation samples one of the original horizon's
commands uniformly. This displays its precise normalization factor. -/
theorem fixed_firstLate_controlOccupation [NeZero horizon]
    (seed : Seeds) (players : Player → app.Policy)
    (waited : ∀ owner, players owner ((initialCallback owner).recall owner)
      ((initialCallback owner).observe app owner) = PMF.pure ⟨none⟩)
    (owner : Player) (value : NativeInput → ℝ) {bound : ℝ} (nonnegative : 0 ≤ bound)
    (bounded : ∀ input, |value input| ≤ bound) :
    expect (app.occupationControlLaw (family seed) players initial horizon)
        (secondResponseReward owner value) =
      expect (app.runRounds (family seed) players 14 initialExecution)
        (fun final => value (firstLateInput owner final)) / horizon := by
  rw [app.expect_occupationControlLaw (family seed) players initial horizon
    (secondResponseReward owner value) nonnegative
      (secondResponseReward_abs_le owner value nonnegative bounded), initial, expect_pure]
  exact congrArg (fun total : ℝ => total / horizon)
    (initialized_full_firstLate_occupation seed players waited owner value
      nonnegative bounded).symm

end Vegas.Examples.CommitSeedBroadcast
