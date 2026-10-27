/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.OddsEvensRecoveryClock
import Interaction.ReactiveAnchoredTrace

/-! # Expiry gives a finite completion budget for the forced-exit service -/

noncomputable section

namespace Vegas.Examples.OddsEvensRecoveryService

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability

private theorem every_event_owned (event : compiled.EventId) :
    (compiled.actor? event).isSome = true := by
  fin_cases event <;> rfl

theorem window_completes_ready (inputs : compiled.Inputs) (players : OddsEvens.Player → app.Policy)
    (cycle : Nat) (before after : app.Execution) (aligned : ClockAligned inputs 0 before)
    (cursor : before.environmentRecall.length = cycle * width)
    (event : compiled.EventId) (ready : before.application.native.config.cut.Ready event)
    (reached : after ∈ (app.runRounds scheduler players (8 * width) before).support) :
    event ∈ after.application.native.config.cut.completed := by
  have active := (aligned.valid.native.activated_iff event).mpr ⟨ready, every_event_owned event⟩
  obtain ⟨entered, activated⟩ := Option.isSome_iff_exists.mp active
  have beforeClock : before.application.native.clock = cycle := by
    rw [aligned.clock, cursor, Nat.zero_add]
    simpa only [Nat.add_zero] using (cursor_arithmetic cycle 0 (by decide)).1
  have enteredBound := aligned.valid.native.activated_le event entered activated
  rw [beforeClock] at enteredBound
  have eventBound : event.val < 4 := event.isLt
  let prefixRounds := 6 * width + (packetBudget + 2 + event.val)
  let tail := 8 * width - prefixRounds - 1
  have room : prefixRounds < 8 * width := by
    dsimp [prefixRounds, width, packetBudget, cycles]
    omega
  have splitCount : 8 * width = prefixRounds + (tail + 1) := by dsimp [tail]; omega
  rw [splitCount, app.runRounds_add] at reached
  obtain ⟨middle, prefixReached, suffixReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have middleAligned := (clock_aligned_invariant inputs 0).runRounds players prefixRounds
    before middle aligned prefixReached
  obtain ⟨_, prefixProgress⟩ := Recovery.runRounds_progress runtime leaks inputs scheduler players
    prefixRounds before middle aligned.valid.native prefixReached
  have middleCursor : middle.environmentRecall.length =
      (cycle + 6) * width + (packetBudget + 2 + event.val) := by
    rw [app.runRounds_environmentRecall_length scheduler players prefixRounds before middle
      prefixReached, cursor]
    dsimp [prefixRounds]
    ring
  have middleClock : middle.application.native.clock = cycle + 6 := by
    rw [middleAligned.clock, Nat.zero_add, middleCursor]
    exact (cursor_arithmetic (cycle + 6) (packetBudget + 2 + event.val) (by
      change 64 + 2 + event.val < 71
      omega)).1
  have roundEq : app.round scheduler players middle =
      app.dispatch players (.application (.expire event)) middle := by
    simp only [ReactiveApplication.round, scheduler, PMF.pure_bind]
    rw [middleCursor, expire_command]
  change after ∈ ((app.round scheduler players middle).bind
    (app.runRounds scheduler players tail)).support at suffixReached
  rw [roundEq] at suffixReached
  obtain ⟨expired, moved, finalReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ suffixReached)
  have expiredReached : expired ∈
      (middle.environmentStep app (.application (.expire event))).support := by
    change expired ∈ ((middle.environmentStep app (.application (.expire event))).bind
      (fun execution => PMF.pure execution)).support at moved
    simpa only [PMF.bind_pure] using moved
  obtain ⟨_, suffixProgress⟩ := Recovery.runRounds_progress runtime leaks inputs scheduler players
    tail expired after
      (Recovery.environmentStep_progress runtime leaks inputs middle expired
        (.application (.expire event)) middleAligned.valid.native expiredReached).invariant
      finalReached
  by_cases done : event ∈ middle.application.native.config.cut.completed
  · have step := Recovery.environmentStep_progress runtime leaks inputs middle expired
      (.application (.expire event)) middleAligned.valid.native expiredReached
    exact suffixProgress.completed (step.completed done)
  · have stillReady := (prefixProgress.ready_or_completed event ready).resolve_left done
    have stillActivated := prefixProgress.activated event entered activated done
    have due : runtime.deadline event ≤ middle.application.native.clock - entered := by
      change 6 ≤ middle.application.native.clock - entered
      rw [middleClock]
      omega
    obtain ⟨updated, observed, rfl⟩ := PMF.support_map .. ▸ expiredReached
    obtain ⟨native, nativeMoved, rfl⟩ := PMF.support_map .. ▸ observed
    have completed := middle.application.expire_complete runtime native middleAligned.valid.native
      event stillReady (every_event_owned event) entered stillActivated due nativeMoved
    exact suffixProgress.completed completed

theorem nonterminal_window_progress (inputs : compiled.Inputs)
    (players : OddsEvens.Player → app.Policy) (cycle : Nat) (before after : app.Execution)
    (aligned : ClockAligned inputs 0 before)
    (cursor : before.environmentRecall.length = cycle * width)
    (reached : after ∈ (app.runRounds scheduler players (8 * width) before).support)
    (unfinished : ¬ after.application.native.config.cut.Terminal) :
    before.application.native.config.cut.completed.card + 1 ≤
      after.application.native.config.cut.completed.card := by
  obtain ⟨_, progress⟩ := Recovery.runRounds_progress runtime leaks inputs scheduler players
    (8 * width) before after aligned.valid.native reached
  have beforeUnfinished : ¬ before.application.native.config.cut.Terminal := by
    intro finished
    apply unfinished
    exact Finset.eq_univ_iff_forall.mpr fun event =>
      progress.completed (Finset.eq_univ_iff_forall.mp finished event)
  obtain ⟨event, ready⟩ := before.application.native.config.cut.exists_ready_of_not_terminal
    beforeUnfinished
  have completed := window_completes_ready inputs players cycle before after aligned cursor
    event ready reached
  have strict : before.application.native.config.cut.completed ⊂
      after.application.native.config.cut.completed := by
    exact Finset.ssubset_iff_subset_ne.mpr ⟨progress.completed, fun equal =>
      ready.1 (equal ▸ completed)⟩
  exact Nat.succ_le_of_lt (Finset.card_lt_card strict)

theorem windows_card_bound (inputs : compiled.Inputs) (players : OddsEvens.Player → app.Policy)
    (blocks cycle : Nat) (before after : app.Execution) (aligned : ClockAligned inputs 0 before)
    (cursor : before.environmentRecall.length = cycle * width)
    (reached : after ∈ (app.runRounds scheduler players (blocks * (8 * width)) before).support)
    (unfinished : ¬ after.application.native.config.cut.Terminal) :
    before.application.native.config.cut.completed.card + blocks ≤
      after.application.native.config.cut.completed.card := by
  induction blocks generalizing cycle before after with
  | zero =>
      simp only [ReactiveApplication.runRounds, PMF.mem_support_pure_iff _ _]
        at reached
      subst after
      omega
  | succ blocks ih =>
      have splitCount : (blocks + 1) * (8 * width) =
          8 * width + blocks * (8 * width) := by ring
      rw [splitCount, app.runRounds_add] at reached
      obtain ⟨middle, firstReached, finalReached⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have middleAligned := (clock_aligned_invariant inputs 0).runRounds players (8 * width)
        before middle aligned firstReached
      obtain ⟨_, later⟩ := Recovery.runRounds_progress runtime leaks inputs scheduler players
        (blocks * (8 * width)) middle after middleAligned.valid.native finalReached
      have middleUnfinished : ¬ middle.application.native.config.cut.Terminal := by
        intro finished
        apply unfinished
        exact Finset.eq_univ_iff_forall.mpr fun event =>
          later.completed (Finset.eq_univ_iff_forall.mp finished event)
      have strict := nonterminal_window_progress inputs players cycle before middle aligned
        cursor firstReached middleUnfinished
      have middleCursor : middle.environmentRecall.length = (cycle + 8) * width := by
        rw [app.runRounds_environmentRecall_length scheduler players (8 * width) before middle
          firstReached, cursor]
        ring
      have bound := ih (cycle + 8) middle after middleAligned middleCursor finalReached unfinished
      omega

theorem runRounds_complete (inputs : compiled.Inputs) (players : OddsEvens.Player → app.Policy)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds scheduler players horizon
      (ReactiveApplication.Execution.initial app ⟨State.initial inputs, ∅⟩)).support) :
    final.application.native.config.cut.Terminal := by
  by_contra unfinished
  have aligned : ClockAligned inputs 0
      (ReactiveApplication.Execution.initial app ⟨State.initial inputs, ∅⟩) :=
    ⟨RecoveryState.Invariant.initial _, by
      simp [ReactiveApplication.Execution.initial, State.initial]⟩
  have bound := windows_card_bound inputs players 4 0 _ final aligned (by rfl) reached unfinished
  apply unfinished
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  change 4 ≤ final.application.native.config.cut.completed.card
  omega

theorem completesPlay : Recovery.CompletesPlay runtime leaks initial horizon scheduler := by
  intro current trace terminal
  rcases current with ⟨remaining, actor, execution⟩
  obtain ⟨rfl, rfl⟩ := terminal
  let players : OddsEvens.Player → app.Policy := fun _ => app.silentPolicy
  obtain ⟨_, supported⟩ := app.mem_roundsFrom_anchoredPolicy_of_trace initial horizon scheduler
    players trace
  change execution ∈ (initial.bind fun state => app.runRounds scheduler
    (app.anchoredPolicy execution players) horizon
      (ReactiveApplication.Execution.initial app state)).support at supported
  obtain ⟨state, initialized, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  rw [initial, PMF.support_map] at initialized
  obtain ⟨native, initialized, rfl⟩ := initialized
  rw [Vegas.initialLaw, serviceInitialLaw, PMF.support_map] at initialized
  obtain ⟨input, _, rfl⟩ := initialized
  exact runRounds_complete (fixture.eventInputs input) (app.anchoredPolicy execution players)
    execution reached

end Vegas.Examples.OddsEvensRecoveryService
