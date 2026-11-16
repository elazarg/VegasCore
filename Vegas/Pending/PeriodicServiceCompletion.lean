module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.PeriodicServiceClock
public import Interaction.ReactiveAnchoredTrace
public import Vegas.Pending.PeriodicServiceOpportunity
public import Vegas.Pending.PeriodicServiceReceipts

@[expose] public section

/-! # Completion and service certificates for small two-player graphs -/

noncomputable section

namespace Vegas.EventGraphRuntime.PeriodicService

open EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

variable {graph : EventGraph Player L} {roster : Bool ≃ Player}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {inputLaw : PMF graph.Inputs}

local notation "app" => (reactiveApplication (timeouts graph)) leaks
local notation "deadlines" => timeouts graph
local notation "startLaw" => initial graph leaks inputLaw
local notation "schedule" => scheduler graph roster leaks
local notation "selectedCommand" => command graph roster leaks

variable [Fact (graph.order.eventCount ≤ 4)]
  [Fact (∀ event : graph.EventId, (graph.actor? event).isSome = true)]

omit [DecidableEq Player] [Fact (graph.order.eventCount ≤ 4)] in
private theorem every_event_owned (event : graph.EventId) :
    (graph.actor? event).isSome = true :=
  (Fact.out : ∀ event : graph.EventId, (graph.actor? event).isSome = true) event

theorem window_completes_ready (inputs : graph.Inputs) (players : Player → (app).Policy)
    (cycle : Nat) (before after : (app).Execution) (aligned : ClockAligned inputs 0 before)
    (cursor : before.environmentRecall.length = cycle * width)
    (event : graph.EventId) (ready : before.application.config.cut.Ready event)
    (reached : after ∈ ((app).runRounds schedule players (8 * width) before).support) :
    event ∈ after.application.config.cut.completed := by
  have active := (aligned.valid.activated_iff event).mpr ⟨ready, every_event_owned event⟩
  obtain ⟨entered, activated⟩ := Option.isSome_iff_exists.mp active
  have beforeClock : before.application.clock = cycle := by
    rw [aligned.clock, cursor, Nat.zero_add]
    simpa only [Nat.add_zero] using (cursor_arithmetic cycle 0 (by decide)).1
  have enteredBound := aligned.valid.activated_le event entered activated
  rw [beforeClock] at enteredBound
  have eventBound : event.val < 4 := event.isLt.trans_le (Fact.out : graph.order.eventCount ≤ 4)
  let prefixRounds := 6 * width + (packetBudget + 2 + event.val)
  let tail := 8 * width - prefixRounds - 1
  have room : prefixRounds < 8 * width := by
    dsimp [prefixRounds, width, packetBudget, cycles]
    omega
  have splitCount : 8 * width = prefixRounds + (tail + 1) := by dsimp [tail]; omega
  rw [splitCount, (app).runRounds_add] at reached
  obtain ⟨middle, prefixReached, suffixReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have middleAligned := (clock_aligned_invariant (roster := roster) inputs 0).runRounds players
    prefixRounds
    before middle aligned prefixReached
  obtain ⟨_, prefixProgress⟩ := runRounds_progress inputs players
    prefixRounds before middle aligned.valid prefixReached
  have middleCursor : middle.environmentRecall.length =
      (cycle + 6) * width + (packetBudget + 2 + event.val) := by
    rw [(app).runRounds_environmentRecall_length schedule players prefixRounds before middle
      prefixReached, cursor]
    dsimp [prefixRounds]
    ring
  have middleClock : middle.application.clock = cycle + 6 := by
    rw [middleAligned.clock, Nat.zero_add, middleCursor]
    exact (cursor_arithmetic (cycle + 6) (packetBudget + 2 + event.val) (by
      change 64 + 2 + event.val < 71
      omega)).1
  have roundEq : (app).round schedule players middle =
      (app).dispatch players (.application (.expire event)) middle := by
    simp only [ReactiveApplication.round, scheduler, PMF.pure_bind]
    rw [middleCursor, expire_command _ _ eventBound]
  change after ∈ (((app).round schedule players middle).bind
    ((app).runRounds schedule players tail)).support at suffixReached
  rw [roundEq] at suffixReached
  obtain ⟨expired, moved, finalReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ suffixReached)
  have expiredReached : expired ∈
      (middle.environmentStep app (.application (.expire event))).support := by
    change expired ∈ ((middle.environmentStep app (.application (.expire event))).bind
      (fun execution => PMF.pure execution)).support at moved
    simpa only [PMF.bind_pure] using moved
  obtain ⟨_, suffixProgress⟩ := runRounds_progress inputs players
    tail expired after
      (reactive_environment_progress deadlines leaks inputs middle expired
        (.application (.expire event)) middleAligned.valid expiredReached).invariant
      finalReached
  by_cases done : event ∈ middle.application.config.cut.completed
  · have step := reactive_environment_progress deadlines leaks inputs middle expired
      (.application (.expire event)) middleAligned.valid expiredReached
    exact suffixProgress.completed (step.completed done)
  · have stillReady := (prefixProgress.ready_or_completed event ready).resolve_left done
    have stillActivated := prefixProgress.activated event entered activated done
    have due : (deadlines).duration event ≤ middle.application.clock - entered := by
      change 6 ≤ middle.application.clock - entered
      rw [middleClock]
      omega
    obtain ⟨updated, observed, rfl⟩ := PMF.support_map .. ▸ expiredReached
    obtain ⟨native, nativeMoved, rfl⟩ := PMF.support_map .. ▸ observed
    change native ∈ ((environmentStep deadlines middle.application (.expire event)).map
      State.drain).support at nativeMoved
    obtain ⟨raw, rawMoved, rfl⟩ := PMF.support_map .. ▸ nativeMoved
    have completed := environmentStep_expire_complete deadlines middle.application raw
      event stillReady (every_event_owned event) entered stillActivated due rawMoved
    exact suffixProgress.completed
      (raw.drainFuel_completed_subset raw.config.remaining completed)

theorem nonterminal_window_progress (inputs : graph.Inputs)
    (players : Player → (app).Policy) (cycle : Nat) (before after : (app).Execution)
    (aligned : ClockAligned inputs 0 before)
    (cursor : before.environmentRecall.length = cycle * width)
    (reached : after ∈ ((app).runRounds schedule players (8 * width) before).support)
    (unfinished : ¬ after.application.config.cut.Terminal) :
    before.application.config.cut.completed.card + 1 ≤
      after.application.config.cut.completed.card := by
  obtain ⟨_, progress⟩ := runRounds_progress inputs players
    (8 * width) before after aligned.valid reached
  have beforeUnfinished : ¬ before.application.config.cut.Terminal := by
    intro finished
    apply unfinished
    exact Finset.eq_univ_iff_forall.mpr fun event =>
      progress.completed (Finset.eq_univ_iff_forall.mp finished event)
  obtain ⟨event, ready⟩ := before.application.config.cut.exists_ready_of_not_terminal
    beforeUnfinished
  have completed := window_completes_ready inputs players cycle before after aligned cursor
    event ready reached
  have strict : before.application.config.cut.completed ⊂
      after.application.config.cut.completed := by
    exact Finset.ssubset_iff_subset_ne.mpr ⟨progress.completed, fun equal =>
      ready.1 (equal ▸ completed)⟩
  exact Nat.succ_le_of_lt (Finset.card_lt_card strict)

theorem windows_card_bound (inputs : graph.Inputs) (players : Player → (app).Policy)
    (blocks cycle : Nat) (before after : (app).Execution) (aligned : ClockAligned inputs 0 before)
    (cursor : before.environmentRecall.length = cycle * width)
    (reached : after ∈ ((app).runRounds schedule players (blocks * (8 * width)) before).support)
    (unfinished : ¬ after.application.config.cut.Terminal) :
    before.application.config.cut.completed.card + blocks ≤
      after.application.config.cut.completed.card := by
  induction blocks generalizing cycle before after with
  | zero =>
      simp only [ReactiveApplication.runRounds, PMF.mem_support_pure_iff _ _]
        at reached
      subst after
      omega
  | succ blocks ih =>
      have splitCount : (blocks + 1) * (8 * width) =
          8 * width + blocks * (8 * width) := by ring
      rw [splitCount, (app).runRounds_add] at reached
      obtain ⟨middle, firstReached, finalReached⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have middleAligned := (clock_aligned_invariant (roster := roster) inputs 0).runRounds
        players (8 * width)
        before middle aligned firstReached
      obtain ⟨_, later⟩ := runRounds_progress inputs players
        (blocks * (8 * width)) middle after middleAligned.valid finalReached
      have middleUnfinished : ¬ middle.application.config.cut.Terminal := by
        intro finished
        apply unfinished
        exact Finset.eq_univ_iff_forall.mpr fun event =>
          later.completed (Finset.eq_univ_iff_forall.mp finished event)
      have strict := nonterminal_window_progress inputs players cycle before middle aligned
        cursor firstReached middleUnfinished
      have middleCursor : middle.environmentRecall.length = (cycle + 8) * width := by
        rw [(app).runRounds_environmentRecall_length schedule players (8 * width) before middle
          firstReached, cursor]
        ring
      have bound := ih (cycle + 8) middle after middleAligned middleCursor finalReached unfinished
      omega

theorem runRounds_complete (inputs : graph.Inputs) (players : Player → (app).Policy)
    (final : (app).Execution)
    (reached : final ∈ ((app).runRounds schedule players horizon
      (ReactiveApplication.Execution.initial app (State.initial inputs))).support) :
    final.application.config.cut.Terminal := by
  by_contra unfinished
  have aligned : ClockAligned inputs 0
      (ReactiveApplication.Execution.initial app (State.initial inputs)) :=
    ⟨State.initial_invariant _, by
      simp [ReactiveApplication.Execution.initial, State.initial]⟩
  have bound := windows_card_bound inputs players 4 0 _ final aligned (by rfl) reached unfinished
  apply unfinished
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  have countBound : graph.order.eventCount ≤ 4 := Fact.out
  simpa only [Finset.card_univ, Fintype.card_fin] using
    countBound.trans (by simpa only [ReactiveApplication.Execution.initial, State.initial,
      EventGraph.Config.initial, EventOrder.Cut.empty, Finset.card_empty,
      Nat.zero_add] using bound)

theorem completesPlay : CompletesPlay deadlines leaks startLaw horizon schedule := by
  intro current trace terminal
  rcases current with ⟨remaining, actor, execution⟩
  obtain ⟨rfl, rfl⟩ := terminal
  let players : Player → (app).Policy := fun _ => (app).silentPolicy
  obtain ⟨_, supported⟩ := (app).mem_roundsFrom_anchoredPolicy_of_trace startLaw horizon schedule
    players trace
  change execution ∈ ((startLaw).bind fun state => (app).runRounds schedule
    ((app).anchoredPolicy execution players) horizon
      (ReactiveApplication.Execution.initial app state)).support at supported
  obtain ⟨state, initialized, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  rw [initial, PMF.support_map] at initialized
  obtain ⟨input, _, rfl⟩ := initialized
  exact runRounds_complete (input) ((app).anchoredPolicy execution players)
    execution reached


omit [Fact (graph.order.eventCount ≤ 4)]
  [Fact (∀ event : graph.EventId, (graph.actor? event).isSome = true)] in
/-- Every raw history receives an owner opportunity, protected inclusion and
completion within the fixed service horizon. -/
theorem contract (small : graph.order.eventCount ≤ 4)
    (owned : ∀ event : graph.EventId, (graph.actor? event).isSome = true) :
    AsyncContract deadlines leaks startLaw horizon schedule (fun _ => 3) (fun _ => 2) := by
  let : Fact (graph.order.eventCount ≤ 4) := ⟨small⟩
  let : Fact (∀ event : graph.EventId, (graph.actor? event).isSome = true) := ⟨owned⟩
  exact ⟨opportunity, protectedInclusion, completesPlay⟩

end Vegas.EventGraphRuntime.PeriodicService
