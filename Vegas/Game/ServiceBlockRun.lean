/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.BarrierBlocks
import Vegas.Game.SourceServiceAsyncStep
import Vegas.Game.SourceServiceReachedDecoding

/-! # Running the service through a block of events

On a barrier-ordered service graph the events between two public barriers form
a block. From a completion boundary at the block's start, every round keeps the
completed events between the block's start and end, and every recorded response
sees only block events ready (`Vegas.round_within`). A run stopped once the
whole block has completed therefore stops at the completion boundary of the
block's end (`Vegas.blockRun_boundary`), and under complete play it does stop
there before the horizon (`Vegas.blockRun_completes`). A public event is a
block of one event, and on the sequential graph so is every event.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- Every event below `high` has completed. -/
def BlockDone (high : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution) :
    Prop :=
  ∀ event : (serviceGraph setup mode).EventId, event.val < high →
    event ∈ execution.application.config.cut.completed

instance (high : Nat) : DecidablePred
    (BlockDone (setup := setup) (deadline := deadline) (leaks := leaks) high) := fun _ => by
  unfold BlockDone
  infer_instance

/-- The end of a block: a public event, or the end of the graph. -/
def BlockEnd (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
    (high : Nat) : Prop :=
  high ≤ (serviceGraph setup mode).order.eventCount ∧
    ∀ event : (serviceGraph setup mode).EventId, event.val = high →
      ((serviceGraph setup mode).outputLayout event).IsPublic

/-- The run state inside a block: the completed events lie between the block's
start and end, and no recorded response has seen an event at or beyond the
end ready. -/
structure WithinBlock (low high : Nat)
    (execution : (serviceApplication setup mode deadline leaks).Execution) : Prop where
  within : execution.application.config.cut.Within low high
  untouched : ∀ event : (serviceGraph setup mode).EventId, high ≤ event.val →
    Untouched setup leaks event execution

/-- A block is sealed when, at every cut inside it that has not finished it,
every ready event lies in it. -/
def BlockSealed (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
    (low high : Nat) : Prop :=
  ∀ cut : (serviceGraph setup mode).order.Cut, cut.Within low high →
    ¬ (∀ event : (serviceGraph setup mode).EventId, event.val < high → event ∈ cut.completed) →
    ∀ event, cut.Ready event → event.val < high

/-- On a barrier-ordered graph a block ending at a public event or at the end
of the graph is sealed. -/
theorem BlockEnd.sealed (ordered : (serviceGraph setup mode).BarrierOrdered) {low high : Nat}
    (wall : BlockEnd setup mode high) : BlockSealed setup mode low high := by
  intro cut within running event ready
  rcases ordered.ready_lt_of_within within wall.2 ready with below | done
  · exact below
  · exact (running done).elim

/-- An event ready alone at its prefix is a sealed block of its own. -/
theorem sealed_of_alone {event : (serviceGraph setup mode).EventId}
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event) :
    BlockSealed setup mode event.val (event.val + 1) := by
  intro cut within running other ready
  have pending : event ∉ cut.completed := by
    intro done
    apply running
    intro below lower
    rcases Nat.lt_succ_iff_lt_or_eq.mp lower with less | equal
    · exact within.1 below less
    · rw [show below = event from Fin.ext equal]
      exact done
  have prefixed : cut.IsPrefix event.val := by
    refine ⟨Nat.le_of_lt event.isLt, fun earlier => ⟨fun done => ?_, within.1 earlier⟩⟩
    have bounded := within.2 earlier done
    rcases Nat.lt_succ_iff_lt_or_eq.mp bounded with less | equal
    · exact less
    · have same : earlier = event := Fin.ext equal
      subst same
      exact (pending done).elim
  have eventReady : cut.Ready event := by
    have := prefixed.ready event.isLt
    exact this
  rw [alone cut other eventReady ready]
  exact Nat.lt_succ_self _

/-- **One round inside a block.** A round from a state inside an unfinished
sealed block stays inside the block. -/
theorem round_within {low high : Nat} (sealed : BlockSealed setup mode low high)
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy)
    (execution next : (serviceApplication setup mode deadline leaks).Execution)
    (inside : WithinBlock low high execution) (running : ¬ BlockDone high execution)
    (reached : next ∈ ((serviceApplication setup mode deadline leaks).round scheduler players
      execution).support) :
    WithinBlock low high next := by
  let app := serviceApplication setup mode deadline leaks
  have readyBelow (event : (serviceGraph setup mode).EventId)
      (ready : execution.application.config.cut.Ready event) : event.val < high :=
    sealed _ inside.within running event ready
  obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have recallEq := app.environmentStep_recall execution middle command moved
  have middleWithin : middle.application.config.cut.Within low high := by
    rcases environmentStep_configStep setup leaks execution middle command moved with
      same | ⟨event, ready, action, member⟩
    · rw [same]
      exact inside.within
    · rw [execution.application.config.step_cut event ready action _ member]
      exact inside.within.complete event ready (readyBelow event ready)
  change next ∈ (app.resume players (command.actor? app) middle).support at resumed
  by_cases activation : ∃ who, command = .activate who
  · obtain ⟨who, rfl⟩ := activation
    have sameApp := activation_application setup leaks execution middle who moved
    change next ∈ (app.invoke players who middle).support at resumed
    rw [ReactiveApplication.invoke, PMF.support_map] at resumed
    obtain ⟨response, _, rfl⟩ := resumed
    obtain ⟨configEq, _⟩ := (serviceRuntime setup mode deadline).reactive_respond_application leaks
      middle who response
    refine ⟨by rw [configEq, sameApp]; exact inside.within, ?_⟩
    intro event later observer entry member readyView
    rcases app.respond_entry_origin middle who observer response entry member with
      prior | ⟨_, fresh⟩
    · rw [recallEq] at prior
      exact inside.untouched event later observer entry prior readyView
    · rw [fresh] at readyView
      change middle.application.publicView.EventReady event at readyView
      have readyNow := (State.publicView_eventReady _ event).mp readyView
      rw [sameApp] at readyNow
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (readyBelow event readyNow) later)
  · have idle : command.actor? app = none := by
      cases command with
      | activate who => exact (activation ⟨who, rfl⟩).elim
      | «include» _ => rfl
      | application _ => rfl
      | wait => rfl
    rw [idle] at resumed
    simp only [ReactiveApplication.resume, PMF.mem_support_pure_iff] at resumed
    subst resumed
    refine ⟨middleWithin, fun event later observer entry member => ?_⟩
    rw [recallEq] at member
    exact inside.untouched event later observer entry member

/-- Rounds stopped once the block is done stay inside the block. -/
theorem runUntil_within {low high : Nat} (sealed : BlockSealed setup mode low high)
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) :
    ∀ (count : Nat) (execution stopped : (serviceApplication setup mode deadline leaks).Execution),
      WithinBlock low high execution →
      stopped ∈ ((serviceApplication setup mode deadline leaks).runUntil scheduler players
        (BlockDone high) count execution).support →
      WithinBlock low high stopped := by
  intro count
  induction count with
  | zero =>
      intro execution stopped inside reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact inside
  | succ count ih =>
      intro execution stopped inside reached
      by_cases halt : BlockDone high execution
      · rw [ReactiveApplication.runUntil_of_stop _ _ _ _ _ execution halt] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact inside
      · simp only [ReactiveApplication.runUntil, halt, ↓reduceIte] at reached
        obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
        exact ih middle stopped (round_within sealed scheduler players execution middle
          inside halt moved) rest

/-- A completion boundary at a block's start is inside the block. -/
theorem CompletionBoundary.withinBlock
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    {low high : Nat} {execution : (serviceApplication setup mode deadline leaks).Execution}
    (boundary : CompletionBoundary setup leaks scheduler players low execution)
    (later : low ≤ high) : WithinBlock low high execution :=
  ⟨boundary.ordered.within later, fun event above =>
    boundary.untouched event (Nat.le_trans later above)⟩

/-- **The block's end is a completion boundary.** A run stopped once a block
is done, from a completion boundary at its start, stops within the horizon at
a completion boundary of the block's end, if it stops with the block done. -/
theorem blockRun_boundary {low high : Nat} (later : low ≤ high)
    (sealed : BlockSealed setup mode low high)
    (bounded' : high ≤ (serviceGraph setup mode).order.eventCount)
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy} {horizon : Nat}
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players low execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (stopped : (serviceApplication setup mode deadline leaks).Execution)
    (reached : stopped ∈ ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
      players (BlockDone high) horizon execution).support)
    (finished : BlockDone high stopped) :
    stopped.environmentRecall.length ≤ horizon ∧
      CompletionBoundary setup leaks scheduler players high stopped := by
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨used, within, _, length⟩ := app.runUntil_runRounds scheduler players _ _ execution
    stopped reached
  have inside := runUntil_within sealed scheduler players _ execution stopped
    (boundary.withinBlock later) reached
  exact ⟨by omega, app.roundsFrom_runUntil scheduler players (serviceInitialLaw setup mode) _ _
    execution stopped boundary.supported reached,
    inside.within.isPrefix bounded' finished, inside.untouched⟩

/-- **Complete play finishes the block.** Under a scheduler that completes play
by the horizon, a run stopped once a block is done, from a completion boundary
within the horizon, stops with the block done. -/
theorem blockRun_completes {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {horizon : Nat} {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    (complete : CompletesPlay (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler)
    {low : Nat} (high : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players low execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (stopped : (serviceApplication setup mode deadline leaks).Execution)
    (reached : stopped ∈ ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
      players (BlockDone high) horizon execution).support) :
    BlockDone high stopped := by
  let app := serviceApplication setup mode deadline leaks
  rcases app.runUntilHorizon_stopped scheduler players _ horizon
      (horizon - execution.environmentRecall.length) execution stopped (by omega) reached with
    done | spent
  · exact done
  · have supported := app.roundsFrom_runUntil scheduler players (serviceInitialLaw setup mode) _ _
      execution stopped boundary.supported reached
    obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler
      players _ (by omega) stopped supported
    have terminal := complete _ trace (by
      change horizon - stopped.environmentRecall.length = 0 ∧ _
      exact ⟨by omega, rfl⟩)
    change stopped.application.config.cut.completed = Finset.univ at terminal
    intro event _
    rw [terminal]
    exact Finset.mem_univ _

/-- **Complete play finishes the block, for any players.** Under a scheduler
that completes play, a run stopped once a block is done, from a legal raw
history with as many rounds left as the run has, stops with the block done. -/
theorem runUntil_blockDone_of_trace
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {horizon : Nat} (players : Player → (serviceApplication setup mode deadline leaks).Policy)
    (complete : CompletesPlay (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler) (high : Nat) :
    ∀ (count : Nat) (execution stopped : (serviceApplication setup mode deadline leaks).Execution),
      ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨count, none, execution⟩) →
      stopped ∈ ((serviceApplication setup mode deadline leaks).runUntil scheduler players
        (BlockDone high) count execution).support →
      BlockDone high stopped := by
  let app := serviceApplication setup mode deadline leaks
  intro count
  induction count with
  | zero =>
      intro execution stopped trace reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      have terminal := complete _ trace (by
        change 0 = 0 ∧ _
        exact ⟨rfl, rfl⟩)
      change execution.application.config.cut.completed = Finset.univ at terminal
      intro event _
      rw [terminal]
      exact Finset.mem_univ _
  | succ count ih =>
      intro execution stopped trace reached
      by_cases halt : BlockDone high execution
      · rw [ReactiveApplication.runUntil_of_stop _ _ _ _ _ execution halt] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact halt
      · simp only [ReactiveApplication.runUntil, halt, ↓reduceIte] at reached
        obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
        obtain ⟨middleTrace⟩ := app.raw_trace_round (serviceInitialLaw setup mode) horizon
          scheduler players count execution middle (by simpa only [Nat.zero_add] using trace) moved
        exact ih middle stopped (by simpa only [Nat.zero_add] using middleTrace) rest

end Vegas
