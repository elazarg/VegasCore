/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochTape
import Vegas.Pending.PhaseApplication
import Interaction.ReactiveSchedulerImplementation

/-! # Reserved epochs on the physical phase application

Each cycle reserves packet processing, owner activations, a source sample,
event expiry checks and a clock advance. The cursor counts actual environment
commands; neither pending-list length nor a player's response moves it.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

def cycleWidth (packetBudget : Nat) : Nat :=
  packetBudget + Fintype.card Player + graph.order.eventCount + 2

omit [DecidableEq Player] in
theorem cycleWidth_pos (packetBudget : Nat) :
    0 < cycleWidth (graph := graph) packetBudget := by
  unfold cycleWidth
  omega

/-- Deliver the first pending envelope, including stale or malformed packets. -/
def process (view : (app).EnvironmentView) : (app).Command :=
  match view.network.pending.head? with
  | none => .wait
  | some message => .include message.id

def sample (view : (app).EnvironmentView) : (app).Command :=
  match view.application.phase with
  | some (.sample, low, _) =>
      if bounded : low < graph.order.eventCount then
        .application (.executeSample ⟨low, bounded⟩)
      else .wait
  | _ => .wait

/-- One physical command at a fixed reserved slot. Activations are exogenous,
including offers at which the current owner has no logical task. -/
def command {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (cursor : Nat) (view : (app).EnvironmentView) : (app).Command :=
  let cycle := cursor / cycleWidth (graph := graph) packetBudget
  let slot := cursor % cycleWidth (graph := graph) packetBudget
  if slot < packetBudget then
    if tape.processes cycle then process runtime leaks view else .wait
  else if ownerSlot : slot - packetBudget < Fintype.card Player then
    let owner := tape.owner cycle ⟨slot - packetBudget, ownerSlot⟩
    if tape.activates cycle owner then .activate owner else .wait
  else if slot = packetBudget + Fintype.card Player then sample runtime leaks view
  else if eventSlot : slot - (packetBudget + Fintype.card Player + 1) <
      graph.order.eventCount then
    .application (.expire ⟨slot - (packetBudget + Fintype.card Player + 1), eventSlot⟩)
  else .application .advanceClock

def family {length : Nat} (packetBudget : Nat) (tape : Tape Player length) : (app).Scheduler :=
  fun past view => PMF.pure (command runtime leaks packetBudget tape past.length view)

/-- Sampling the whole tape permits arbitrary temporal and cross-owner correlation. -/
def implementation {length : Nat} (packetBudget : Nat) (prior : PMF (Tape Player length)) :
    (app).SchedulerImplementation (Tape Player length) :=
  (app).schedulerMixture prior (family runtime leaks packetBudget)

theorem family_support {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView) (selected : (app).Command) :
    selected ∈ (family runtime leaks packetBudget tape past view).support ↔
      selected = command runtime leaks packetBudget tape past.length view := by
  exact PMF.mem_support_pure_iff _ _

theorem processing_command {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (cursor : Nat) (view : (app).EnvironmentView)
    (slot : cursor % cycleWidth (graph := graph) packetBudget < packetBudget)
    (epoch : tape.processes (cursor / cycleWidth (graph := graph) packetBudget) = true) :
    command runtime leaks packetBudget tape cursor view = process runtime leaks view := by
  simp [command, slot, epoch]

omit [Fintype Player] in
theorem processing_empty (view : (app).EnvironmentView) (empty : view.network.pending = []) :
    process runtime leaks view = .wait := by
  simp [process, empty]

omit [Fintype Player] in
theorem processing_head (view : (app).EnvironmentView)
    (message : Message Player (CommitAttemptPacket graph))
    (rest : List (Message Player (CommitAttemptPacket graph)))
    (pending : view.network.pending = message :: rest) :
    process runtime leaks view = .include message.id := by
  simp [process, pending]

theorem realize {length : Nat} (packetBudget : Nat) (prior : PMF (Tape Player length))
    (players : Player → (app).Policy) (rounds : Nat) (state : (app).State) :
    (prior.bind fun tape =>
      (app).runRounds (family runtime leaks packetBudget tape) players rounds
        (ReactiveApplication.Execution.initial app state)) =
      (app).runRounds (implementation runtime leaks packetBudget prior).scheduler players rounds
        (ReactiveApplication.Execution.initial app state) :=
  (app).schedulerMixture_realize prior (family runtime leaks packetBudget) players rounds state

end Vegas.EventGraphRuntime.ReservedEpoch
