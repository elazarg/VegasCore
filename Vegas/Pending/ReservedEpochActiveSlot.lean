/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochSlots
import Interaction.ReactiveRecordedRounds

/-! # Every genuine active response follows the cycle's processing segment -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
theorem process_actor_none (view : (app).EnvironmentView) :
    (process runtime leaks view).actor? app = none := by
  unfold process
  split <;> rfl

omit [Fintype Player] in
theorem sample_actor_none (view : (app).EnvironmentView) :
    (sample runtime leaks view).actor? app = none := by
  unfold sample
  split
  · split_ifs <;> rfl
  · rfl

theorem command_activation_window {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (cursor : Nat) (view : (app).EnvironmentView) (owner : Player)
    (active : (command runtime leaks packetBudget tape cursor view).actor? app = some owner) :
    packetBudget ≤ cursor % cycleWidth (graph := graph) packetBudget ∧
      cursor % cycleWidth (graph := graph) packetBudget < packetBudget + Fintype.card Player := by
  dsimp only [command] at active
  split_ifs at active with processing marked ownerSlot offered sampleSlot eventSlot
  · rw [process_actor_none] at active
    cases active
  · cases active
  · exact ⟨by omega, by omega⟩
  · cases active
  · rw [sample_actor_none] at active
    cases active
  · cases active
  · cases active

theorem active_after_processing {length : Nat} (packetBudget : Nat) (tape : Tape Player length)
    (initial : PMF (app).State) (physicalHorizon : Nat) (current : (app).Control)
    (trace : ((app).protocol initial physicalHorizon
      (family runtime leaks packetBudget tape)).Trace (some current))
    (owner : Player) (active : current.actor = some owner) :
    packetBudget ≤ current.execution.environmentRecall.length %
      cycleWidth (graph := graph) packetBudget := by
  let choose := fun (tape : Tape Player length) (past : List (app).EnvironmentEntry)
    (view : (app).EnvironmentView) => command runtime leaks packetBudget tape past.length view
  have consistent := ((app).deterministic_transcript_invariant choose tape).history initial
    physicalHorizon (fun _ _ => trivial) trace
  change (app).commandConsistentFrom choose tape []
    current.execution.environmentRecall at consistent
  obtain ⟨past, view, selected, recalled, actor⟩ := (app).active_environment_entry initial
    physicalHorizon (family runtime leaks packetBudget tape) current trace owner active
  rw [recalled, (app).commandConsistent_snoc choose tape past ⟨view, selected⟩] at consistent
  have chosen : command runtime leaks packetBudget tape past.length view = selected := consistent.2
  rw [← chosen] at actor
  obtain ⟨lower, upper⟩ := command_activation_window runtime leaks packetBudget tape past.length
    view owner actor
  let width := cycleWidth (graph := graph) packetBudget
  change packetBudget ≤ past.length % width at lower
  change past.length % width < packetBudget + Fintype.card Player at upper
  have widthBound : packetBudget + Fintype.card Player + 1 < width := by
    dsimp [width, cycleWidth]
    omega
  have remainder : past.length % width + 1 < width := by omega
  have decomposition : current.execution.environmentRecall.length =
      (past.length / width) * width + (past.length % width + 1) := by
    rw [recalled, List.length_append, List.length_singleton]
    have divided := Nat.mod_add_div past.length width
    rw [Nat.mul_comm width] at divided
    omega
  rw [decomposition, cursor_mod packetBudget (past.length / width)
    (past.length % width + 1) remainder]
  omega

end Vegas.EventGraphRuntime.ReservedEpoch
