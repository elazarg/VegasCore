/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochCommandShape
import Interaction.ReactiveRoundBoundary
import Interaction.ReactiveStopping
import Interaction.ReactiveRecall
import Interaction.ReactiveOwnerSelection

/-! # Submitted envelopes remain pending before the next processing boundary -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem pending_until_processing_boundary {length : Nat} (packetBudget : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy)
    (sentCycle slot cycle count : Nat) (before after : (app).Execution)
    (cursor : before.environmentRecall.length =
      sentCycle * cycleWidth (graph := graph) packetBudget + slot)
    (afterProcessing : packetBudget ≤ slot)
    (quiet : ∀ later, sentCycle < later → later < cycle → tape.processes later = false)
    (room : before.environmentRecall.length + count ≤
      cycle * cycleWidth (graph := graph) packetBudget)
    (message : Message Player (app).Payload) (pending : message ∈ before.network.pending)
    (reached : after ∈ ((app).runRounds (family runtime leaks packetBudget tape) players count
      before).support) : message ∈ after.network.pending := by
  let scheduler := family runtime leaks packetBudget tape
  by_contra absent
  obtain ⟨used, tail, prior, middle, resumed, selected, lengthEq, prefixReached, priorPending,
      chosen, moved, lost, _response, _future⟩ :=
    (app).runRounds_environment_boundary scheduler players
      (fun execution => message ∈ execution.network.pending)
      (fun execution actor action member =>
        (app).respond_pending_mono execution actor action member)
      count before after pending reached absent
  have priorCursor := (app).runRounds_environmentRecall_length scheduler players used before
    prior prefixReached
  have later : sentCycle * cycleWidth (graph := graph) packetBudget + slot ≤
      prior.environmentRecall.length := by omega
  have earlier : prior.environmentRecall.length <
      cycle * cycleWidth (graph := graph) packetBudget := by omega
  have selectedEq := (family_support runtime leaks packetBudget tape prior.environmentRecall
    (prior.observeEnvironment app) selected).mp chosen
  have noInclude : ∀ identifier, selected ≠ .include identifier := by
    intro identifier same
    exact no_include_between_epochs runtime leaks packetBudget tape sentCycle slot cycle
      afterProcessing quiet prior.environmentRecall.length (prior.observeEnvironment app)
        later earlier identifier (selectedEq.symm.trans same)
  cases selected with
  | «include» identifier => exact noInclude identifier rfl
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff _ _] at moved
      cases moved
      exact lost priorPending
  | activate owner =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨sample, _supported, rfl⟩ := PMF.support_map .. ▸ supported
      exact lost priorPending
  | application native =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨state, _supported, rfl⟩ := PMF.support_map .. ▸ supported
      exact lost priorPending

end Vegas.EventGraphRuntime.ReservedEpoch
