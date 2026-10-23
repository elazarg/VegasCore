/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingResponseDispatcher
import Interaction.ReactiveOwnPlay
import GameTheoryExtensions.Analysis.Protocol.OwnPlayReach
import GameTheoryExtensions.Analysis.Protocol.SingleMoverReach
import Interaction.ReactiveEnvironmentMass

/-! # Observable unsent and canonical sending witnesses for repaired callbacks -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- A genuinely available nonsilent response excludes a previous own packet
for its current request, as an exact property of the complete signed word. -/
theorem unsent_of_nonsilent (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat) (owner : Player)
    (physical : (phaseApplication runtime leaks).Execution)
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, physical⟩))
    (coordinate : CommitAttemptEvent graph) (request : physical.application.SeedRequest owner
      coordinate) (material : WitnessedSubmission graph)
    (member : (⟨some material⟩ : (phaseApplication runtime leaks).Action) ∈
      onePacketActions runtime leaks bounds owner (physical.recall owner)
        (physical.observe (phaseApplication runtime leaks) owner)) :
    ∀ message ∈ (phaseApplication runtime leaks).outputs (physical.recall owner),
      event? message.payload ≠ some coordinate := by
  let app := phaseApplication runtime leaks
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have recalled := (app).history_inputRecall initial horizon scheduler
    ((onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler trace)
  intro message output same
  have own : message.sender = owner := by
    rw [← recalled owner] at output
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp output).2
  have fields : message.payload.attempt = coordinate.attempt ∧
      message.payload.packet.call.event? graph = some coordinate.event := by
    unfold event? at same
    obtain ⟨event, named, paired⟩ := Option.map_eq_some_iff.mp same
    cases paired
    exact ⟨rfl, named⟩
  have sent : PhaseSeedScheduler.ownPacket coordinate owner message = true := by
    simp only [PhaseSeedScheduler.ownPacket, decide_eq_true_eq]
    exact ⟨own, fields⟩
  have singleton := onePacketActions_eq_singleton_of_sent runtime leaks bounds plan ordered
    inputs horizon scheduler remaining owner physical trace coordinate request
      ⟨message, output, sent⟩
  rw [singleton] at member
  have impossible := congrArg ReactiveApplication.Action.transmission
    (Finset.mem_singleton.mp member)
  cases impossible

end Vegas.EventGraphRuntime.PhaseCount
