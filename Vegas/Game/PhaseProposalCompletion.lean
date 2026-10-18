/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalAcceptedHistory
import Vegas.Pending.PhaseProposalTyping
import Vegas.Game.PhaseProposalSourceArchive

/-! # Completed disclosures occur in the actual submitted proposal archive -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open EventGraph Interaction SourceProgram GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Recorded true publication actions have submitted packets even if their
guard verdict excluded the sender. The original physical address is retained. -/
theorem recorded_disclosure_submitted
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some current))
    (completion : graph.Completion)
    (recorded : completion ∈ current.execution.application.current.native.config.history)
    (payload : L.Ty) (outputEq : graph.outputLayout completion.event = .publication payload)
    (disclosed : cast (congrArg EventField.Action outputEq) completion.action = true) :
    ∃ message ∈ current.execution.network.inputs, ∃ raw : Raw L,
      packetProposal? message.payload =
        some (⟨message.payload.attempt, completion.event⟩, raw) := by
  have origins := (openingOrigins_history runtime leaks plan inputs horizon scheduler current
    trace).1
  have actual : publicationDiscloses (graph.outputLayout completion.event) completion.action =
      true := (publicationDiscloses_cast outputEq completion.action).symm.trans disclosed
  obtain ⟨message, present, candidate, raw, call⟩ := origins completion recorded actual
  exact ⟨message, present, raw, by simp only [packetProposal?, call]⟩

/-- Type decoding retains each actual counted disclosure in the canonical
source archive, including truthful openings with failed guards. -/
theorem recorded_disclosure_typed_archive [Fintype Player]
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (current : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (completion : graph.Completion)
    (recorded : completion ∈ current.execution.application.current.native.config.history)
    (payload : L.Ty) (outputEq : graph.outputLayout completion.event = .publication payload)
    (disclosed : cast (congrArg EventField.Action outputEq) completion.action = true) :
    ∃ (message : Message Player (CommitAttemptPacket graph)) (value : L.Val payload),
      message ∈ current.execution.network.inputs ∧
      (⟨sourceAddress ⟨message.payload.attempt, completion.event⟩, payload, value⟩ :
        ProposalRecoveryProposal L) ∈ sourceArchive current.execution.network.inputs := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler trace
  obtain ⟨message, present, raw, proposed⟩ := recorded_disclosure_submitted runtime leaks plan
    inputs horizon scheduler current rawTrace completion recorded payload outputEq disclosed
  have archived : (⟨message.payload.attempt, completion.event⟩, raw) ∈
      archive current.execution.network.inputs := (mem_archive _ _).mpr ⟨message, present, proposed⟩
  obtain ⟨actualPayload, value, actualOutput, typed⟩ := archive_publication_typed runtime leaks
    bounds initial horizon scheduler current trace _ raw archived
  have samePayload := EventField.publication.inj (actualOutput.symm.trans outputEq)
  subst actualPayload
  refine ⟨message, value, present, (mem_sourceArchive _ _).mpr ⟨_, archived, ?_⟩⟩
  rw [typed]
  exact sourceProposal?_publication _ payload outputEq value

end Vegas.EventGraphRuntime.PhaseProposal
