/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalAcceptedHistory
import Vegas.Game.PhaseProposalReplay
import Vegas.Pending.PhaseProposalNamespace
import Vegas.Pending.PhaseArchiveGeneration

/-! # Exact physical proposal coordinates in completed publication images -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open EventGraph Interaction SourceProgram GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- An opening for an event in the installed publication phase carries that
phase's full current attempt, not merely its static phase address. -/
theorem submitted_opening_installed_attempt
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (phase : RuntimePhase graph)
    (installed : current.execution.application.phases.head? = some phase)
    (coordinate : CommitAttemptEvent graph) (inside : coordinate.event ∈ phase.events)
    (message : Message Player (CommitAttemptPacket graph))
    (submitted : message ∈ current.execution.network.inputs) (raw : Raw L)
    (proposed : packetProposal? message.payload = some (coordinate, raw)) :
    coordinate.attempt = current.execution.application.attempt := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler trace
  obtain ⟨sourcePhase, sourceMember, event, named, sourceInside, sourceAddress⟩ :=
    PhaseCount.packetPhaseOrigins_history runtime leaks plan bounds inputs horizon scheduler trace
      message submitted
  obtain ⟨attempt, candidate, call⟩ := opening_of_packetProposal message.payload coordinate raw
    proposed
  have sameEvent : event = coordinate.event :=
    Option.some.inj (named.symm.trans (by rw [call]; rfl))
  subst event
  have suffix := phasePlanSuffix_history runtime leaks plan inputs horizon scheduler rawTrace
  have currentMember := suffix.subset (List.mem_of_mem_head? installed)
  have samePhase := RuntimePhasePlan.containing_unique plan.phases plan.adjacent coordinate.event
    sourcePhase phase sourceMember currentMember sourceInside inside
  have phaseEq : coordinate.attempt.phase = current.execution.application.attempt.phase := by
    rw [← attempt, sourceAddress, samePhase]
    simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some]
  exact submitted_publication_current_attempt runtime leaks bounds plan ordered inputs horizon
    scheduler current trace message submitted coordinate raw proposed phaseEq

/-- The live phase bucket has no stale generation or out-of-phase event.
Both facts follow from the actual counted emission, rather than its wire tag. -/
theorem archived_proposal_in_installed_phase
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (phase : RuntimePhase graph)
    (installed : current.execution.application.phases.head? = some phase)
    (proposal : ProposalRecoveryProposal L)
    (member : proposal ∈ sourceArchive current.execution.network.inputs)
    (samePhase : proposal.address.phase = current.execution.application.attempt.phase) :
    ∃ event : graph.EventId, event ∈ phase.events ∧
      proposal.address = sourceAddress ⟨current.execution.application.attempt, event⟩ := by
  obtain ⟨coordinate, archived, decoded⟩ := (mem_sourceArchive _ _).mp member
  obtain ⟨message, submitted, proposed⟩ := (mem_archive _ _).mp archived
  obtain ⟨attempt, _candidate, call⟩ := opening_of_packetProposal message.payload coordinate.1
    coordinate.2 proposed
  obtain ⟨sourcePhase, sourceMember, event, named, sourceInside, sourceAddress⟩ :=
    PhaseCount.packetPhaseOrigins_history runtime leaks plan bounds inputs horizon scheduler trace
      message submitted
  have sameEvent : event = coordinate.1.event :=
    Option.some.inj (named.symm.trans (by rw [call]; rfl))
  subst event
  have address := sourceProposal?_address coordinate proposal decoded
  have low : current.execution.application.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some]
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler trace
  have suffix := phasePlanSuffix_history runtime leaks plan inputs horizon scheduler rawTrace
  have phaseMember := suffix.subset (List.mem_of_mem_head? installed)
  have lowEq : sourcePhase.low = phase.low := by
    rw [← sourceAddress, attempt]
    exact (congrArg ProposalRecoveryAddress.phase address).symm.trans (samePhase.trans low)
  have same := plan.phase_eq_of_low_eq sourcePhase phase sourceMember phaseMember lowEq
  subst sourcePhase
  have sameAttempt := submitted_opening_installed_attempt runtime leaks bounds plan ordered inputs
    horizon scheduler current trace phase installed coordinate.1 sourceInside message submitted
    coordinate.2 proposed
  refine ⟨coordinate.1.event, sourceInside, ?_⟩
  simpa only [PhaseProposal.sourceAddress, sameAttempt] using address

/-- The native image used to replay a completed phase has the same submitted
packets as its actual counted anchor. True image completions therefore have
typed proposals at the anchor's literal full publication attempt. -/
theorem publication_image_disclosure_typed_archive
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (phase : RuntimePhase graph)
    (installed : current.execution.application.phases.head? = some phase)
    (image : EventGraphRuntime.State graph)
    (origins : OpeningOrigins current.execution.network.inputs image)
    (kept : KeepsStore current.execution.application.current.native image)
    (completion : graph.Completion) (inside : completion.event ∈ phase.events)
    (recorded : completion ∈ image.config.history)
    (payload : L.Ty) (outputEq : graph.outputLayout completion.event = .publication payload)
    (disclosed : cast (congrArg EventField.Action outputEq) completion.action = true) :
    ∃ value : L.Val payload,
      (⟨sourceAddress ⟨current.execution.application.attempt, completion.event⟩, payload, value⟩ :
        ProposalRecoveryProposal L) ∈ sourceArchive current.execution.network.inputs ∧
      nativeStoredProposal? image completion.event.val = some ⟨payload, value⟩ := by
  have actual : publicationDiscloses (graph.outputLayout completion.event) completion.action =
      true := (publicationDiscloses_cast outputEq completion.action).symm.trans disclosed
  obtain ⟨message, submitted, candidate, raw, call⟩ := origins completion recorded actual
  have proposed : packetProposal? message.payload =
      some (⟨message.payload.attempt, completion.event⟩, raw) := by
    simp only [packetProposal?, call]
  have sameAttempt := submitted_opening_installed_attempt runtime leaks bounds plan ordered inputs
    horizon scheduler current trace phase installed _ inside message submitted raw proposed
  change message.payload.attempt = current.execution.application.attempt at sameAttempt
  have archived : (⟨message.payload.attempt, completion.event⟩, raw) ∈
      archive current.execution.network.inputs := (mem_archive _ _).mpr
        ⟨message, submitted, proposed⟩
  obtain ⟨actualPayload, value, actualOutput, typed⟩ := archive_publication_typed runtime leaks
    bounds (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler current trace _ raw
      archived
  have samePayload := EventField.publication.inj (actualOutput.symm.trans outputEq)
  subst actualPayload
  have read := submitted_proposal_replay_value runtime leaks bounds plan ordered inputs horizon
    scheduler current trace message submitted _ raw proposed sameAttempt image kept
  refine ⟨value, (mem_sourceArchive _ _).mpr ⟨_, archived, ?_⟩, ?_⟩
  · rw [typed]
    simpa only [sameAttempt] using sourceProposal?_publication
      ⟨message.payload.attempt, completion.event⟩ payload outputEq value
  · rw [typed] at read
    exact read

end Vegas.EventGraphRuntime.PhaseProposal
