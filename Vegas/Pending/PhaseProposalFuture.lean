/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalAccepted
import Vegas.Pending.PhasePacketAddress
import Vegas.Pending.PhaseInputNamespace

/-! # No current signed opening can originate in an unentered future phase -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Counting ties the event to the packet's original static phase. Namespace
monotonicity then excludes packets for phases the actual execution never entered. -/
theorem submitted_opening_phase_le
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (phase : RuntimePhase graph) (member : phase ∈ plan.phases)
    (event : graph.EventId) (inside : event ∈ phase.events)
    (message : Message Player (CommitAttemptPacket graph))
    (submitted : message ∈ current.execution.network.inputs) (candidate : Handle graph)
    (raw : Raw L) (call : message.payload.packet.call = .opening event candidate raw) :
    phase.low ≤ current.execution.application.attempt.phase := by
  obtain ⟨sourcePhase, sourceMember, sourceEvent, named, sourceInside, sourceAddress⟩ :=
    PhaseCount.packetPhaseOrigins_history runtime leaks plan bounds inputs horizon scheduler trace
      message submitted
  have sameEvent : sourceEvent = event :=
    Option.some.inj (named.symm.trans (by rw [call]; rfl))
  subst sourceEvent
  have same := RuntimePhasePlan.containing_unique plan.phases plan.adjacent event
    sourcePhase phase sourceMember member sourceInside inside
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler trace
  have namespaces := inputNamespaces_history runtime leaks initial (by
    intro state supported
    obtain ⟨input, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan input) horizon scheduler rawTrace
  calc
    phase.low = sourcePhase.low := congrArg RuntimePhase.low same.symm
    _ = message.payload.attempt.phase := sourceAddress.symm
    _ ≤ current.execution.application.attempt.phase := (namespaces.bounded message submitted).2

/-- Even a normalization that drains multiple future phases cannot invent a
true opening stamp there: its origin would be a forbidden future submitted packet. -/
theorem future_publication_image_nondisclosing
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (phase : RuntimePhase graph) (member : phase ∈ plan.phases)
    (future : current.execution.application.attempt.phase < phase.low)
    (image : EventGraphRuntime.State graph)
    (origins : OpeningOrigins current.execution.network.inputs image)
    (completion : graph.Completion) (inside : completion.event ∈ phase.events)
    (recorded : completion ∈ image.config.history) :
    publicationDiscloses (graph.outputLayout completion.event) completion.action = false := by
  cases disclosed : publicationDiscloses (graph.outputLayout completion.event)
      completion.action with
  | false => rfl
  | true =>
      obtain ⟨message, submitted, candidate, raw, call⟩ := origins completion recorded disclosed
      have lower := submitted_opening_phase_le runtime leaks bounds plan inputs horizon scheduler
        current trace phase member completion.event inside message submitted candidate raw call
      omega

end Vegas.EventGraphRuntime.PhaseProposal
