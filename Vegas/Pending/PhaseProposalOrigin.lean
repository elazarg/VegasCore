/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalTyping
import Vegas.Pending.PhaseBindingIdleMenu
import Vegas.Pending.PhaseOpeningMenuShape
import Vegas.Pending.PhaseBindingFreshness
import Vegas.Pending.PhaseAttemptCheckpoint
import Vegas.Pending.PhaseFailureCoverage
import Interaction.ReactiveRecordedResponse

/-! # Genuine requesting callbacks for every submitted counted proposal

The packet's original callback is recovered from actual signed provenance and
literal own recall. It remains available after rejection, exclusion or phase
retirement. Neither a clean endpoint nor consistency with a prescribed strategy
is assumed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every submitted counted opening came from a genuine requesting callback in
its original physical attempt, even when the current state is already later. -/
theorem submitted_proposal_callback (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (current : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (message : Message Player (CommitAttemptPacket graph))
    (submitted : message ∈ current.execution.network.inputs)
    (coordinate : CommitAttemptEvent graph) (raw : Raw L)
    (proposed : packetProposal? message.payload = some (coordinate, raw)) :
    ∃ (before : (app).Control)
      (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
      (material : WitnessedSubmission graph) (candidate : Handle graph),
      TracePrefix prior trace ∧ before.actor = some message.sender ∧
      before.execution.application.SeedRequest message.sender coordinate ∧
      material.call.packet = .opening coordinate.event candidate raw ∧
      (⟨some material⟩ : (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds
        message.sender (before.execution.recall message.sender)
          (before.execution.observe (app) message.sender) ∧
      message.payload.attempt = before.execution.application.attempt := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have rawTrace := menu.toRawTrace initial horizon scheduler trace
  have origins : current.execution.Provenance (app) :=
    (app).history_provenance initial horizon scheduler rawTrace
  obtain ⟨entry, recorded, material, sent, emitted, state, known, packet⟩ :=
    origins.inputs message submitted
  have materialCall : message.payload.packet.call = material.call.packet := by
    rw [← packet]
    exact phase_emit_call state message.sender known material
  obtain ⟨attempt, candidate, call⟩ :=
    opening_of_packetProposal message.payload coordinate raw proposed
  have opening : material.call.packet = .opening coordinate.event candidate raw :=
    materialCall.symm.trans call
  obtain ⟨before, prior, retained, acting, viewed, offered, after, recalled⟩ :=
    menu.recorded_response_prefix initial horizon scheduler current trace message.sender
      entry recorded
  have action : entry.action = (⟨some material⟩ : (app).Action) := by
    cases named : entry.action with
    | mk transmission =>
        rw [named] at sent
        exact congrArg ReactiveApplication.Action.mk sent
  have offeredMaterial : (⟨some material⟩ : (app).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds message.sender
        (before.execution.recall message.sender)
        (before.execution.observe (app) message.sender) := by
    rwa [action] at offered
  rcases before with ⟨remaining, actor, physical⟩
  cases acting
  obtain ⟨actual, request⟩ := PhaseCount.onePacket_request_of_nonsilent runtime leaks bounds plan
    inputs horizon scheduler remaining message.sender physical prior material offeredMaterial
  have named := PhaseCount.onePacket_event_of_request runtime leaks bounds plan ordered inputs
    horizon scheduler remaining message.sender physical prior actual request material
      offeredMaterial
  have eventEq : actual.event = coordinate.event :=
    Option.some.inj (named.symm.trans (by rw [opening]; rfl))
  have stamp := phase_recalled_emission_attempt runtime leaks initial horizon scheduler rawTrace
    message.sender entry recorded message emitted
  rw [viewed] at stamp
  change message.payload.attempt = physical.application.attempt at stamp
  have attemptEq : actual.attempt = coordinate.attempt :=
    request.1.trans (stamp.symm.trans attempt)
  have same : actual = coordinate := by
    cases actual with
    | mk actualAttempt actualEvent =>
        cases coordinate with
        | mk expectedAttempt expectedEvent =>
            change actualAttempt = expectedAttempt at attemptEq
            change actualEvent = expectedEvent at eventEq
            cases attemptEq
            cases eventEq
            rfl
  exact ⟨⟨remaining, some message.sender, physical⟩, prior, material, candidate, retained, rfl,
    same ▸ request, opening, offeredMaterial, stamp⟩

omit [Fintype Player] in
/-- At a genuine request, every earlier event of the same owner is completed
without a surviving public failure. In particular a later same-owner reveal
cannot be submitted before an earlier reveal fails and excludes that owner. -/
theorem requested_earlier_own_completed_not_failed
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (current : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some current))
    (owner : Player) (coordinate : CommitAttemptEvent graph)
    (request : current.execution.application.SeedRequest owner coordinate)
    (earlier : graph.EventId) (earlierOwner : graph.actor? earlier = some owner)
    (rank : earlier.val < coordinate.event.val) :
    earlier ∈ current.execution.application.current.native.config.cut.completed ∧
      ¬ current.execution.application.current.native.PublicFailure earlier := by
  have actor := request.2.2.2.1
  have completed := (ordered.ready_visible_iff
    current.execution.application.current.native.config.cut request.2.2.1 actor
    (EventCode.output_visible_of_actor (graph.nodes earlier) owner earlierOwner)
    (IndependentReveals.not_of_actor_eq (by rw [earlierOwner, actor]))
    (IndependentReveals.not_of_actor_eq (by rw [earlierOwner, actor]))).mpr rank
  have covered := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler trace
  exact ⟨completed, fun failed => request.2.2.2.2 (covered.active.covered earlier owner
    earlierOwner failed)⟩

end Vegas.EventGraphRuntime.PhaseProposal
