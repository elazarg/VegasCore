/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketChanceMass

/-! # Completions of events with an actor in the intended replay

A binding or a reveal is a deterministic source step, so at a configuration
with a source residual the source step of the decoded action of a completion
with an actor gives the decoded point of the reached configuration mass one
(`Vegas.SourceResidual.actorStepMass`). Such a completion has source factor
one. So it matches in the intended replay exactly when the other players'
factor of the replayed step, for the observer, is the unsettled content before
the completion (`Vegas.replayStepMatches_actor`): one when the observer moves,
and otherwise the mover's mass of the decoded action, which must be the content
factor taken when the mover's packet was sent.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {profile : BehavioralProfile setup.program}

/-- **A completion with an actor is a deterministic source step.** At a
configuration with a source residual, the source step of the decoded action of
a completion of an event with an actor gives the decoded point of the reached
configuration mass one. -/
theorem SourceResidual.actorStepMass {rank : Nat} {before : (graph setup).Config}
    (residual : SourceResidual setup profile rank before)
    (event : (graph setup).EventId) (ready : before.cut.Ready event)
    (action : (graph setup).Action event) (after : (graph setup).Config)
    (member : after ∈ (before.step event ready action).support) {actor : Player}
    (acts : (graph setup).actor? event = some actor) :
    ((ProtocolState.step setup.program
        (residual.lift (ProtocolState.entry residual.program residual.source))
        (fun _ => decodeEventAction setup.program event action)).map some)
      (decodedPoint setup after) = 1 := by
  obtain ⟨point, next, beforeEq, afterEq, reached⟩ :=
    decodedPoint_step residual event ready action after member
  rw [decodedPoint_eq residual, Option.some.injEq] at beforeEq
  rw [afterEq, beforeEq]
  suffices deterministic : ∃ result, ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event action) = PMF.pure result by
    obtain ⟨result, pure⟩ := deterministic
    rw [pure] at reached ⊢
    rw [(PMF.mem_support_pure_iff _ _).mp reached, PMF.pure_map, PMF.pure_apply_self]
  subst beforeEq
  obtain ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore, aligned,
    admitted, effective, supports, disclosing, lift, commutes, steps, injective, transport,
    checkpoint⟩ := residual
  have atEvent := (ready_iff_rank setup before rank checkpoint.ordered event).mp ready
  have counted := aligned.graphSuffix.countEq
  change rank + eventCount program = (graph setup).order.eventCount at counted
  cases program with
  | ret payoffs =>
      have := event.isLt
      simp only [eventCount] at counted
      omega
  | @sample Γ openNames name payload fresh distribution next =>
      exfalso
      let index : Fin (eventCount (.sample name fresh distribution next)) :=
        ⟨0, by simp [eventCount]⟩
      have atRank : (embedding.event index).val = rank := by
        simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
      have same : event = embedding.event index := Fin.ext (atEvent.trans atRank.symm)
      subst same
      have outputEq : (graph setup).outputLayout (embedding.event index) =
          .publicData payload := by
        change outputLayout setup.program (embedding.event index) = _
        simpa [index, outputLayout, eventCount] using embedding.layout_eq index
      have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes (embedding.event index)) =
            .sample payload (compilePublicDist refs distribution) := by
        change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
          ((toEventGraph setup.program).nodes (embedding.event index)) = _
        simpa [index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
      change EventGraph.EventCode.actor ((graph setup).nodes (embedding.event index)) =
        some actor at acts
      rw [← EventGraph.EventCode.actor_cast outputEq, codeEq] at acts
      cases acts
  | @commit Γ openNames name owner payload fresh guard next =>
      refine ⟨lift (Sum.inr (ProtocolState.entry next (commitSuccessor name guard source
        (OwnAction.binding owner name payload
          (decodeEventAction setup.program event action))))), ?_⟩
      change ProtocolState.step setup.program (lift (Sum.inl source)) _ = _
      rw [steps]
      change (PMF.pure _).map lift = _
      rw [PMF.pure_map]
  | @reveal Γ openNames published owner name payload fresh selected unresolved next =>
      refine ⟨lift (Sum.inr (ProtocolState.entry next (revealSuccessor published selected source
        (OwnAction.disclosure (decodeEventAction setup.program event action))))), ?_⟩
      change ProtocolState.step setup.program (lift (Sum.inl source)) _ = _
      rw [steps]
      change (PMF.pure _).map lift = _
      rw [PMF.pure_map]

/-- The completion mass of a completion of an event with an actor is one. -/
theorem completionMass_of_actor (before after : EventGraphRuntime.State (graph setup))
    {event : (graph setup).EventId} (ready : before.config.cut.Ready event)
    {action : (graph setup).Action event}
    (member : after.config ∈ (before.config.step event ready action).support) {actor : Player}
    (acts : (graph setup).actor? event = some actor) :
    completionMass setup before after = 1 := by
  have dropped : after.config.history.drop before.config.history.length = [⟨event, action⟩] := by
    rw [EventGraph.Config.step_history _ event ready action _ member, List.drop_left]
  unfold completionMass
  rw [dropped]
  simp only [acts]

variable [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- **A completion with an actor matches** in the intended replay, from a
replayed history at the decoded point of a configuration with a source
residual, when the other players' factor of the replayed step is the unsettled
content before the completion. -/
theorem replayStepMatches_actor (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (history : setup.intendedProtocol.History) (pending : ℝ)
    (before after : (application setup leaks).Control) (idle : before.actor = none)
    (joint : Player → Option (application setup leaks).Action) {rank : Nat}
    (residual : SourceResidual setup profile rank before.execution.application.config)
    (current : history.state =
      some (residual.lift (ProtocolState.entry residual.program residual.source)))
    {event : (graph setup).EventId} (ready : before.execution.application.config.cut.Ready event)
    {action : (graph setup).Action event}
    (member : after.execution.application.config ∈
      (before.execution.application.config.step event ready action).support)
    {actor : Player} (acts : (graph setup).actor? event = some actor)
    (others : ∀ legal : setup.intendedProtocol.Legal history.state
        (actingJoint setup history.state (decodeEventAction setup.program event action)),
      setup.intendedModel.opponentsStepProb assessment.strategy who history.trace
        ⟨_, legal⟩ = pending) :
    ReplayStepMatches setup leaks assessment who history pending (some before) joint
      (some after) := by
  have mass := residual.actorStepMass event ready action _ member acts
  refine replayStepMatches_completion assessment who history pending before after idle joint
    ready member fun legal => ?_
  simp only [acts, Option.isSome_some, ↓reduceIte]
  rw [completionMass_of_actor _ _ ready member acts]
  unfold counterfactualStepProb
  rw [others legal]
  change pending * (setup.protocolStep history.state (actingJoint setup history.state
    (decodeEventAction setup.program event action)) _).toReal * 1 = 1 * pending
  rw [current, protocolStep_actingJoint, mass, ENNReal.toReal_one]
  ring

end Vegas
