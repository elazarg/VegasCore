/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketChanceMass
import Vegas.EventGraph.OwnedStep

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
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)} {profile : BehavioralProfile setup.program}

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
  obtain ⟨next, _reached, mass⟩ := residual.step_mass event ready action after member
  rw [decodedPoint_eq next, pmf_map_apply_of_injective _ (Option.some_injective _), mass]
  obtain ⟨result, pure⟩ := before.step_eq_pure_of_actor event ready action actor acts
  rw [pure] at member ⊢
  rw [(PMF.mem_support_pure_iff _ _).mp member, PMF.pure_apply_self]

/-- The completion mass of a completion of an event with an actor is one. -/
theorem completionMass_of_actor (before after : EventGraphRuntime.State (graph setup))
    {event : (graph setup).EventId} (ready : before.config.cut.Ready event)
    {action : (graph setup).Action event}
    (member : after.config ∈ (before.config.step event ready action).support) {actor : Player}
    (acts : (graph setup).actor? event = some actor) :
    completionMass setup before after = 1 := by
  obtain ⟨value, _output, changed⟩ := before.config.step_completion event ready action _ member
  unfold completionMass
  rw [changed, List.drop_left]
  simp [EventGraph.Completion.fromDecision, acts]

variable [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- An active owner's actual completion matches in the intended replay, from a
replayed history at a configuration's source residual, when the other players'
factor of the recorded decision is the unsettled content before completion. -/
theorem replayStepMatches_actor (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (history : setup.intendedProtocol.History) (pending : ℝ)
    (before after : (application setup runtime leaks).Control) (idle : before.actor = none)
    (joint : Player → Option (application setup runtime leaks).Action) {rank : Nat}
    (residual : SourceResidual setup profile rank before.execution.application.config)
    (current : history.state =
      some (residual.lift (ProtocolState.entry residual.program residual.source)))
    (completion : (graph setup).Completion)
    (ready : before.execution.application.config.cut.Ready completion.event)
    {action : (graph setup).Action completion.event}
    (member : after.execution.application.config ∈
      (before.execution.application.config.step completion.event ready action).support)
    (dropped : after.execution.application.config.history.drop
      before.execution.application.config.history.length = [completion])
    {actor : Player} (acts : (graph setup).actor? completion.event = some actor)
    (active : actor ∉ before.execution.application.config.defaulted)
    (others : ∀ legal : setup.intendedProtocol.Legal history.state
        (actingJoint setup history.state
          (completion.decision.bind (decodeEventAction setup.program completion.event))),
      setup.intendedModel.opponentsStepProb assessment.strategy who history.trace
        ⟨_, legal⟩ = pending) :
    ReplayStepMatches setup runtime leaks assessment who history pending (some before) joint
      (some after) := by
  have mass := residual.actorStepMass completion.event ready action _ member acts
  obtain ⟨value, _output, changed⟩ :=
    before.execution.application.config.step_completion completion.event ready action _ member
  have recordEq : EventGraph.Completion.fromDecision completion.event
      (before.execution.application.config.actualDecision completion.event action) value =
        completion := by
    apply List.singleton_injective
    simpa only [changed, List.drop_left] using dropped
  have chosen : completion.decision = some action := by
    have packed := congrArg (fun record : (graph setup).Completion =>
      (⟨record.event, record.decision⟩ : Σ event, Option ((graph setup).Action event))) recordEq
    have decisionEq := eq_of_heq (Sigma.mk.inj packed).2
    change before.execution.application.config.actualDecision completion.event action =
      completion.decision at decisionEq
    exact decisionEq.symm.trans
      (before.execution.application.config.actualDecision_of_active completion.event actor
        acts active action)
  refine replayStepMatches_completion (runtime := runtime) assessment who history pending before
    after idle joint completion dropped fun legal => ?_
  simp only [acts, Option.isSome_some, ↓reduceIte]
  rw [completionMass_of_actor _ _ ready member acts]
  unfold counterfactualStepProb
  rw [others legal]
  change pending * (setup.protocolStep history.state (actingJoint setup history.state
    (completion.decision.bind (decodeEventAction setup.program completion.event))) _).toReal * 1 =
      1 * pending
  simp only [chosen, Option.bind_some]
  rw [current, protocolStep_actingJoint, mass, ENNReal.toReal_one]
  ring

end Vegas
