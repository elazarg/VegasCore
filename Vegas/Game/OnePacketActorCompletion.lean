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
    (before after : (application setup runtime leaks).Control) (idle : before.actor = none)
    (joint : Player → Option (application setup runtime leaks).Action) {rank : Nat}
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
    ReplayStepMatches setup runtime leaks assessment who history pending (some before) joint
      (some after) := by
  have mass := residual.actorStepMass event ready action _ member acts
  refine replayStepMatches_completion (runtime := runtime) assessment who history pending before
    after idle joint
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
