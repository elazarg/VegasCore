/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketReplaySteps
import Vegas.Game.OnePacketEnvironmentSteps

/-! # Chance completions and the source chance law

A chance event of the compiled graph draws from the exact source chance law,
and both the graph's completion and the source successor record the drawn
value. So at a configuration with a source residual, completing a chance event
reaches each configuration with the probability the source step gives its
decoded point, and the decoded action of a chance completion is nothing
(`Vegas.SourceResidual.chanceMass`). Hence the completion of a chance event
matches in the intended replay (`Vegas.replayStepMatches_chance`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)} {profile : BehavioralProfile setup.program}

/-- **A chance completion has the source chance mass.** At a configuration with
a source residual, completing a chance event decodes to no action, and reaches
a configuration with the probability that the source step from the residual's
point gives its decoded point. -/
theorem SourceResidual.chanceMass {rank : Nat} {before : (graph setup).Config}
    (residual : SourceResidual setup profile rank before)
    (event : (graph setup).EventId) (ready : before.cut.Ready event)
    (action : (graph setup).Action event) (after : (graph setup).Config)
    (member : after ∈ (before.step event ready action).support)
    (chance : (graph setup).actor? event = none) :
    decodeEventAction setup.program event action = none ∧
      (((ProtocolState.step setup.program
          (residual.lift (ProtocolState.entry residual.program residual.source))
          (fun _ => none)).map some) (decodedPoint setup after)).toReal =
        ((before.step event ready action) after).toReal := by
  have decoded : decodeEventAction setup.program event action = none := by
    have owner := decodeEventAction_owner setup.program event action
    rw [eventOwner?_eq_actor] at owner
    change (decodeEventAction setup.program event action).map sourceActionOwner =
      (graph setup).actor? event at owner
    rw [chance] at owner
    exact Option.map_eq_none_iff.mp owner
  obtain ⟨next, _reached, mass⟩ := residual.step_mass event ready action after member
  refine ⟨decoded, ?_⟩
  rw [decodedPoint_eq next, pmf_map_apply_of_injective _ (Option.some_injective _), ← decoded]
  exact congrArg ENNReal.toReal mass


variable [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- **A chance completion matches** in the intended replay, from a replayed
history at the decoded point of a configuration with a source residual. -/
theorem replayStepMatches_chance (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (history : setup.intendedProtocol.History) (pending : ℝ)
    (before after : (application setup timeouts leaks).Control) (idle : before.actor = none)
    (joint : Player → Option (application setup timeouts leaks).Action) {rank : Nat}
    (residual : SourceResidual setup profile rank before.execution.application.config)
    (current : history.state =
      some (residual.lift (ProtocolState.entry residual.program residual.source)))
    {event : (graph setup).EventId} (ready : before.execution.application.config.cut.Ready event)
    {action : (graph setup).Action event}
    (member : after.execution.application.config ∈
      (before.execution.application.config.step event ready action).support)
    (chance : (graph setup).actor? event = none) :
    ReplayStepMatches setup timeouts leaks assessment who history pending (some before) joint
      (some after) := by
  obtain ⟨decoded, mass⟩ := residual.chanceMass event ready action _ member chance
  obtain ⟨value, _output, changed⟩ :=
    before.execution.application.config.step_completion event ready action _ member
  let completion : (graph setup).Completion := ⟨event, none, none⟩
  have dropped : after.execution.application.config.history.drop
      before.execution.application.config.history.length = [completion] := by
    rw [changed, List.drop_left]
    have ownerless : ((graph setup).nodes event).actor = none := chance
    simp only [EventGraph.completion, EventGraph.Config.actualDecision,
      EventGraph.EventCode.actualDecision, ownerless]
    rfl
  refine replayStepMatches_completion (timeouts := timeouts) assessment who history pending before
    after idle joint completion dropped fun legal => ?_
  dsimp only [completion, Option.bind_none] at legal ⊢
  have nobody : ∀ player, (⟨actingJoint setup history.state none, legal⟩ :
      { action : ∀ i, Option (setup.intendedProtocol.Action i) //
        setup.intendedProtocol.Legal history.state action }).1 player = none := by
    intro player
    change actingJoint setup history.state none player = none
    rw [current]
    simp [actingJoint]
  have opponents := setup.intendedModel.opponentsStepProb_eq_one_of_none assessment.strategy
    who history.trace _ nobody
  change _ * (if ((graph setup).actor? event).isSome then 1 else pending) = _
  simp only [chance, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rw [completionMass_of_chance _ _ ready member chance]
  unfold counterfactualStepProb
  rw [opponents, one_mul]
  congr 1
  change (setup.protocolStep history.state (actingJoint setup history.state none) _).toReal = _
  rw [current, protocolStep_actingJoint]
  exact mass

end Vegas
