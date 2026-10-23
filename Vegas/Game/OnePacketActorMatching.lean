/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketPeriodInvariant
import Vegas.Game.OnePacketDecodedActor

/-! # Actor completions match along forced histories

At a completion of an event with an actor along a native history ending in a
forced state of `who`, from a replayed intended history at the decoded point,
the replayed step moves exactly the actor, so the other players' factor is one
when the actor is `who` and the actor's mass of the decoded action otherwise
(`Vegas.opponentsStepProb_actingJoint`). A legal intended action is not failing,
so the event was completed by an accepted packet of the actor whose content is
the decoded action (`Vegas.completion_content`). By the period invariant that
packet is the one whose content the unsettled content records, and its content
has not changed since it was sent. Hence every actor completion matches
(`Vegas.actorCompletionsMatch_of_forced`), and the source weight of such a
history is the counterfactual reach of its intended replay times the unsettled
content.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

omit [Fintype Player] in
/-- **The replayed step moves the actor.** At a replayed intended history whose
state is the decoded point of a configuration with a ready event of `actor`,
the acting joint of a choice gives it to `actor` and nothing to the others. -/
theorem actingJoint_of_decoded {config : (graph setup).Config} {event : (graph setup).EventId}
    (ready : config.cut.Ready event) {actor : Player}
    (acts : (graph setup).actor? event = some actor) {point : ProtocolState setup.program}
    (decoded : decodedPoint setup config = some point) (choice : Option (OwnAction Player L))
    (player : Player) :
    actingJoint setup (some point) choice player = if actor = player then choice else none := by
  change (if ProtocolView.actor player setup.program
      (ProtocolState.observe player setup.program point) = some player then choice else none) = _
  rw [decodedPoint_actor player ready decoded, acts]
  by_cases same : actor = player <;> simp [same]

/-- **The other players' factor of a replayed actor step.** It is one when the
actor is `who`, and otherwise the actor's mass of the choice at its view of
the decoded point. -/
theorem opponentsStepProb_actingJoint (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (history : setup.intendedProtocol.History) {config : (graph setup).Config}
    {event : (graph setup).EventId} (ready : config.cut.Ready event) {actor : Player}
    (acts : (graph setup).actor? event = some actor) {point : ProtocolState setup.program}
    (decoded : decodedPoint setup config = some point) (current : history.state = some point)
    (choice : Option (OwnAction Player L))
    (legal : setup.intendedProtocol.Legal history.state (actingJoint setup history.state choice)) :
    setup.intendedModel.opponentsStepProb assessment.strategy who history.trace ⟨_, legal⟩ =
      if actor = who then 1 else
        (((assessment.strategy actor (setup.protocolObserve actor (some point))).map
          Subtype.val) choice).toReal := by
  have joint : ∀ player, actingJoint setup history.state choice player =
      if actor = player then choice else none := by
    intro player
    rw [current]
    exact actingJoint_of_decoded ready acts decoded choice player
  rw [setup.intendedModel.opponentsStepProb_eq_of_single assessment.strategy who history.trace
    ⟨_, legal⟩ actor fun player different => by
      change actingJoint setup history.state choice player = none
      rw [joint]
      simp [Ne.symm different]]
  split_ifs with same
  · rfl
  · have value : (setup.intendedModel.choicesOfLegal history.trace ⟨_, legal⟩ actor).1 =
        choice := by
      change actingJoint setup history.state choice actor = choice
      rw [joint]
      simp
    have mass := pmf_map_apply_of_injective
      (f := fun picked : setup.intendedModel.Choice actor
        (setup.intendedModel.infoOf actor history.trace) => picked.1)
      (assessment.strategy actor (setup.intendedModel.infoOf actor history.trace))
      Subtype.val_injective (setup.intendedModel.choicesOfLegal history.trace ⟨_, legal⟩ actor)
    rw [value] at mass
    rw [← mass]
    have info : setup.intendedModel.infoOf actor history.trace =
        setup.protocolObserve actor (some point) := by
      rw [setup.intended_info, current]
    rw [info]

omit [Fintype Player] in
/-- A legal intended acting joint at a replayed actor step gives the actor a
choice that is not failing. -/
theorem not_failing_of_legal {history : setup.intendedProtocol.History}
    {config : (graph setup).Config} {event : (graph setup).EventId}
    (ready : config.cut.Ready event) {actor : Player}
    (acts : (graph setup).actor? event = some actor) {point : ProtocolState setup.program}
    (decoded : decodedPoint setup config = some point) (current : history.state = some point)
    {choice : Option (OwnAction Player L)}
    (legal : setup.intendedProtocol.Legal history.state (actingJoint setup history.state choice)) :
    ¬ Failing choice := by
  have localLegal := setup.intendedProtocol.legalOption_of_legal legal actor
  have own : actingJoint setup history.state choice actor = choice := by
    rw [current, actingJoint_of_decoded ready acts decoded]
    simp
  rw [own] at localLegal
  cases choice with
  | none =>
      exfalso
      apply localLegal
      rw [current]
      change ProtocolView.actor actor setup.program
        (ProtocolState.observe actor setup.program point) = some actor
      rw [decodedPoint_actor actor ready decoded, acts]
  | some action =>
      obtain ⟨_, available⟩ := localLegal
      rw [current] at available
      exact ProtocolView.not_failing_of_intendedAvailable actor setup.program _ action available

/-- **Actor completions match along forced histories.** Along every native
history of the one-packet game ending in a forced state of `who`, every
completion of an event with an actor matches in the intended replay. -/
theorem actorCompletionsMatch_of_forced (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) :
    ∀ {state} (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
      (control : (application setup leaks).Control), state = some control →
      ForcedState setup leaks who (some control) →
      ActorCompletionsMatch setup leaks bounds horizon scheduler assessment who trace
  | _, .start, _, current, _ => by cases current
  | _, .extend (source := before) (target := after) prior joint legal realized, control,
      current, forced => by
      have recursive := fun next same forcedNext =>
        actorCompletionsMatch_of_forced assessment who prior next same forcedNext
      subst current
      change some control ∈ ((application setup leaks).transition (initialLaw setup) horizon
        scheduler before joint).support at realized
      refine ⟨?_, ?_⟩
      · cases before with
        | none =>
            obtain rfl := trace_eq_start_of_none prior
            trivial
        | some current =>
            exact recursive current rfl (forcedState_of_transition prior joint realized forced)
      · intro history replayed current next beforeEq afterEq idle event ready action member actor
          acts intendedLegal
        subst beforeEq
        cases afterEq
        have forcedCurrent := forcedState_of_transition prior joint realized forced
        have invariant := periodInvariant assessment who prior current rfl forcedCurrent
        obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
          (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler prior current rfl
        have decoded := decodedPoint_eq residual
        have currentState : history.state =
            some (residual.lift (ProtocolState.entry residual.program residual.source)) :=
          (intendedHistory?_state prior replayed).trans decoded
        rw [opponentsStepProb_actingJoint assessment who history ready acts decoded currentState _
          intendedLegal]
        split_ifs with same
        · symm
          refine invariant.quiet fun other otherReady sender otherActs => ?_
          have sameEvent := ready_unique (setup := setup) _ otherReady ready
          subst sameEvent
          rw [acts] at otherActs
          cases otherActs
          exact same
        · have notFailing := not_failing_of_legal ready acts decoded currentState intendedLegal
          rcases transition_idle_cases (initialLaw setup) horizon scheduler current idle joint
              realized with sameExecution | ⟨command, moved⟩
          · exact (config_ne_of_step member (by rw [sameExecution])).elim
          · obtain ⟨message, onLedger, sender, named, content, owned⟩ := completion_content
              current.execution _ command moved ready action member acts notFailing
            have rawTrace := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace
              (initialLaw setup) horizon scheduler (prior.extend joint legal realized)
            have facts := settledFacts_history (initialLaw setup) horizon scheduler rawTrace
            have inputsEq := transition_idle_inputs (initialLaw setup) horizon scheduler current
              idle joint realized
            have present : message ∈ current.execution.network.inputs := by
              rw [← inputsEq]
              exact facts.carried.ledger message onLedger
            rcases invariant.settled event ready actor acts same with ⟨_, nothing⟩ |
                ⟨recorded, recordedPresent, recordedSender, recordedNamed, sent, keep, fixed, eq⟩
            · exact (nothing message present sender named).elim
            · have sameMessage := invariant.unique recorded recordedPresent message present
                (recordedSender ▸ same) (recordedSender.trans sender.symm) event recordedNamed
                named
              subst sameMessage
              rw [eq, content, callContent_keep keep _ fun named' handle call =>
                fixed named' handle call (owned named' handle call), decoded]

end Vegas
