module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketPeriodInvariant
public import Vegas.Game.OnePacketCompletionContent
public import Vegas.Game.OnePacketReplayInputs
public import Vegas.Game.OnePacketDecodedActor
public import Vegas.Game.SourcePrefixPublications
public import Vegas.Game.SourceServiceFacts

@[expose] public section

/-! # Actor completions match along forced histories

For a native round recording one completion with an actor along a history
ending in a forced state of `who`, from a replayed intended history at the decoded point,
the replayed step moves exactly the actor, so the other players' factor is one
when the actor is `who` and the actor's mass of the decoded action otherwise
(`Vegas.opponentsStepProb_actingJoint`). A legal intended choice at the active owner is not failing,
so the actual completion records an accepted packet of the actor whose content is
the decoded choice (`Vegas.completion_content`). By the period invariant that
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
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- **Actor completions match along forced histories.** Along every native
history of the one-packet game ending in a forced state of `who`, every
completion of an event with an actor matches in the intended replay. -/
theorem actorCompletionsMatch_of_forced (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) :
    ∀ {state} (trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace
      state)
      (control : (application setup timeouts leaks).Control), state = some control →
      ForcedState setup timeouts leaks who (some control) →
      ActorCompletionsMatch setup timeouts leaks bounds horizon scheduler assessment who trace
  | _, .start, _, current, _ => by cases current
  | _, .extend (source := before) (target := after) prior joint legal realized, control,
      current, forced => by
      have recursive := fun next same forcedNext =>
        actorCompletionsMatch_of_forced assessment who prior next same
          forcedNext
      subst current
      change some control ∈ ((application setup timeouts leaks).transition (initialLaw setup)
        horizon
        scheduler before joint).support at realized
      refine ⟨?_, ?_⟩
      · cases before with
        | none =>
            obtain rfl := trace_eq_start_of_none (timeouts := timeouts) prior
            trivial
        | some current =>
            exact recursive current rfl (forcedState_of_transition (timeouts := timeouts) prior
              joint realized forced)
      · intro history replayed current next beforeEq afterEq idle completion ready completed actor
          acts intendedLegal
        subst beforeEq
        cases afterEq
        have forcedCurrent := forcedState_of_transition (timeouts := timeouts) prior joint realized
          forced
        have invariant := periodInvariant (timeouts := timeouts) assessment who prior current rfl
          forcedCurrent
        obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (timeouts := timeouts) (failureProfile
          setup.program)
          (bounds.onePacketMenu timeouts leaks) horizon scheduler prior current rfl
        have decoded := decodedPoint_eq residual
        have currentState : history.state =
            some (residual.lift (ProtocolState.entry residual.program residual.source)) :=
          (intendedHistory?_state (timeouts := timeouts) prior replayed).trans decoded
        have rawPrior := (bounds.onePacketMenu timeouts leaks).toRawTrace
          (initialLaw setup) horizon scheduler prior
        have facts := legalFacts setup leaks horizon scheduler current rawPrior
        have actorActive := current.execution.application.active_of_ready_owned
          facts.quiescent ready acts
        rw [opponentsStepProb_actingJoint assessment who history ready acts decoded currentState _
          intendedLegal, ite_eq_right actorActive]
        split_ifs with same
        · symm
          refine invariant.quiet fun other otherReady sender otherActs => ?_
          have sameEvent := setup.eventGraph.sequentialize_ready_unique _ otherReady ready
          subst sameEvent
          rw [acts] at otherActs
          cases otherActs
          exact same
        · have notFailing :=
            (defaulted_or_not_failing_of_legal ready acts decoded currentState
              intendedLegal).resolve_left actorActive
          rcases transition_idle_cases (timeouts := timeouts) (initialLaw setup) horizon scheduler
            current idle joint
              realized with sameExecution | ⟨command, moved⟩
          · have empty : control.execution.application.config.history.drop
                current.execution.application.config.history.length = [] := by
                rw [sameExecution, List.drop_length]
            rw [empty] at completed
            cases completed
          · have fresh : completion ∉ current.execution.application.config.history := by
              intro old
              apply ready.1
              exact (current.execution.application.config.history_exact completion.event).mp
                (List.mem_map.mpr ⟨completion, old, rfl⟩)
            have appended : completion ∈ control.execution.application.config.history :=
              List.mem_of_mem_drop (by rw [completed]; exact List.mem_singleton_self completion)
            obtain ⟨message, onLedger, sender, named, content, owned⟩ := completion_content
              (timeouts := timeouts) current.execution control.execution command moved completion
              fresh appended acts notFailing
            have rawTrace := (bounds.onePacketMenu timeouts leaks).toRawTrace
              (initialLaw setup) horizon scheduler (prior.extend joint legal realized)
            have facts := legalFacts setup leaks horizon scheduler control rawTrace
            have inputsEq := transition_idle_inputs (timeouts := timeouts) (initialLaw setup)
              horizon scheduler current
              idle joint realized
            have present : message ∈ current.execution.network.inputs := by
              rw [← inputsEq]
              obtain ⟨entry, entryPresent, material, _transmission, emitted, _packet⟩ :=
                facts.provenance.ledger message onLedger
              have recalled : message ∈ (application setup timeouts leaks).outputs
                  (control.execution.logs message.sender) :=
                List.mem_filterMap.mpr ⟨entry, entryPresent, emitted⟩
              rw [← facts.inputs message.sender] at recalled
              exact (List.mem_filter.mp recalled).1
            rcases invariant.settled completion.event ready actor acts same with ⟨_,
              nothing⟩ |
                ⟨recorded, recordedPresent, recordedSender, recordedNamed, sent, keep, fixed, eq⟩
            · exact (nothing message present sender named).elim
            · have sameMessage := invariant.unique recorded recordedPresent
                message present
                (recordedSender ▸ same) (recordedSender.trans sender.symm) completion.event
                recordedNamed named
              subst sameMessage
              rw [eq, content, callContent_keep keep _ fun named' handle call =>
                fixed named' handle call (owned named' handle call), decoded]

end Vegas
