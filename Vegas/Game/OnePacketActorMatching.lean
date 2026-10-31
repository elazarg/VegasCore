/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketPeriodInvariant
import Vegas.Game.OnePacketDecodedActor
import Vegas.Game.SourcePrefixPublications
import Vegas.Game.SourceServiceFacts

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
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- **Actor completions match along forced histories.** Along every native
history of the one-packet game ending in a forced state of `who`, every
completion of an event with an actor matches in the intended replay. -/
theorem actorCompletionsMatch_of_forced (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) :
    ∀ {state} (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state)
      (control : (application setup runtime leaks).Control), state = some control →
      ForcedState setup runtime leaks who (some control) →
      ActorCompletionsMatch setup runtime leaks bounds horizon scheduler assessment who trace
  | _, .start, _, current, _ => by cases current
  | _, .extend (source := before) (target := after) prior joint legal realized, control,
      current, forced => by
      have recursive := fun next same forcedNext =>
        actorCompletionsMatch_of_forced assessment who prior next same
          forcedNext
      subst current
      change some control ∈ ((application setup runtime leaks).transition (initialLaw setup) horizon
        scheduler before joint).support at realized
      refine ⟨?_, ?_⟩
      · cases before with
        | none =>
            obtain rfl := trace_eq_start_of_none (runtime := runtime) prior
            trivial
        | some current =>
            exact recursive current rfl (forcedState_of_transition (runtime := runtime) prior
              joint realized forced)
      · intro history replayed current next beforeEq afterEq idle event ready action member actor
          acts intendedLegal
        subst beforeEq
        cases afterEq
        have forcedCurrent := forcedState_of_transition (runtime := runtime) prior joint realized
          forced
        have invariant := periodInvariant (runtime := runtime) assessment who prior current rfl
          forcedCurrent
        obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (runtime := runtime) (failureProfile
          setup.program)
          (bounds.onePacketMenu runtime leaks) horizon scheduler prior current rfl
        have decoded := decodedPoint_eq residual
        have currentState : history.state =
            some (residual.lift (ProtocolState.entry residual.program residual.source)) :=
          (intendedHistory?_state (runtime := runtime) prior replayed).trans decoded
        have rawPrior := (bounds.onePacketMenu runtime leaks).toRawTrace
          (initialLaw setup) horizon scheduler prior
        have facts := legalFacts setup leaks horizon scheduler current rawPrior
        have actorActive := current.execution.application.active_of_ready_owned
          facts.quiescent ready acts
        rw [opponentsStepProb_actingJoint assessment who history ready acts decoded currentState _
          intendedLegal, ite_eq_right actorActive]
        split_ifs with same
        · symm
          refine invariant.quiet fun other otherReady sender otherActs => ?_
          have sameEvent := ready_unique (setup := setup) _ otherReady ready
          subst sameEvent
          rw [acts] at otherActs
          cases otherActs
          exact same
        · have notFailing :=
            (defaulted_or_not_failing_of_legal ready acts decoded currentState
              intendedLegal).resolve_left actorActive
          rcases transition_idle_cases (runtime := runtime) (initialLaw setup) horizon scheduler
            current idle joint
              realized with sameExecution | ⟨command, moved⟩
          · exact (config_ne_of_step member (by rw [sameExecution])).elim
          · obtain ⟨message, onLedger, sender, named, content, owned⟩ := completion_content
              (runtime := runtime)
              current.execution _ command moved ready action member acts notFailing
            have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace
              (initialLaw setup) horizon scheduler (prior.extend joint legal realized)
            have facts := settledFacts_history (initialLaw setup) horizon scheduler rawTrace
            have inputsEq := transition_idle_inputs (runtime := runtime) (initialLaw setup)
              horizon scheduler current
              idle joint realized
            have present : message ∈ current.execution.network.inputs := by
              rw [← inputsEq]
              exact facts.carried.ledger message onLedger
            rcases invariant.settled event ready actor acts same with ⟨_,
              nothing⟩ |
                ⟨recorded, recordedPresent, recordedSender, recordedNamed, sent, keep, fixed, eq⟩
            · exact (nothing message present sender named).elim
            · have sameMessage := invariant.unique recorded recordedPresent
                message present
                (recordedSender ▸ same) (recordedSender.trans sender.symm) event recordedNamed
                named
              subst sameMessage
              rw [eq, content, callContent_keep keep _ fun named' handle call =>
                fixed named' handle call (owned named' handle call), decoded]

end Vegas
