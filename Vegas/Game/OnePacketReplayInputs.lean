/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketActorCompletion

/-! # Source weights of forced beliefs from the intended replay

**Matching along a history.** The initial draw, every response, every round
completing no event, and every chance completion match in the intended replay
whatever the profiles. So every step of a native history matches as soon as
every completion of an event with an actor does, which asks that the other
players' factor of the replayed step be the unsettled content before it
(`Vegas.ActorCompletionsMatch`, `Vegas.replayMatches_of_actorCompletions`).

**The replay projection.** At a decision site of `who` with an intended site at
its projected view, a native history projects to its intended replay when that
exists, and to a fixed history of the intended site otherwise
(`Vegas.replayProjection`).

**Source weights.** Intended reach is the observer's own reach times its
counterfactual reach, and the intended model has decision recall, so the own
reach is common to the intended site and positive under fully mixed play.
Hence at every native history whose replay exists, along which every actor
completion matches, and whose unsettled content is one, the source weight times
that common own reach is the intended reach of the replay projection
(`Vegas.othersSourceWeight_mul_ownReach`). These are the source weights of
`Vegas.ForcedBeliefInputs`, which can be assembled from the replay projection
(`Vegas.ForcedBeliefInputs.ofReplay`).
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The intended model has decision recall. -/
theorem intendedModel_decisionRecall (setup : Setup (Player := Player) (L := L)) :
    setup.intendedModel.DecisionRecall :=
  setup.intendedModel.decisionRecall_of_perfectRecall
    ((setup.informationModel _).restrictMenu_perfectRecall _ _
      (setup.protocol_perfectRecall _))

end Vegas.SourceProgram.Setup

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- **Matching actor completions.** At every completion of an event with an
actor along a native history, from the replay of its prefix, the other
players' factor of the replayed step for `who` is the unsettled content of the
prefix. -/
def ActorCompletionsMatch (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) :
    ∀ {state}, (onePacketProtocol setup leaks bounds horizon scheduler).Trace state → Prop
  | _, .start => True
  | _, .extend (source := before) (target := after) prior _ _ _ =>
      ActorCompletionsMatch assessment who prior ∧
        ∀ history, intendedHistory? setup leaks bounds horizon scheduler prior = some history →
          ∀ (current next : (application setup leaks).Control), before = some current →
            after = some next → current.actor = none →
            ∀ (event : (graph setup).EventId)
              (ready : current.execution.application.config.cut.Ready event)
              (action : (graph setup).Action event),
              next.execution.application.config ∈
                (current.execution.application.config.step event ready action).support →
              ∀ actor, (graph setup).actor? event = some actor →
              ∀ legal : setup.intendedProtocol.Legal history.state
                  (actingJoint setup history.state (decodeEventAction setup.program event action)),
                setup.intendedModel.opponentsStepProb assessment.strategy who history.trace
                  ⟨_, legal⟩ =
                unsettledContent setup leaks bounds horizon scheduler assessment who prior

variable {setup leaks bounds horizon scheduler}

/-- A history of the one-packet game never returns to the state before
initialization. -/
theorem trace_eq_start_of_none :
    ∀ (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace none),
      trace = .start
  | .start => rfl
  | .extend (source := before) _ joint _ realized => by
      exfalso
      change none ∈ ((application setup leaks).transition (initialLaw setup) horizon scheduler
        before joint).support at realized
      cases before with
      | none =>
          obtain ⟨_, _, impossible⟩ := PMF.support_map .. ▸ realized
          cases impossible
      | some control =>
          cases acting : control.actor with
          | none =>
              obtain ⟨_, impossible, _⟩ := transition_environment control acting joint realized
              cases impossible
          | some actor =>
              rw [transition_respond control acting joint, PMF.mem_support_pure_iff] at realized
              cases realized

/-- **Matching along a history.** If every actor completion along a native
history matches, so does every step. -/
theorem replayMatches_of_actorCompletions
    (assessment : setup.intendedModel.BehavioralAssessment) (who : Player) : ∀ {state}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state),
    ActorCompletionsMatch setup leaks bounds horizon scheduler assessment who trace →
      ReplayMatches setup leaks bounds horizon scheduler assessment who trace
  | _, .start, _ => trivial
  | _, .extend (source := before) (target := after) prior joint legal realized,
      ⟨priorMatches, actorMatches⟩ => by
      refine ⟨replayMatches_of_actorCompletions assessment who prior priorMatches,
        fun history replayed => ?_⟩
      change after ∈ ((application setup leaks).transition (initialLaw setup) horizon scheduler
        before joint).support at realized
      cases before with
      | none =>
          obtain rfl := trace_eq_start_of_none prior
          cases replayed
          exact replayStepMatches_start assessment who joint realized
      | some control =>
          cases acting : control.actor with
          | some actor =>
              exact replayStepMatches_respond assessment who history _ control acting joint
                realized
          | none =>
              obtain ⟨next, rfl, _⟩ := transition_environment control acting joint realized
              obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
                (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler prior control rfl
              have current : history.state =
                  some (residual.lift (ProtocolState.entry residual.program residual.source)) := by
                rw [intendedHistory?_state prior replayed]
                exact decodedPoint_eq residual
              rcases transition_configStep (initialLaw setup) horizon scheduler control next joint
                  realized with same | ⟨event, ready, action, member⟩
              · exact replayStepMatches_unchanged assessment who history _ control next acting
                  joint same
              · cases owner : (graph setup).actor? event with
                | none =>
                    exact replayStepMatches_chance assessment who history _ control next acting
                      joint residual current ready member owner
                | some mover =>
                    exact replayStepMatches_actor assessment who history _ control next acting
                      joint residual current ready member owner
                      (actorMatches history replayed control next rfl rfl acting event ready
                        action member mover owner)

section Projection

variable {who : Player}
  {site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who}
  {sourceSite : setup.intendedModel.InformationSite who}
  {past : List (application setup leaks).PlayerEntry} {view : (application setup leaks).PlayerView}

variable (setup leaks bounds horizon scheduler) in
open Classical in
/-- **The replay projection.** At a decision site of `who` whose projected view
is an intended site, a native history projects to its intended replay when that
exists, and to a fixed history of the intended site otherwise. -/
def replayProjection (sourceSite : setup.intendedModel.InformationSite who)
    (site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who)
    (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup leaks who site.1)
    (history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory
      who site.1) : setup.intendedModel.InformationHistory who sourceSite.1 :=
  match replayed : intendedHistory? setup leaks bounds horizon scheduler history.1.trace with
  | some replay => ⟨replay, by
      rw [projected, intendedHistory?_infoOf history.1 (history.2.trans decision) replayed,
        decision]⟩
  | none => sourceSite.2.choose

theorem replayProjection_eq (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup leaks who site.1)
    (history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory
      who site.1) {replay : setup.intendedProtocol.History}
    (replayed : intendedHistory? setup leaks bounds horizon scheduler history.1.trace =
      some replay) :
    (replayProjection setup leaks bounds horizon scheduler sourceSite site decision projected
      history).1 = replay := by
  unfold replayProjection
  split
  · rename_i other otherReplayed
    rw [replayed] at otherReplayed
    exact Option.some.inj otherReplayed.symm
  · rename_i otherReplayed
    rw [replayed] at otherReplayed
    cases otherReplayed

/-- **Source weights from the replay.** Under a fully mixed intended
assessment, at a native history of the site whose replay exists, along which
every actor completion matches, and whose unsettled content is one, the source
weight times the own reach of a fixed history of the intended site is the
intended reach of the replay projection. -/
theorem othersSourceWeight_mul_ownReach (assessment : setup.intendedModel.BehavioralAssessment)
    (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup leaks who site.1)
    (history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory
      who site.1) {replay : setup.intendedProtocol.History}
    (replayed : intendedHistory? setup leaks bounds horizon scheduler history.1.trace =
      some replay)
    (matching : ActorCompletionsMatch setup leaks bounds horizon scheduler assessment who
      history.1.trace)
    (settled : unsettledContent setup leaks bounds horizon scheduler assessment who
      history.1.trace = 1) :
    othersSourceWeight setup leaks bounds horizon scheduler assessment who history.1.trace *
        setup.intendedModel.playerReachProbability assessment.strategy who
          sourceSite.2.choose.1.trace =
      (setup.intendedModel.historyReachWeight assessment.strategy
        (replayProjection setup leaks bounds horizon scheduler sourceSite site decision projected
          history).1).toReal := by
  have weight := othersSourceWeight_eq_replay assessment who history.1.trace replayed
    (replayMatches_of_actorCompletions assessment who history.1.trace matching)
  rw [settled, mul_one] at weight
  have projection := replayProjection_eq decision projected history replayed
  have own := setup.intendedModel.playerReachProbability_eq_of_decisionRecall
    setup.intendedModel_decisionRecall assessment.strategy who sourceSite sourceSite.2.choose
    (replayProjection setup leaks bounds horizon scheduler sourceSite site decision projected
      history)
  rw [own, projection, weight,
    historyReachProbability_eq_player_mul_counterfactual setup.intendedModel
      assessment.strategy who replay.trace]
  ring

open Classical in
/-- **Forced-belief inputs from the intended replay.** At a forced decision site
of `who` whose projected view is an intended site, under a fully mixed intended
assessment at stage `n`, the replay projection supplies the source weights of
`Vegas.ForcedBeliefInputs` with the common own reach of the intended site as
the constant, as soon as every regular history of the site has a replay along
which every actor completion matches and whose unsettled content is one. The
common fibers and the honest counterparts remain inputs. -/
def ForcedBeliefInputs.ofReplay {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {profiles : ℕ → ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
    {steps : OperationalSteps setup leaks bounds horizon scheduler sequence profiles who}
    [Fintype ((onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      site.1)]
    [DecidableEq (setup.intendedModel.InformationHistory who sourceSite.1)]
    {scale floors : ℕ → ℝ} {depth : ℕ} {slack : ℝ} {n : ℕ}
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
      scheduler who site.1)
    (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup leaks who site.1)
    (mixed : (sequence n).IsFullyMixed)
    (faithful : ∀ history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who site.1,
      RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace →
      ∃ replay, intendedHistory? setup leaks bounds horizon scheduler history.1.trace =
          some replay ∧
        ActorCompletionsMatch setup leaks bounds horizon scheduler (sequence n) who
          history.1.trace ∧
        unsettledContent setup leaks bounds horizon scheduler (sequence n) who
          history.1.trace = 1)
    (fiberMass : ℝ)
    (fiber : ∀ point, ∑ history with RegularTrace setup leaks bounds horizon scheduler
        (sequence n) who history.1.trace ∧
        replayProjection setup leaks bounds horizon scheduler sourceSite site decision projected
          history = point,
      operationalWeight setup leaks who (steps.mass n)
        (operationalRecord setup leaks bounds horizon scheduler history.1.trace) = fiberMass)
    (counterpart : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory
        who site.1 →
      (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who site.1)
    (commonWeight : (onePacketInformation setup leaks bounds horizon
      scheduler).InformationHistory who site.1 → ℝ)
    (counterpart_regular : ∀ history, ¬ RegularTrace setup leaks bounds horizon scheduler
        (sequence n) who history.1.trace →
      RegularTrace setup leaks bounds horizon scheduler (sequence n) who
        (counterpart history).1.trace)
    (irregular_le : ∀ history, ¬ RegularTrace setup leaks bounds horizon scheduler (sequence n)
        who history.1.trace →
      ((onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight
          (profiles n) history.1).toReal ≤ scale n ^ 3 * commonWeight history)
    (counterpart_ge : ∀ history, ¬ RegularTrace setup leaks bounds horizon scheduler
        (sequence n) who history.1.trace →
      scale n ^ 2 * floors n ^ depth * commonWeight history ≤
        slack * ((onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight
          (profiles n) (counterpart history).1).toReal) :
    ForcedBeliefInputs setup leaks bounds horizon scheduler sequence profiles steps site
      sourceSite (replayProjection setup leaks bounds horizon scheduler sourceSite site decision
        projected) scale floors depth slack n where
  forced := forced
  projected := projected
  sourceScale := setup.intendedModel.playerReachProbability (sequence n).strategy who
    sourceSite.2.choose.1.trace
  sourceScale_pos := setup.intendedModel.playerReachProbability_pos (sequence n).strategy mixed
    who _
  sourceWeight history regular := by
    obtain ⟨replay, replayed, matching, settled⟩ := faithful history regular
    exact othersSourceWeight_mul_ownReach (sequence n) decision projected history replayed
      matching settled
  fiberMass := fiberMass
  fiber := fiber
  counterpart := counterpart
  commonWeight := commonWeight
  counterpart_regular := counterpart_regular
  irregular_le := irregular_le
  counterpart_ge := counterpart_ge

end Projection

end Vegas
