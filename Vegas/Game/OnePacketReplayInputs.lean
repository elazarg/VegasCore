module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketActorCompletion
public import Vegas.Game.SourceServiceFacts
public import Vegas.Game.OnePacketForcedBeliefs

@[expose] public section

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
(`Vegas.ForcedBeliefInputs.ofReplay`). Common fibers follow from bijections
between fibers that keep the operational record (`Vegas.fiber_sum_eq_of_swap`).
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
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)

/-- **Matching actor completions.** At every completion of an event with an
actor along a native history, from the replay of its prefix, the other
players' factor of the replayed step for `who` is the unsettled content of the
prefix. -/
def ActorCompletionsMatch (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) :
    ∀ {state}, (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace state → Prop
  | _, .start => True
  | _, .extend (source := before) (target := after) prior _ _ _ =>
      ActorCompletionsMatch assessment who prior ∧
        ∀ history, intendedHistory? setup timeouts leaks bounds horizon scheduler prior = some
          history →
          ∀ (current next : (application setup timeouts leaks).Control), before = some current →
            after = some next → current.actor = none →
            ∀ (completion : (graph setup).Completion)
              (_ready : current.execution.application.config.cut.Ready completion.event),
              next.execution.application.config.history.drop
                current.execution.application.config.history.length = [completion] →
              ∀ actor, (graph setup).actor? completion.event = some actor →
              ∀ legal : setup.intendedProtocol.Legal history.state
                  (actingJoint setup history.state
                    (completion.decision.bind (decodeEventAction setup.program completion.event))),
                setup.intendedModel.opponentsStepProb assessment.strategy who history.trace
                  ⟨_, legal⟩ =
                unsettledContent setup timeouts leaks bounds horizon scheduler assessment who prior

variable {setup timeouts leaks bounds horizon scheduler}

/-- **Matching along a history.** If every actor completion along a native
history matches, so does every step. -/
theorem replayMatches_of_actorCompletions
    (assessment : setup.intendedModel.BehavioralAssessment) (who : Player) : ∀ {state}
    (trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace state),
    ActorCompletionsMatch setup timeouts leaks bounds horizon scheduler assessment who trace →
      ReplayMatches setup timeouts leaks bounds horizon scheduler assessment who trace
  | _, .start, _ => trivial
  | _, .extend (source := before) (target := after) prior joint legal realized,
      ⟨priorMatches, actorMatches⟩ => by
      refine ⟨replayMatches_of_actorCompletions assessment who prior
        priorMatches,
        fun history replayed => ?_⟩
      change after ∈ ((application setup timeouts leaks).transition (initialLaw setup) horizon
        scheduler
        before joint).support at realized
      cases before with
      | none =>
          obtain rfl := trace_eq_start_of_none (timeouts := timeouts) prior
          cases replayed
          exact replayStepMatches_start (timeouts := timeouts) assessment who joint realized
      | some control =>
          cases acting : control.actor with
          | some actor =>
              exact replayStepMatches_respond (timeouts := timeouts) assessment who history _
                control acting joint
                realized
          | none =>
              obtain ⟨next, rfl, _⟩ := transition_environment (timeouts := timeouts) control acting
                joint realized
              obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (timeouts := timeouts)
                (failureProfile setup.program)
                (bounds.onePacketMenu timeouts leaks) horizon scheduler prior control rfl
              have current : history.state =
                  some (residual.lift (ProtocolState.entry residual.program residual.source)) := by
                rw [intendedHistory?_state (timeouts := timeouts) prior replayed]
                exact decodedPoint_eq residual
              have path := (reactive_protocol_graph_steps timeouts) leaks (initialLaw setup)
                horizon scheduler control next joint realized
              cases dropped : next.execution.application.config.history.drop
                  control.execution.application.config.history.length with
              | nil =>
                  have length := congrArg List.length dropped
                  simp only [List.length_drop, List.length_nil] at length
                  have same := EventGraph.Config.Step.path_eq_of_history_length_le path (by omega)
                  exact replayStepMatches_unchanged (timeouts := timeouts) assessment who history _
                    control next acting joint same
              | cons completion rest =>
                  cases rest with
                  | nil =>
                      obtain ⟨ready, action, member⟩ :=
                        EventGraph.Config.Step.path_singleton path completion dropped
                      cases owner : (graph setup).actor? completion.event with
                      | none =>
                          exact replayStepMatches_chance (timeouts := timeouts) assessment who
                            history _ control next acting joint residual current ready member owner
                      | some mover =>
                          have raw := (bounds.onePacketMenu timeouts leaks).toRawTrace
                            (initialLaw setup) horizon scheduler prior
                          have facts := legalFacts setup leaks horizon scheduler control raw
                          have active := control.execution.application.active_of_ready_owned
                            facts.quiescent ready owner
                          exact replayStepMatches_actor (timeouts := timeouts) assessment who
                            history _ control next acting joint residual current completion ready
                            member dropped owner active
                            (actorMatches history replayed control next rfl rfl acting completion
                              ready dropped mover owner)
                  | cons other tail =>
                      intro final advanced
                      simp only [advanceIntended?, dropped] at advanced
                      cases advanced

section Projection


variable {who : Player}
  {site : (onePacketInformation setup timeouts leaks bounds horizon scheduler).InformationSite who}
  {sourceSite : setup.intendedModel.InformationSite who}
  {past : List (application setup timeouts leaks).PlayerEntry} {view : (application setup timeouts
    leaks).PlayerView}

variable (setup timeouts leaks bounds horizon scheduler) in
open Classical in
/-- **The replay projection.** At a decision site of `who` whose projected view
is an intended site, a native history projects to its intended replay when that
exists, and to a fixed history of the intended site otherwise. -/
def replayProjection (sourceSite : setup.intendedModel.InformationSite who)
    (site : (onePacketInformation setup timeouts leaks bounds horizon scheduler).InformationSite
      who)
    (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup timeouts leaks who site.1)
    (history : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationHistory
      who site.1) : setup.intendedModel.InformationHistory who sourceSite.1 :=
  match replayed : intendedHistory? setup timeouts leaks bounds horizon scheduler history.1.trace
    with
  | some replay => ⟨replay, by
      rw [projected, intendedHistory?_infoOf (timeouts := timeouts) history.1 (history.2.trans
        decision) replayed,
        decision]⟩
  | none => sourceSite.2.choose

theorem replayProjection_eq (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup timeouts leaks who site.1)
    (history : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationHistory
      who site.1) {replay : setup.intendedProtocol.History}
    (replayed : intendedHistory? setup timeouts leaks bounds horizon scheduler history.1.trace =
      some replay) :
    (replayProjection setup timeouts leaks bounds horizon scheduler sourceSite site decision
      projected
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
    (projected : sourceSite.1 = projectView setup timeouts leaks who site.1)
    (history : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationHistory
      who site.1) {replay : setup.intendedProtocol.History}
    (replayed : intendedHistory? setup timeouts leaks bounds horizon scheduler history.1.trace =
      some replay)
    (matching : ActorCompletionsMatch setup timeouts leaks bounds horizon scheduler assessment who
      history.1.trace)
    (settled : unsettledContent setup timeouts leaks bounds horizon scheduler assessment who
      history.1.trace = 1) :
    othersSourceWeight setup timeouts leaks bounds horizon scheduler assessment who
      history.1.trace *
        setup.intendedModel.playerReachProbability assessment.strategy who
          sourceSite.2.choose.1.trace =
      (setup.intendedModel.historyReachWeight assessment.strategy
        (replayProjection setup timeouts leaks bounds horizon scheduler sourceSite site decision
          projected
          history).1).toReal := by
  have weight := othersSourceWeight_eq_replay (timeouts := timeouts) assessment who history.1.trace
    replayed
    (replayMatches_of_actorCompletions (timeouts := timeouts) assessment who history.1.trace
      matching)
  rw [settled, mul_one] at weight
  have projection := replayProjection_eq (timeouts := timeouts) decision projected history replayed
  have own := setup.intendedModel.playerReachProbability_eq_of_decisionRecall
    setup.intendedModel_decisionRecall assessment.strategy who sourceSite sourceSite.2.choose
    (replayProjection setup timeouts leaks bounds horizon scheduler sourceSite site decision
      projected
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
      (onePacketInformation setup timeouts leaks bounds horizon scheduler).BehavioralPolicy player}
    {steps : OperationalSteps setup timeouts leaks bounds horizon scheduler sequence profiles who}
    [Fintype ((onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationHistory who
      site.1)]
    [DecidableEq (setup.intendedModel.InformationHistory who sourceSite.1)]
    {scale floors : ℕ → ℝ} {depth : ℕ} {slack : ℝ} {n : ℕ}
    (forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks) (initialLaw
      setup) horizon
      scheduler who site.1)
    (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup timeouts leaks who site.1)
    (mixed : (sequence n).IsFullyMixed)
    (faithful : ∀ history : (onePacketInformation setup timeouts leaks bounds horizon
        scheduler).InformationHistory who site.1,
      RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who history.1.trace →
      ∃ replay, intendedHistory? setup timeouts leaks bounds horizon scheduler history.1.trace =
          some replay ∧
        ActorCompletionsMatch setup timeouts leaks bounds horizon scheduler (sequence n) who
          history.1.trace ∧
        unsettledContent setup timeouts leaks bounds horizon scheduler (sequence n) who
          history.1.trace = 1)
    (fiberMass : ℝ)
    (fiber : ∀ point, ∑ history with RegularTrace setup timeouts leaks bounds horizon scheduler
        (sequence n) who history.1.trace ∧
        replayProjection setup timeouts leaks bounds horizon scheduler sourceSite site decision
          projected
          history = point,
      operationalWeight setup timeouts leaks who (steps.mass n)
        (operationalRecord setup timeouts leaks bounds horizon scheduler history.1.trace) =
          fiberMass)
    (counterpart : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationHistory
        who site.1 →
      (onePacketInformation setup timeouts leaks bounds horizon scheduler).InformationHistory who
        site.1)
    (commonWeight : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationHistory who site.1 → ℝ)
    (counterpart_regular : ∀ history, ¬ RegularTrace setup timeouts leaks bounds horizon scheduler
        (sequence n) who history.1.trace →
      RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
        (counterpart history).1.trace)
    (irregular_le : ∀ history, ¬ RegularTrace setup timeouts leaks bounds horizon scheduler
      (sequence n)
        who history.1.trace →
      ((onePacketInformation setup timeouts leaks bounds horizon scheduler).historyReachWeight
          (profiles n) history.1).toReal ≤ scale n ^ 3 * commonWeight history)
    (counterpart_ge : ∀ history, ¬ RegularTrace setup timeouts leaks bounds horizon scheduler
        (sequence n) who history.1.trace →
      scale n ^ 2 * floors n ^ depth * commonWeight history ≤
        slack * ((onePacketInformation setup timeouts leaks bounds horizon
          scheduler).historyReachWeight
          (profiles n) (counterpart history).1).toReal) :
    ForcedBeliefInputs setup timeouts leaks bounds horizon scheduler sequence profiles steps site
      sourceSite (replayProjection setup timeouts leaks bounds horizon scheduler sourceSite site
        decision
        projected) scale floors depth slack n where
  forced := forced
  projected := projected
  sourceScale := setup.intendedModel.playerReachProbability (sequence
    n).strategy who
    sourceSite.2.choose.1.trace
  sourceScale_pos := setup.intendedModel.playerReachProbability_pos (sequence
    n).strategy mixed
    who _
  sourceWeight history regular := by
    obtain ⟨replay, replayed, matching, settled⟩ := faithful history regular
    exact othersSourceWeight_mul_ownReach (timeouts := timeouts) (sequence n) decision projected
      history replayed
      matching settled
  fiberMass := fiberMass
  fiber := fiber
  counterpart := counterpart
  commonWeight := commonWeight
  counterpart_regular := counterpart_regular
  irregular_le := irregular_le
  counterpart_ge := counterpart_ge

open Classical in
/-- **Common fibers from swaps.** If, between the regular histories of the site
projecting to an intended history and those projecting to a base intended
history, a bijection keeps the operational record, then their operational
weights have the same sum. Such a bijection exchanges the other players' hidden
values, which the operational record does not read while no reveal is
pending. -/
theorem fiber_sum_eq_of_swap {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {profiles : ℕ → ∀ player,
      (onePacketInformation setup timeouts leaks bounds horizon scheduler).BehavioralPolicy player}
    {steps : OperationalSteps setup timeouts leaks bounds horizon scheduler sequence profiles who}
    [Fintype ((onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationHistory who
      site.1)]
    [DecidableEq (setup.intendedModel.InformationHistory who sourceSite.1)] {n : ℕ}
    (project : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationHistory who
      site.1 → setup.intendedModel.InformationHistory who sourceSite.1)
    (point base : setup.intendedModel.InformationHistory who sourceSite.1)
    (swap : {history // RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
        history.1.trace ∧ project history = point} ≃
      {history // RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
        history.1.trace ∧ project history = base})
    (record : ∀ history, operationalRecord setup timeouts leaks bounds horizon scheduler
        (swap history).1.1.trace =
      operationalRecord setup timeouts leaks bounds horizon scheduler history.1.1.trace) :
    ∑ history with RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
        history.1.trace ∧ project history = point,
      operationalWeight setup timeouts leaks who (steps.mass n)
        (operationalRecord setup timeouts leaks bounds horizon scheduler history.1.trace) =
    ∑ history with RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
        history.1.trace ∧ project history = base,
      operationalWeight setup timeouts leaks who (steps.mass n)
        (operationalRecord setup timeouts leaks bounds horizon scheduler history.1.trace) := by
  rw [← Finset.sum_subtype_eq_sum_filter, ← Finset.sum_subtype_eq_sum_filter,
    Finset.subtype_univ, Finset.subtype_univ]
  exact Fintype.sum_equiv swap _ _ fun history => by rw [record history]

end Projection

end Vegas
