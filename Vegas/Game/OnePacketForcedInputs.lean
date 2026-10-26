/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketActorMatching

/-! # Forced-belief inputs at own-turn sites

At a decision site of `who` whose view shows its own ready event, every native
history in a forced state of `who` has unsettled content one: the ready event
is `who`'s own, so the period invariant leaves nothing unsettled
(`Vegas.unsettledContent_eq_one_of_ownTurn`). Every actor completion along it
matches (`Vegas.actorCompletionsMatch_of_forced`). So the source weights of
`Vegas.ForcedBeliefInputs` hold at such a site as soon as every regular history
of the site is in a forced state of `who` and has an intended replay
(`Vegas.ForcedBeliefInputs.ofForcedReplay`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- **Nothing is unsettled at the observer's own turn.** At a native history of
the one-packet game ending in a forced state of `who` whose view shows `who`'s
own ready event, the unsettled content is one. -/
theorem unsettledContent_eq_one_of_ownTurn
    (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    {control : (application setup runtime leaks).Control}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    (forced : ForcedState setup runtime leaks who (some control)) {event : (graph setup).EventId}
    (turn : (control.execution.observe (application setup runtime leaks)
      who).application.publicView.ownTurn? who = some event) :
    unsettledContent setup runtime leaks bounds horizon scheduler assessment who trace = 1 := by
  obtain ⟨publicReady, owned⟩ := PublicView.ownTurn?_spec _ who event turn
  have ready : control.execution.application.config.cut.Ready event :=
    (State.publicView_eventReady _ event).mp publicReady
  refine (periodInvariant (runtime := runtime) assessment who trace control rfl forced).quiet
    fun other otherReady sender acts => ?_
  have sameEvent := ready_unique (setup := setup) _ otherReady ready
  subst sameEvent
  exact Option.some.inj (acts.symm.trans owned)

section Assembly

variable {who : Player}
  {site : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationSite who}
  {sourceSite : setup.intendedModel.InformationSite who}
  {past : List (application setup runtime leaks).PlayerEntry}
  {view : (application setup runtime leaks).PlayerView}

/-- A native history of a decision site of `who` with recall `past` and view
`view` ends at an initialized state at which `who` acts and sees `view`. -/
theorem state_of_decision
    (history : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who
      site.1) (decision : site.1 = some (past, view)) :
    ∃ control : (application setup runtime leaks).Control, history.1.state = some control ∧
      control.execution.observe (application setup runtime leaks) who = view := by
  obtain ⟨⟨state, trace⟩, info⟩ := history
  have seen := info.trans decision
  rw [onePacket_infoOf] at seen
  cases state with
  | none => cases seen
  | some control =>
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at seen
        exact ⟨control, rfl, (Prod.mk.inj (Option.some.inj seen)).2⟩
      · simp [ReactiveApplication.observe, active] at seen

open Classical in
/-- **Forced-belief inputs at an own-turn site.** At a forced decision site of
`who` whose view shows `who`'s own ready event and whose projected view is an
intended site, under a fully mixed intended assessment at stage `n`, the
replay projection supplies the source weights of `Vegas.ForcedBeliefInputs`
as soon as every regular history of the site is in a forced state of `who` and
has an intended replay. The common fibers and the honest counterparts remain
inputs. -/
def ForcedBeliefInputs.ofForcedReplay
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {profiles : ℕ → ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player}
    {steps : OperationalSteps setup runtime leaks bounds horizon scheduler sequence profiles who}
    [Fintype ((onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who
      site.1)]
    [DecidableEq (setup.intendedModel.InformationHistory who sourceSite.1)]
    {scale floors : ℕ → ℝ} {depth : ℕ} {slack : ℝ} {n : ℕ}
    (forced : forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) (initialLaw
      setup) horizon
      scheduler who site.1)
    (decision : site.1 = some (past, view)) {event : (graph setup).EventId}
    (turn : view.application.publicView.ownTurn? who = some event)
    (projected : sourceSite.1 = projectView setup runtime leaks who site.1)
    (mixed : (sequence n).IsFullyMixed)
    (forcedHistories : ∀ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who site.1,
      RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who history.1.trace →
      ForcedState setup runtime leaks who history.1.state)
    (replayed : ∀ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who site.1,
      RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who history.1.trace →
      ∃ replay, intendedHistory? setup runtime leaks bounds horizon scheduler history.1.trace =
        some replay)
    (fiberMass : ℝ)
    (fiber : ∀ point, ∑ history with RegularTrace setup runtime leaks bounds horizon scheduler
        (sequence n) who history.1.trace ∧
        replayProjection setup runtime leaks bounds horizon scheduler sourceSite site decision
          projected
          history = point,
      operationalWeight setup runtime leaks who (steps.mass n)
        (operationalRecord setup runtime leaks bounds horizon scheduler history.1.trace) =
          fiberMass)
    (counterpart : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory
        who site.1 →
      (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationHistory who
        site.1)
    (commonWeight : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who site.1 → ℝ)
    (counterpart_regular : ∀ history, ¬ RegularTrace setup runtime leaks bounds horizon scheduler
        (sequence n) who history.1.trace →
      RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who
        (counterpart history).1.trace)
    (irregular_le : ∀ history, ¬ RegularTrace setup runtime leaks bounds horizon scheduler
      (sequence n)
        who history.1.trace →
      ((onePacketInformation setup runtime leaks bounds horizon scheduler).historyReachWeight
          (profiles n) history.1).toReal ≤ scale n ^ 3 * commonWeight history)
    (counterpart_ge : ∀ history, ¬ RegularTrace setup runtime leaks bounds horizon scheduler
        (sequence n) who history.1.trace →
      scale n ^ 2 * floors n ^ depth * commonWeight history ≤
        slack * ((onePacketInformation setup runtime leaks bounds horizon
          scheduler).historyReachWeight
          (profiles n) (counterpart history).1).toReal) :
    ForcedBeliefInputs setup runtime leaks bounds horizon scheduler sequence profiles steps site
      sourceSite (replayProjection setup runtime leaks bounds horizon scheduler sourceSite site
        decision
        projected) scale floors depth slack n :=
  ForcedBeliefInputs.ofReplay (runtime := runtime) forced decision projected mixed (fun history
    regular => by
      obtain ⟨replay, replayEq⟩ := replayed history regular
      have forcedHistory := forcedHistories history regular
      obtain ⟨control, stateEq, viewEq⟩ := state_of_decision (runtime := runtime) history decision
      obtain ⟨⟨state, trace⟩, info⟩ := history
      change state = some control at stateEq
      subst stateEq
      refine ⟨replay, replayEq, actorCompletionsMatch_of_forced (runtime := runtime) (sequence n)
        who trace control
        rfl forcedHistory, unsettledContent_eq_one_of_ownTurn (runtime := runtime) (sequence n)
          who trace
          forcedHistory (event := event) ?_⟩
      rw [viewEq]
      exact turn)
    fiberMass fiber counterpart commonWeight counterpart_regular irregular_le counterpart_ge

end Assembly

end Vegas
