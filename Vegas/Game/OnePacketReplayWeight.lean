/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketIntendedProjection
import GameTheoryExtensions.Analysis.Protocol.SingleMoverReach

/-! # Source weights against the counterfactual reach of the intended replay

The source weight of a native history (`Vegas.othersSourceWeight`) takes the
content factor of another player's packet when the packet is sent, while the
intended replay of the history (`Vegas.intendedHistory?`) takes the mover's
mass when the event completes. The *unsettled content* of a native history
(`Vegas.unsettledContent`) multiplies the content factors sent since the last
completion of an event with an actor, and is reset to one there.

**Bookkeeping.** Suppose that at every native step along a history whose
intended replay exists, the counterfactual reach of the replay times the
unsettled content after the step matches the counterfactual reach before times
the step's source factor times the unsettled content before
(`Vegas.ReplayStepMatches`). Then the source weight is the counterfactual reach
of the intended replay for the observer times the unsettled content
(`Vegas.othersSourceWeight_eq_replay`).

**The routine steps.** A response matches: its source factor is its content
factor, which the unsettled content takes, and the replay does not move
(`Vegas.replayStepMatches_respond`). A scheduler round completing no event
matches: its source factor is one and nothing moves
(`Vegas.replayStepMatches_unchanged`). What remains are the initial draw, the
completion of a chance event, and the completion of an event with an actor;
for each, matching is an explicit equality of one-step masses
(`Vegas.replayStepMatches_initial`, `Vegas.replayStepMatches_completion`).
-/

noncomputable section

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

/-- The unsettled content after one native transition: a response of another
player multiplies its content factor in; a scheduler round completing one
event with an actor resets it to one; anything else keeps it. -/
def unsettledStep (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (pending : ℝ) : (application setup leaks).ProtocolState →
      (Player → Option (application setup leaks).Action) →
        (application setup leaks).ProtocolState → ℝ
  | some before, joint, some after =>
      match before.actor with
      | some actor =>
          if actor = who then pending else
            pending * contentFactor setup leaks assessment actor before.execution
              after.execution ((joint actor).getD ⟨none⟩)
      | none =>
          match after.execution.application.config.history.drop
              before.execution.application.config.history.length with
          | [⟨event, _⟩] => if ((graph setup).actor? event).isSome then 1 else pending
          | _ => pending
  | _, _, _ => pending

/-- **The unsettled content** of a native history for an observer: the content
factors of other players' packets sent since the last completion of an event
with an actor. -/
def unsettledContent (assessment : setup.intendedModel.BehavioralAssessment) (who : Player) :
    ∀ {state}, (onePacketProtocol setup leaks bounds horizon scheduler).Trace state → ℝ
  | _, .start => 1
  | _, .extend (source := before) (target := after) prior joint _ _ =>
      unsettledStep setup leaks assessment who (unsettledContent assessment who prior) before joint
        after

/-- **A matching step.** Every intended history the replay reaches from
`history` through the native transition from `before` to `after` has
counterfactual reach for `who` times the unsettled content after the step equal
to the counterfactual reach of `history` times the step's source factor times
the unsettled content `pending` before it. -/
def ReplayStepMatches (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (history : setup.intendedProtocol.History) (pending : ℝ)
    (before : (application setup leaks).ProtocolState)
    (joint : Player → Option (application setup leaks).Action)
    (after : (application setup leaks).ProtocolState) : Prop :=
  ∀ next, advanceIntended? setup leaks history before after = some next →
    setup.intendedModel.counterfactualReachProbability assessment.strategy who next.trace *
        unsettledStep setup leaks assessment who pending before joint after =
      setup.intendedModel.counterfactualReachProbability assessment.strategy who history.trace *
        transitionSourceFactor setup leaks assessment who before joint after * pending

/-- Every step of a native history matches, from the replay of its prefix. -/
def ReplayMatches (assessment : setup.intendedModel.BehavioralAssessment) (who : Player) :
    ∀ {state}, (onePacketProtocol setup leaks bounds horizon scheduler).Trace state → Prop
  | _, .start => True
  | _, .extend (source := before) (target := after) prior joint _ _ =>
      ReplayMatches assessment who prior ∧
        ∀ history, intendedHistory? setup leaks bounds horizon scheduler prior = some history →
          ReplayStepMatches setup leaks assessment who history
            (unsettledContent setup leaks bounds horizon scheduler assessment who prior) before
            joint after

variable {setup leaks bounds horizon scheduler}

/-- **Source weights are counterfactual intended reach up to unsettled content.**
Along a native history whose intended replay exists and every step of which
matches, the source weight for `who` is the counterfactual reach of the replay
for `who` times the unsettled content. -/
theorem othersSourceWeight_eq_replay (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) : ∀ {state}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
    {history : setup.intendedProtocol.History},
    intendedHistory? setup leaks bounds horizon scheduler trace = some history →
    ReplayMatches setup leaks bounds horizon scheduler assessment who trace →
      othersSourceWeight setup leaks bounds horizon scheduler assessment who trace =
        setup.intendedModel.counterfactualReachProbability assessment.strategy who
            history.trace *
          unsettledContent setup leaks bounds horizon scheduler assessment who trace
  | _, .start, history, replayed, _ => by
      cases replayed
      simp [othersSourceWeight, unsettledContent, ExecutionProtocol.initHistory]
  | _, .extend (source := before) (target := after) prior joint legal realized, history,
      replayed, ⟨matchesPrior, matchesStep⟩ => by
      obtain ⟨previous, previousReplay, advanced⟩ := Option.bind_eq_some_iff.mp replayed
      have earlier := othersSourceWeight_eq_replay assessment who prior previousReplay
        matchesPrior
      have stepEq := matchesStep previous previousReplay history advanced
      simp only [othersSourceWeight, unsettledContent]
      rw [earlier, stepEq]
      ring

/-- **A response matches.** Its source factor is the content factor the pending
content takes, and a response completes no event, so the replay does not
move. -/
theorem replayStepMatches_respond (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (history : setup.intendedProtocol.History) (pending : ℝ)
    (control : (application setup leaks).Control) {actor : Player}
    (acting : control.actor = some actor)
    (joint : Player → Option (application setup leaks).Action)
    {after : (application setup leaks).ProtocolState}
    (realized : after ∈ ((application setup leaks).transition (initialLaw setup) horizon scheduler
      (some control) joint).support) :
    ReplayStepMatches setup leaks assessment who history pending (some control) joint after := by
  rw [transition_respond control acting joint, PMF.mem_support_pure_iff] at realized
  subst realized
  intro next advanced
  have kept := ((runtime setup).reactive_respond_application leaks control.execution actor
    ((joint actor).getD ⟨none⟩)).1
  change (match (control.execution.respond (application setup leaks) actor
      ((joint actor).getD ⟨none⟩)).application.config.history.drop
        control.execution.application.config.history.length with
    | [] => some history
    | [⟨event, action⟩] => extendIntended? setup history
        (decodeEventAction setup.program event action)
        (decodedPoint setup (control.execution.respond (application setup leaks) actor
          ((joint actor).getD ⟨none⟩)).application.config)
    | _ => none) = some next at advanced
  rw [kept, List.drop_length] at advanced
  cases advanced
  simp only [unsettledStep, transitionSourceFactor, acting]
  split_ifs <;> ring

/-- **A round completing no event matches.** Its source factor is one, and
neither the replay nor the unsettled content moves. -/
theorem replayStepMatches_unchanged (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (history : setup.intendedProtocol.History) (pending : ℝ)
    (before after : (application setup leaks).Control) (idle : before.actor = none)
    (joint : Player → Option (application setup leaks).Action)
    (kept : after.execution.application.config = before.execution.application.config) :
    ReplayStepMatches setup leaks assessment who history pending (some before) joint
      (some after) := by
  have dropped : after.execution.application.config.history.drop
      before.execution.application.config.history.length = [] := by
    rw [kept, List.drop_length]
  intro next advanced
  change (match after.execution.application.config.history.drop
      before.execution.application.config.history.length with
    | [] => some history
    | [⟨event, action⟩] => extendIntended? setup history
        (decodeEventAction setup.program event action)
        (decodedPoint setup after.execution.application.config)
    | _ => none) = some next at advanced
  rw [dropped] at advanced
  cases advanced
  simp only [unsettledStep, transitionSourceFactor, idle, completionMass, dropped]
  ring

omit [Fintype Player] in
/-- The intended history an extension by the acting joint reaches. -/
theorem extendIntended?_eq_some {history : setup.intendedProtocol.History}
    {choice : Option (OwnAction Player L)} {target : setup.ProtocolState}
    {next : setup.intendedProtocol.History}
    (extended : extendIntended? setup history choice target = some next) :
    ∃ (legal : setup.intendedProtocol.Legal history.state (actingJoint setup history.state choice))
      (reached : target ∈ (setup.intendedProtocol.step history.state
        ⟨actingJoint setup history.state choice, legal⟩).support),
      next = ⟨target, history.trace.extend _ legal reached⟩ := by
  unfold extendIntended? at extended
  split at extended
  · rename_i legal
    split at extended
    · rename_i reached
      cases extended
      exact ⟨legal, reached, rfl⟩
    · cases extended
  · cases extended

/-- **The initial draw matches** when the intended initial step gives the
decoded initial point the mass the native initial law gives the initial
state. -/
theorem replayStepMatches_initial (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (after : (application setup leaks).Control)
    (joint : Player → Option (application setup leaks).Action)
    (initialMass : (setup.protocolStep none (fun _ => none)
        (decodedPoint setup after.execution.application.config)).toReal =
      (initialLaw setup after.execution.application).toReal) :
    ReplayStepMatches setup leaks assessment who setup.intendedProtocol.initHistory 1 none joint
      (some after) := by
  intro next advanced
  obtain ⟨legal, reached, rfl⟩ := extendIntended?_eq_some advanced
  have opponents := setup.intendedModel.opponentsStepProb_eq_one_of_none assessment.strategy
    who setup.intendedProtocol.initHistory.trace ⟨_, legal⟩ (fun _ => rfl)
  simp only [counterfactualReachProbability, counterfactualStepProb, opponents, unsettledStep,
    transitionSourceFactor]
  change setup.intendedModel.counterfactualReachProbability assessment.strategy who
      (ExecutionProtocol.Trace.start : setup.intendedProtocol.Trace setup.intendedProtocol.init) *
      (1 * (setup.protocolStep none (fun _ => none)
        (decodedPoint setup after.execution.application.config)).toReal) * 1 =
    setup.intendedModel.counterfactualReachProbability assessment.strategy who
      (ExecutionProtocol.Trace.start : setup.intendedProtocol.Trace setup.intendedProtocol.init) *
      (initialLaw setup after.execution.application).toReal * 1
  rw [initialMass]
  ring

/-- **A completion matches** when the counterfactual step of the replay, times
the unsettled content after the completion, is the completion's source factor
times the unsettled content before it. -/
theorem replayStepMatches_completion (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (history : setup.intendedProtocol.History) (pending : ℝ)
    (before after : (application setup leaks).Control) (idle : before.actor = none)
    (joint : Player → Option (application setup leaks).Action)
    {event : (graph setup).EventId} (ready : before.execution.application.config.cut.Ready event)
    {action : (graph setup).Action event}
    (member : after.execution.application.config ∈
      (before.execution.application.config.step event ready action).support)
    (close : ∀ legal : setup.intendedProtocol.Legal history.state
        (actingJoint setup history.state (decodeEventAction setup.program event action)),
      setup.intendedModel.counterfactualStepProb assessment.strategy who history.trace
          ⟨_, legal⟩ (decodedPoint setup after.execution.application.config) *
        (if ((graph setup).actor? event).isSome then 1 else pending) =
      completionMass setup before.execution.application after.execution.application *
        pending) :
    ReplayStepMatches setup leaks assessment who history pending (some before) joint
      (some after) := by
  have dropped : after.execution.application.config.history.drop
      before.execution.application.config.history.length = [⟨event, action⟩] := by
    rw [EventGraph.Config.step_history _ event ready action _ member, List.drop_left]
  intro next advanced
  change (match after.execution.application.config.history.drop
      before.execution.application.config.history.length with
    | [] => some history
    | [⟨event, action⟩] => extendIntended? setup history
        (decodeEventAction setup.program event action)
        (decodedPoint setup after.execution.application.config)
    | _ => none) = some next at advanced
  rw [dropped] at advanced
  obtain ⟨legal, reached, rfl⟩ := extendIntended?_eq_some advanced
  have stepEq := close legal
  simp only [unsettledStep, transitionSourceFactor, idle, dropped,
    counterfactualReachProbability]
  rw [mul_assoc, stepEq]
  ring

end Vegas
