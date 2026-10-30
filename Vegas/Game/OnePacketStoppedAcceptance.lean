/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDisclosureCompletion
import Vegas.Game.OnePacketStoppedSettlement
import Vegas.Game.OnePacketPendingClear

/-! # Full continuations through counted native acceptance boundaries -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}
  {bound : (graph setup).EventId → Nat}
  (inclusion : ∀ control : (application setup runtime leaks).Control,
    ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) → control.execution.application.config.defaulted = ∅ →
    ProtectedInclusionAt runtime leaks control.execution bound)

local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "protocol" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup)
  horizon scheduler
local notation "model" => ReactiveApplication.ResponseMenu.information menu (initialLaw setup)
  horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks)
    (fun state : EventGraphRuntime.State (graph setup) =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config state) = ∅)

include inclusion in
/-- A supported counted stop either retains the sent configuration, or has the
same full graph continuation as the typed accepted event completion. -/
theorem counted_accepted_until_continuation
    (reference : (graph setup).BehavioralProfile)
    (certificate : (protocol).WellFoundedHistories)
    (players : ∀ player, (model).BehavioralPolicy player)
    (extraStop : (protocol).History → Prop)
    {who : Player} {entry : (application setup runtime leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} {action : (graph setup).Action event}
    {output : ((graph setup).outputLayout event).Value}
    (start : (protocol).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control)
    (clear : control.execution.application.config.defaulted = ∅)
    (invariant : AcceptanceInvariant setup runtime leaks bounds horizon scheduler who entry
      message event sent action output (some control))
    (atSent : control.execution.application.config = sent)
    (owned : (graph setup).actor? event = some who)
    (fresh : FreshCall setup leaks who event bound entry message) :
    ∀ stop ∈ ((model).runBehavioralUntil certificate players
      (fun history => (∃ final, history.state = some final ∧
        event ∈ final.execution.application.config.cut.completed) ∨
        ¬ Clear history.state ∨ extraStop history) start).support,
      ∃ final, stop.state = some final ∧
        (event ∉ final.execution.application.config.cut.completed →
          final.execution.application.config = sent) ∧
        (event ∈ final.execution.application.config.cut.completed →
          ∃ ready : sent.cut.Ready event, sent.actualDecision event action = some action ∧
            (graph setup).runPlan
                ((graph setup).policyPlan reference (graph setup).canonicalScheduler)
                final.execution.application.config.remaining final.execution.application.config =
              (graph setup).runPlan
                ((graph setup).policyPlan reference (graph setup).canonicalScheduler)
                (sent.complete event ready action output).remaining
                (sent.complete event ready action output)) := by
  let completed := fun history : (protocol).History => ∃ final, history.state = some final ∧
    event ∈ final.execution.application.config.cut.completed
  have stopEq : (fun history => completed history ∨ ¬ Clear history.state ∨ extraStop history) =
      (fun history => ¬ Clear history.state ∨ completed history ∨ extraStop history) := by
    funext history
    exact propext or_left_comm
  have receipts := counted_stopped_freshCall_receipt (runtime := runtime) bounds inclusion
    certificate players (fun history => completed history ∨ extraStop history)
    start control current clear who event owned entry message fresh
  exact accepted_until_continuation (runtime := runtime) reference certificate players
    (fun history => ¬ Clear history.state ∨ extraStop history) start current invariant atSent
    (fun stopped member final state records done => by
      change stopped ∈ ((model).runBehavioralUntil certificate players
        (fun history => completed history ∨ ¬ Clear history.state ∨ extraStop history)
        start).support at member
      rw [stopEq] at member
      exact receipts stopped member final state records done)

include inclusion in
/-- Public clarity while pending and terminal completion force every supported
counted completion stop to contain the actual event. Its full continuation is
that of the typed accepted action, including publication failure and draining. -/
theorem counted_accepted_stop_continuation
    (completes : ∀ control : (application setup runtime leaks).Control,
      (protocol).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      (application setup runtime leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (reference : (graph setup).BehavioralProfile)
    (certificate : (protocol).WellFoundedHistories)
    (players : ∀ player, (model).BehavioralPolicy player)
    {who : Player} {entry : (application setup runtime leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} {action : (graph setup).Action event}
    {output : ((graph setup).outputLayout event).Value}
    (start : (protocol).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control)
    (clear : control.execution.application.config.defaulted = ∅)
    (invariant : AcceptanceInvariant setup runtime leaks bounds horizon scheduler who entry
      message event sent action output (some control))
    (atSent : control.execution.application.config = sent)
    (owned : (graph setup).actor? event = some who)
    (fresh : FreshCall setup leaks who event bound entry message) :
    ∀ stop ∈ ((model).runBehavioralUntil certificate players
      (fun history => (∃ final, history.state = some final ∧
        event ∈ final.execution.application.config.cut.completed) ∨ ¬ Clear history.state)
      start).support,
      ∃ final, ∃ ready : sent.cut.Ready event, stop.state = some final ∧
        event ∈ final.execution.application.config.cut.completed ∧
        sent.actualDecision event action = some action ∧
        (graph setup).runPlan
            ((graph setup).policyPlan reference (graph setup).canonicalScheduler)
            final.execution.application.config.remaining final.execution.application.config =
          (graph setup).runPlan
            ((graph setup).policyPlan reference (graph setup).canonicalScheduler)
            (sent.complete event ready action output).remaining
            (sent.complete event ready action output) := by
  intro stopped supported
  let stop := fun history : (protocol).History => (∃ final, history.state = some final ∧
    event ∈ final.execution.application.config.cut.completed) ∨ ¬ Clear history.state
  have partialLaw := counted_accepted_until_continuation (runtime := runtime) inclusion reference
    certificate players (fun _ => False) start current clear invariant atSent owned fresh
  obtain ⟨final, state, _stable, completed⟩ := partialLaw stopped
    (by simpa only [or_false] using supported)
  have clearPending := pending_publicClear_of_acceptanceInvariant (runtime := runtime) certificate
    players stop who entry message event sent action output start control current clear invariant
    stopped supported final state
  have ends := (model).mem_support_runBehavioralUntil certificate players stop start stopped
    supported
  have done : event ∈ final.execution.application.config.cut.completed := by
    by_contra pending
    rcases ends with (completed | failed) | ended
    · obtain ⟨other, otherState, completed⟩ := completed
      rw [state] at otherState
      cases Option.some.inj otherState
      exact pending completed
    · rw [state] at failed
      exact failed (clearPending pending)
    · rw [state] at ended
      have terminal := completes final (state ▸ stopped.trace) (clearPending pending) ended
      exact pending (by rw [terminal]; exact Finset.mem_univ _)
  obtain ⟨ready, actual, continuation⟩ := completed done
  exact ⟨final, ready, state, done, actual, continuation⟩

end Vegas
