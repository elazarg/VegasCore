/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketFirstActivationCompletion
import Vegas.Game.RecoveryStoppedSettlement
import Vegas.Game.OnePacketPendingClear

/-! # Compiled binding steps through actual recovery stopping boundaries -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat}
  {recoveryScheduler : ((runtime setup).recoveryApplication leaks).Scheduler}
  {bound : (graph setup).EventId → Nat}
  (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks initial horizon recoveryScheduler
    bound)

local notation "scheduler" => RecoveryProjection.nativeScheduler (runtime setup) leaks
  recoveryScheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun state => PublicExclusionRecord (RecoveryState.mk state ∅))

include initialized nativeLaw inclusion in
/-- At actual clear native continuation stops, and at the first exclusion step,
a recorded fixed-value commitment either remains pending in its sent configuration
or has performed exactly its successful compiled binding step. Only actual
recovery inclusion is assumed; no global native completion contract is used. -/
theorem recovery_committed_until_config
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (extraStop : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History → Prop)
    {who : Player} {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} (ready : sent.cut.Ready event) {rank : Nat}
    (ordered : sent.cut.IsPrefix rank) {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    {candidate : Handle (graph setup)} (call : message.payload.call = .commitment event candidate)
    {value : L.Val payload} (action : (graph setup).Action event)
    (successful : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      PublicationResult (L.Val payload)) = .success value)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History) {control : (application setup leaks).Control}
    (current : start.state = some control)
    (clear : PublicExclusionRecord
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (invariant : AcceptanceInvariant setup leaks bounds horizon scheduler who entry message event
      sent (some control))
    (atSent : control.execution.application.config = sent)
    (fixed : control.execution.application.candidates.lookup candidate =
      .openable ⟨payload, value⟩)
    (owned : (graph setup).actor? event = some who)
    (fresh : FreshCall setup leaks who event bound entry message) :
    ∀ stop ∈ (((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (fun history => LateStopped setup leaks bounds horizon scheduler rank history ∨
          ¬ Clear history.state ∨ extraStop history) start).support,
      ∃ final, stop.state = some final ∧
        (event ∉ final.execution.application.config.cut.completed →
          final.execution.application.config = sent) ∧
        (event ∈ final.execution.application.config.cut.completed →
          final.execution.application.config ∈ (sent.step event ready action).support ∧
            OutputSucceeded final.execution.application.config.store event) := by
  let completed := LateStopped setup leaks bounds horizon scheduler rank
  let model := (bounds.onePacketMenu (runtime setup) leaks).information
    (initialLaw setup) horizon scheduler
  have stopEq : (fun history => completed history ∨ ¬ Clear history.state ∨ extraStop history) =
      (fun history => ¬ Clear history.state ∨ completed history ∨ extraStop history) := by
    funext history
    exact propext or_left_comm
  have receipts := recovery_stopped_freshCall_receipt bounds initialized nativeLaw inclusion
    certificate players (fun history => completed history ∨ extraStop history)
    start control current clear who event owned entry message fresh
  exact committed_until_config certificate players
    (fun history => ¬ Clear history.state ∨ extraStop history) ready ordered
    (outputEq := outputEq) codeEq call action successful start current invariant atSent fixed
    (fun stopped member final state records done => by
      change stopped ∈ (model.runBehavioralUntil certificate players
        (fun history => completed history ∨ ¬ Clear history.state ∨ extraStop history)
        start).support at member
      rw [stopEq] at member
      exact receipts stopped member final state records done)

include initialized nativeLaw inclusion in
/-- Actual recovery completion discharges every premature terminal stop, while
public clarity of pending bindings rules out a premature exclusion stop. Every
stopped continuation therefore performs the successful compiled binding step. -/
theorem recovery_committed_stop_config
    (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon recoveryScheduler)
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {who : Player} {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} (ready : sent.cut.Ready event) {rank : Nat}
    (ordered : sent.cut.IsPrefix rank) {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    {candidate : Handle (graph setup)} (call : message.payload.call = .commitment event candidate)
    {value : L.Val payload} (action : (graph setup).Action event)
    (successful : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      PublicationResult (L.Val payload)) = .success value)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History) {control : (application setup leaks).Control}
    (current : start.state = some control)
    (clear : PublicExclusionRecord
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (invariant : AcceptanceInvariant setup leaks bounds horizon scheduler who entry message event
      sent (some control))
    (atSent : control.execution.application.config = sent)
    (fixed : control.execution.application.candidates.lookup candidate =
      .openable ⟨payload, value⟩)
    (owned : (graph setup).actor? event = some who)
    (fresh : FreshCall setup leaks who event bound entry message) :
    ∀ stop ∈ (((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (fun history => LateStopped setup leaks bounds horizon scheduler rank history ∨
          ¬ Clear history.state) start).support,
      ∃ final, stop.state = some final ∧
        final.execution.application.config ∈ (sent.step event ready action).support ∧
          OutputSucceeded final.execution.application.config.store event := by
  intro stopped supported
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := (menu).information (initialLaw setup) horizon scheduler
  let stop := fun history : (menu.protocol (initialLaw setup) horizon scheduler).History =>
    LateStopped setup leaks bounds horizon scheduler rank history ∨ ¬ Clear history.state
  have partialLaw := recovery_committed_until_config initialized nativeLaw inclusion
    certificate players (fun _ => False) ready ordered (outputEq := outputEq) codeEq call action
    successful start current clear invariant atSent fixed owned fresh
  obtain ⟨final, state, stable, completed⟩ := partialLaw stopped
    (by simpa only [or_false] using supported)
  have clearPending := pending_publicClear_of_acceptanceInvariant certificate players stop who
    entry message event sent start control current clear invariant stopped supported final state
  have ends := model.mem_support_runBehavioralUntil certificate players stop start stopped supported
  have done : event ∈ final.execution.application.config.cut.completed := by
    by_contra pending
    rcases ends with (prefixed | failed) | ended
    · obtain ⟨other, otherState, prefixed⟩ := prefixed
      rw [state] at otherState
      cases Option.some.inj otherState
      rw [stable pending] at prefixed
      exact Nat.succ_ne_self rank (isPrefix_unique prefixed ordered)
    · rw [state] at failed
      exact failed (clearPending pending)
    · rw [state] at ended
      have rawTrace := (menu).toRawTrace (initialLaw setup) horizon scheduler
        (state ▸ stopped.trace)
      rw [← nativeLaw] at rawTrace
      have terminal := Recovery.CompletesPlay.clear_native (runtime setup) leaks initialized
        completes final rawTrace (clearPending pending) ended
      exact pending (by rw [terminal]; exact Finset.mem_univ _)
  exact ⟨final, state, (completed done).1, (completed done).2⟩

end Vegas
