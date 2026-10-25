/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDisclosureCompletion
import Vegas.Game.OnePacketStoppedSettlement
import Vegas.Game.OnePacketPendingClear

/-! # Accepted calls through counted native stopping boundaries -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  {bound : (graph setup).EventId → Nat}
  (inclusion : ∀ control : (application setup leaks).Control,
    (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control) →
    ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
    ProtectedInclusionAt (runtime setup) leaks control.execution bound)

local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun state => ExclusionEvidence 0 ∅ (RecoveryState.mk state ∅))

include inclusion in
/-- At actual clear native continuation stops, and at the first exclusion step,
a recorded accepted call either remains pending in its sent configuration
or has performed a successful compiled event step. Only actual
recovery inclusion is assumed; no global native completion contract is used. -/
theorem counted_accepted_until_config
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (extraStop : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History → Prop)
    {who : Player} {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} (ready : sent.cut.Ready event) {rank : Nat}
    (ordered : sent.cut.IsPrefix rank)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History) {control : (application setup leaks).Control}
    (current : start.state = some control)
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (invariant : AcceptanceInvariant setup leaks bounds horizon scheduler who entry message event
      sent (some control))
    (atSent : control.execution.application.config = sent)
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
          ∃ action, final.execution.application.config ∈ (sent.step event ready action).support ∧
            OutputSucceeded final.execution.application.config.store event) := by
  let completed := LateStopped setup leaks bounds horizon scheduler rank
  let model := (bounds.onePacketMenu (runtime setup) leaks).information
    (initialLaw setup) horizon scheduler
  have stopEq : (fun history => completed history ∨ ¬ Clear history.state ∨ extraStop history) =
      (fun history => ¬ Clear history.state ∨ completed history ∨ extraStop history) := by
    funext history
    exact propext or_left_comm
  have receipts := counted_stopped_freshCall_receipt bounds inclusion
    certificate players (fun history => completed history ∨ extraStop history)
    start control current clear who event owned entry message fresh
  exact accepted_until_config certificate players
    (fun history => ¬ Clear history.state ∨ extraStop history) ready ordered
    start current invariant atSent
    (fun stopped member final state records done => by
      change stopped ∈ (model.runBehavioralUntil certificate players
        (fun history => completed history ∨ ¬ Clear history.state ∨ extraStop history)
        start).support at member
      rw [stopEq] at member
      exact receipts stopped member final state records done)

include inclusion in
/-- Counted native completion discharges every premature terminal stop, while
public clarity while pending rules out a premature exclusion stop. Every
stopped continuation therefore performs a successful compiled event step. -/
theorem counted_accepted_stop_config
    (completes : ∀ control : (application setup leaks).Control,
    (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control) →
    ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
    (application setup leaks).terminal (some control) →
    control.execution.application.config.cut.Terminal)
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {who : Player} {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} (ready : sent.cut.Ready event) {rank : Nat}
    (ordered : sent.cut.IsPrefix rank)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History) {control : (application setup leaks).Control}
    (current : start.state = some control)
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (invariant : AcceptanceInvariant setup leaks bounds horizon scheduler who entry message event
      sent (some control))
    (atSent : control.execution.application.config = sent)
    (owned : (graph setup).actor? event = some who)
    (fresh : FreshCall setup leaks who event bound entry message) :
    ∀ stop ∈ (((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (fun history => LateStopped setup leaks bounds horizon scheduler rank history ∨
          ¬ Clear history.state) start).support,
      ∃ final action, stop.state = some final ∧
        final.execution.application.config ∈ (sent.step event ready action).support ∧
          OutputSucceeded final.execution.application.config.store event := by
  intro stopped supported
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := (menu).information (initialLaw setup) horizon scheduler
  let stop := fun history : (menu.protocol (initialLaw setup) horizon scheduler).History =>
    LateStopped setup leaks bounds horizon scheduler rank history ∨ ¬ Clear history.state
  have partialLaw := counted_accepted_until_config inclusion
    certificate players (fun _ => False) ready ordered start current clear invariant atSent owned
    fresh
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
      have terminal := completes final (state ▸ stopped.trace) (clearPending pending) ended
      exact pending (by rw [terminal]; exact Finset.mem_univ _)
  obtain ⟨action, stepMember, succeeded⟩ := completed done
  exact ⟨final, action, state, stepMember, succeeded⟩

end Vegas
