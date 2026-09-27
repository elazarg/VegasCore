/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceReplaySupport
import Vegas.Game.RevealServiceSignedTraffic
import Vegas.Game.RevealServiceTrafficSound

/-! # Conforming signed-envelope traffic under published replay aliases -/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (watcher : Player)
  (reveals : setup.program.RevealOnly)
  (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
  (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)

include reveals observer openable in
theorem replay_active_clean
    (history : ((replayMenu setup leaks bounds watcher).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).History)
    (control : (application setup leaks).Control) (state : history.state = some control)
    (who : Player) (active : control.actor = some who) :
    control.execution.network.leaked = (fun _ => []) ∧
      (∀ message ∈ control.execution.network.pending,
        message.id ∈ control.execution.network.ledger.map Message.id) ∧
      (∀ input ∈ control.execution.network.inputs,
        input.envelope.id ∈ control.execution.network.ledger.map Message.id) := by
  obtain ⟨original, first, current, same⟩ := replay_history_counterpart setup leaks bounds watcher
    reveals observer openable history control state
  have clean := active_history_clean setup leaks bounds watcher reveals observer openable original
    ⟨control.remaining, control.actor, first⟩ current who active
  exact ⟨same.leaked.symm.trans clean.1, same.pending_published clean.2.1,
    same.inputs_published clean.2.2⟩

omit [Fintype Player] in
theorem ReplayAgreement.ordinary_traffic
    {first second : (application setup leaks).Execution}
    (same : ReplayAgreement setup leaks watcher first second)
    (who : Player) (ordinary : who ≠ watcher) (remaining : Nat)
    (response : (application setup leaks).Action) :
    (application setup leaks).trafficStep (some ⟨remaining, some who, first⟩)
        (some ⟨remaining, none, first.respond (application setup leaks) who response⟩) =
      (application setup leaks).trafficStep (some ⟨remaining, some who, second⟩)
        (some ⟨remaining, none, second.respond (application setup leaks) who response⟩) := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rw [ReactiveApplication.trafficStep_silent, ReactiveApplication.trafficStep_silent]
  | some transmission =>
    cases transmission with
    | submit submission =>
      rw [ReactiveApplication.trafficStep_submit, ReactiveApplication.trafficStep_submit]
      rw [same.applicationEq, same.ledger, same.serials, same.known who ordinary]
    | replay id =>
      have known := same.known who ordinary
      cases found : (first.network.known who).find? (fun message => message.id = id) with
      | none =>
        have other : (second.network.known who).find? (fun message => message.id = id) = none :=
          known ▸ found
        simp only [ReactiveApplication.trafficStep, ReactiveApplication.Execution.respond,
          MessageNetwork.replay, found, other, List.drop_length, List.map_nil]
      | some message =>
        have other : (second.network.known who).find? (fun packet => packet.id = id) =
            some message := known ▸ found
        rw [(application setup leaks).trafficStep_replay first remaining who id message found,
          (application setup leaks).trafficStep_replay second remaining who id message other]
        rw [same.applicationEq, same.ledger]

omit [Fintype Player] in
private theorem published_replay_traffic (execution : (application setup leaks).Execution)
    (who : Player) (remaining : Nat) (id : MessageId Player)
    (published : id ∈ execution.network.ledger.map Message.id) :
    ∀ record ∈ (application setup leaks).trafficStep
      (some ⟨remaining, some who, execution⟩)
      (some ⟨remaining, none, execution.respond (application setup leaks) who ⟨some (.replay id)⟩⟩),
      permittedEnvelope setup leaks (envelopeEvidence setup leaks record) = true := by
  cases found : (execution.network.known who).find? (fun packet => packet.id = id) with
  | none =>
    simp only [ReactiveApplication.trafficStep, ReactiveApplication.Execution.respond,
      MessageNetwork.replay, found, List.drop_length, List.map_nil, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true]
  | some message =>
    rw [(application setup leaks).trafficStep_replay execution remaining who id message found]
    intro record recorded
    cases List.mem_singleton.mp recorded
    apply permittedEnvelope_published setup leaks
    have identified : message.id = id := by
      simpa only [decide_eq_true_eq] using List.find?_some found
    rw [identified]
    exact published

include reveals observer openable in
theorem replay_response_traffic
    (history : ((replayMenu setup leaks bounds watcher).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).History)
    (control : (application setup leaks).Control) (state : history.state = some control)
    (who : Player) (active : control.actor = some who)
    (response : (application setup leaks).Action)
    (allowed : response ∈ (replayMenu setup leaks bounds watcher).actions who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who)) :
    ∀ record ∈ (application setup leaks).trafficStep (some control)
      (some ⟨control.remaining, none,
        control.execution.respond (application setup leaks) who response⟩),
      permittedEnvelope setup leaks (envelopeEvidence setup leaks record) = true := by
  classical
  obtain ⟨original, first, current, same⟩ := replay_history_counterpart setup leaks bounds watcher
    reveals observer openable history control state
  by_cases watches : who = watcher
  · subst who
    have clean := replay_active_clean setup leaks bounds watcher reveals observer openable
      history control state watcher active
    have quiet : (application setup leaks).reportFirstUnpublished (control.execution.recall watcher)
        (control.execution.observe (application setup leaks) watcher) = FinDist.pure ⟨none⟩ := by
      apply ReactiveApplication.reportFirstUnpublished_silent
      intro message observed
      change message ∈ control.execution.network.leaked watcher at observed
      rw [clean.1] at observed
      exact (List.not_mem_nil observed).elim
    rw [replay_menu_watcher] at allowed
    rcases Finset.mem_union.mp allowed with silence | replayed
    · rw [quiet, FinDist.mem_supportFinset, FinDist.mem_support_pure] at silence
      subst response
      cases control with
      | mk remaining actor execution =>
        simp only at active
        subst actor
        simp only [ReactiveApplication.trafficStep_silent, List.not_mem_nil,
          IsEmpty.forall_iff, implies_true]
    · obtain ⟨message, published, rfl⟩ := (mem_publishedReplays setup leaks _ response).mp replayed
      have spent : message.id ∈ control.execution.network.ledger.map Message.id :=
        List.mem_map.mpr ⟨message, published, rfl⟩
      cases control with
      | mk remaining actor execution =>
        simp only at active
        subst actor
        exact published_replay_traffic setup leaks execution watcher remaining message.id spent
  · rw [replay_menu_ordinary setup leaks bounds watcher who watches] at allowed
    rw [← same.recall who watches, ← same.observe who] at allowed
    have conforming := retained_owner_response_traffic setup leaks bounds watcher who reveals
      observer openable watches original ⟨control.remaining, control.actor, first⟩ current
        active response allowed
    have sameTraffic := ReplayAgreement.ordinary_traffic setup leaks watcher same who watches
      control.remaining response
    cases control with
    | mk remaining actor execution =>
      simp only at active
      subst actor
      rw [← sameTraffic]
      intro record member
      exact permittedEnvelope_of_traffic setup leaks watcher record (conforming record member)


include reveals observer openable in
/-- Every actual C+ transition emits conforming signed-envelope evidence. -/
theorem replay_step_traffic
    (history : ((replayMenu setup leaks bounds watcher).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).History)
    (joint : Player → Option (application setup leaks).Action)
    (legal : ((replayMenu setup leaks bounds watcher).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).Legal history.state joint)
    (next : (application setup leaks).ProtocolState)
    (reached : next ∈ (((replayMenu setup leaks bounds watcher).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).step history.state
        ⟨joint, legal⟩).support) :
    ∀ record ∈ (application setup leaks).trafficStep history.state next,
      permittedEnvelope setup leaks (envelopeEvidence setup leaks record) = true := by
  let app := application setup leaks
  change next ∈ (app.transition (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) history.state joint).support at reached
  cases state : history.state with
  | none => simp only [ReactiveApplication.trafficStep, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true]
  | some control =>
    rw [state] at reached
    cases actor : control.actor with
    | some who =>
      have chosen := legal.2 who
      rw [state] at chosen
      cases selected : joint who with
      | none =>
        rw [selected] at chosen
        exact (chosen actor).elim
      | some response =>
        rw [selected] at chosen
        have allowed := chosen.2
        change response ∈ (replayMenu setup leaks bounds watcher).actions who
          (control.execution.recall who) (control.execution.observe app who) at allowed
        simp only [ReactiveApplication.transition, actor, selected,
          Option.getD_some, FinDist.mem_support_pure] at reached
        subst next
        exact replay_response_traffic setup leaks bounds watcher reveals observer openable
          history control state who actor response allowed
    | none =>
      cases countEq : control.remaining with
      | zero =>
        apply (legal.1 _).elim
        rw [state]
        exact ⟨countEq, actor⟩
      | succ remaining =>
        simp only [ReactiveApplication.transition, actor, countEq,
          FinDist.support_bind] at reached
        obtain ⟨command, _selected, moved⟩ := Set.mem_iUnion₂.mp reached
        obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ moved
        have noneTraffic := app.trafficStep_environment control.execution updated command
          supported remaining
        cases control with
        | mk count owner execution =>
          simp only at actor countEq
          subst count owner
          rw [noneTraffic]
          simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]

include reveals observer openable in
/-- The evidence checker is sound for every legal retained-replay history,
not only along a selected equilibrium. -/
theorem replay_history_traffic
    (history : ((replayMenu setup leaks bounds watcher).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).History) :
    ∀ record ∈ (application setup leaks).stateTraffic history.state,
      permittedEnvelope setup leaks (envelopeEvidence setup leaks record) = true := by
  let responses := replayMenu setup leaks bounds watcher
  rw [← responses.trafficAudit_eq_stateTraffic (initialLaw setup)
    (horizon setup watcher) (scheduler setup leaks watcher) history]
  rcases history with ⟨state, trace⟩
  induction trace with
  | start => simp only [ReactiveApplication.ResponseMenu.trafficAudit,
      ReactiveApplication.ResponseMenu.toRawTrace, ReactiveApplication.trafficAudit,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | @extend source target prior joint legal realized ih =>
    change ∀ record ∈ responses.trafficAudit (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) ⟨source, prior⟩ ++
        (application setup leaks).trafficStep source target, _
    intro record member
    rcases List.mem_append.mp member with previous | added
    · exact ih record previous
    · exact replay_step_traffic setup leaks bounds watcher reveals observer openable
        ⟨source, prior⟩ joint legal target realized record added

end Vegas.SourceProgram.RevealService
