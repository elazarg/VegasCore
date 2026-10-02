/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceReplaySupport
import Vegas.Game.RevealServiceSignedTraffic
import Vegas.Game.RevealServiceTraffic

/-! # Clean replay histories and traffic under published replay aliases

At every active retained replay history no sample has been recorded and every
pending and transmitted packet is published. An ordinary response produces the
same traffic record as in the matching original history. -/

noncomputable section

namespace Vegas

open SourceProgram

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

end Vegas
