/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveContinuationObservation
import Vegas.Pending.EvidenceNormalization

/-! # Reconstructing the response entry from local information

Given the same local input and next sender serial, the same raw response adds
the same entry to own recall. This retains both the physical response name and
the emitted certificate or replay envelope. The sender counter is a separate
premise: the general message network does not put it in the player observation.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A player's own broadcast record reconstructs replay and evidence lookup
exactly, including first-match behavior in lists with repeated identifiers. -/
theorem known_eq_of_input_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (past : left.recall who = right.recall who)
    (view : left.observe (runtime.reactiveApplication leaks) who =
      right.observe (runtime.reactiveApplication leaks) who) :
    left.network.known who = right.network.known who := by
  have messages := congrArg ReactiveApplication.PlayerView.messages view
  have leaked := congrArg MessageNetwork.PlayerView.leaked messages
  have ledger := congrArg MessageNetwork.PlayerView.ledger messages
  change left.network.leaked who = right.network.leaked who at leaked
  change left.network.ledger = right.network.ledger at ledger
  rw [(runtime.reactiveApplication leaks).known_from_recall left who leftRecall,
    (runtime.reactiveApplication leaks).known_from_recall right who rightRecall, past]
  change _ ++ left.network.leaked who ++ left.network.ledger =
    _ ++ right.network.leaked who ++ right.network.ledger
  rw [leaked, ledger]

/-- The emitted packet is determined by the owner's observed candidate table
and known messages, even for a response carrying new private binding material. -/
theorem response_packet_eq_of_input_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (submission : WitnessedSubmission graph)
    (view : left.observe (runtime.reactiveApplication leaks) who =
      right.observe (runtime.reactiveApplication leaks) who)
    (remembered : left.application.remembered = right.application.remembered)
    (known : left.network.known who = right.network.known who) :
    submission.emit ((runtime.reactiveApplication leaks).submit left.application who submission)
        who (left.network.known who) =
      submission.emit ((runtime.reactiveApplication leaks).submit right.application who submission)
        who (right.network.known who) := by
  have observed := congrArg ReactiveApplication.PlayerView.application view
  have whole := reactive_playerView_congr runtime leaks left.application right.application
    who observed remembered
  have submitted := submit_playerView_congr runtime leaks left.application right.application
    who submission whole
  have candidates := congrArg (fun observed : PlayerView graph => observed.candidates) submitted
  have publics : ((runtime.reactiveApplication leaks).submit left.application who
        submission).publicView =
      ((runtime.reactiveApplication leaks).submit right.application who submission).publicView :=
    congrArg PlayerView.publicView submitted
  rw [WitnessedSubmission.emit_eq_resolve, WitnessedSubmission.emit_eq_resolve, publics]
  change WitnessedPacket.mk _ (submission.evidence.resolve who _ (left.network.known who)) _ =
    WitnessedPacket.mk _ (submission.evidence.resolve who _ (right.network.known who)) _
  rw [known]
  exact congrArg (fun table => WitnessedPacket.mk submission.call.packet
    (submission.evidence.resolve who table (right.network.known who))
    (((runtime.reactiveApplication leaks).submit right.application who
      submission).publicView.tokenFor submission.call.packet)) candidates

/-- The source checkpoint transcript supplies the serial premise. Together
with local input equality this reconstructs the entire next recall prefix. -/
theorem respond_recall_eq_of_input_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (past : left.recall who = right.recall who)
    (view : left.observe (runtime.reactiveApplication leaks) who =
      right.observe (runtime.reactiveApplication leaks) who)
    (remembered : left.application.remembered = right.application.remembered)
    (serial : left.network.nextSerial who = right.network.nextSerial who) :
    (left.respond (runtime.reactiveApplication leaks) who response).recall who =
      (right.respond (runtime.reactiveApplication leaks) who response).recall who := by
  have known := known_eq_of_input_eq runtime leaks left right who leftRecall rightRecall past view
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => simp only [ReactiveApplication.Execution.respond, ↓reduceIte, past, view]
  | some submission =>
      have packet := response_packet_eq_of_input_eq runtime leaks left right who submission
        view remembered known
      simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit, ↓reduceIte]
      change left.recall who ++ [⟨left.observe _ who, _,
        some ⟨(who, left.network.nextSerial who),
          submission.emit ((runtime.reactiveApplication leaks).submit left.application who
            submission) who (left.network.known who)⟩⟩] = _
      rw [past, view, serial, packet]
      rfl

end Vegas.EventGraphRuntime
