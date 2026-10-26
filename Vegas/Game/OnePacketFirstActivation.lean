/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCanonicalAcceptance
import Interaction.ReactiveDecisionPredecessor

/-! # Recorded response entries

A response appends one entry to its author's recall
(`Vegas.respondEntry`), and every later transition keeps that entry in place
(`Vegas.recordsEntry_transition`): at every later history the author's recall
splits around it (`Vegas.RecordsEntry`). A decision state is reached from an
idle state by activating its actor, which changes neither the application state
nor any recall (`Interaction.ReactiveApplication.decision_predecessor`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable (setup runtime leaks) in
/-- The envelope a response transmitting `material` emits. -/
def sentEnvelope (execution : (application setup runtime leaks).Execution) (who : Player)
    (material : (application setup runtime leaks).Submission) :
    Message Player (WitnessedPacket (graph setup)) :=
  ⟨(who, execution.network.nextSerial who),
    (application setup runtime leaks).packet
      ((application setup runtime leaks).submit execution.application who material) who
      (execution.network.known who) material⟩

variable (setup runtime leaks) in
/-- The recall entry a response appends: the view it was made from, the
response, and the envelope it emits. -/
def respondEntry (execution : (application setup runtime leaks).Execution) (who : Player)
    (response : (application setup runtime leaks).Action) : (application setup runtime
      leaks).PlayerEntry :=
  ⟨execution.observe (application setup runtime leaks) who, response,
    response.transmission.map (sentEnvelope setup runtime leaks execution who)⟩

variable (setup runtime leaks) in
/-- The recall of `who` at the protocol state splits around `entry`. -/
def RecordsEntry (who : Player) (entry : (application setup runtime leaks).PlayerEntry) :
    (application setup runtime leaks).ProtocolState → Prop
  | none => False
  | some control => ∃ earlier later, control.execution.recall who = earlier ++ entry :: later

/-- A response records its own entry. -/
theorem recordsEntry_respond (execution : (application setup runtime leaks).Execution) (who :
  Player)
    (response : (application setup runtime leaks).Action) (remaining : Nat)
    (actor : Option Player) :
    RecordsEntry setup runtime leaks who (respondEntry setup runtime leaks execution who response)
      (some ⟨remaining, actor, execution.respond (application setup runtime leaks) who response⟩)
        := by
  refine ⟨execution.recall who, [], ?_⟩
  rw [respond_recall, ite_eq_left rfl]
  rfl

/-- **Recorded entries stay recorded.** Every protocol transition, under
arbitrary responses and scheduler choices, keeps a recorded entry in place. -/
theorem recordsEntry_transition (who : Player) (entry : (application setup runtime
  leaks).PlayerEntry)
    (initial : PMF (application setup runtime leaks).State) (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler)
    (before after : (application setup runtime leaks).ProtocolState)
    (joint : Player → Option (application setup runtime leaks).Action)
    (holds : RecordsEntry setup runtime leaks who entry before)
    (reached : after ∈ ((application setup runtime leaks).transition initial horizon scheduler
      before
      joint).support) :
    RecordsEntry setup runtime leaks who entry after := by
  cases before with
  | none => exact holds.elim
  | some control =>
      obtain ⟨next, rfl, recalls⟩ := (application setup runtime leaks).transition_recall_prefix
        initial horizon scheduler control after joint reached
      obtain ⟨earlier, later, split⟩ := holds
      obtain ⟨tail, retained⟩ := recalls who
      refine ⟨earlier, later ++ tail, ?_⟩
      rw [← retained, split]
      simp only [List.append_assoc, List.cons_append]


section OnePacket

variable [Fintype Player] (bounds : MessageBounds (graph setup))

omit [Fintype Player] in
/-- The entry of a transmitting response records its envelope. -/
theorem respondEntry_of_transmission (execution : (application setup runtime leaks).Execution)
    (who : Player) (response : (application setup runtime leaks).Action)
    (material : (application setup runtime leaks).Submission)
    (submits : response.transmission = some material) :
    respondEntry setup runtime leaks execution who response =
      ⟨execution.observe (application setup runtime leaks) who, response,
        some (sentEnvelope setup runtime leaks execution who material)⟩ := by
  unfold respondEntry
  rw [submits]
  rfl

end OnePacket

end Vegas
