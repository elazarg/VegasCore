/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCanonicalAcceptance

/-! # Recorded response entries

A response appends one entry to its author's recall
(`Vegas.respondEntry`), and every later transition keeps that entry in place
(`Vegas.recordsEntry_transition`): at every later history the author's recall
splits around it (`Vegas.RecordsEntry`). A decision state is reached from an
idle state by activating its actor, which changes neither the application state
nor any recall (`Vegas.decision_predecessor`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable (setup leaks) in
/-- The envelope a response transmitting `material` emits. -/
def sentEnvelope (execution : (application setup leaks).Execution) (who : Player)
    (material : (application setup leaks).Submission) :
    Message Player (WitnessedPacket (graph setup)) :=
  ⟨(who, execution.network.nextSerial who),
    (application setup leaks).packet
      ((application setup leaks).submit execution.application who material) who
      (execution.network.known who) material⟩

variable (setup leaks) in
/-- The recall entry a response appends: the view it was made from, the
response, and the envelope it emits. -/
def respondEntry (execution : (application setup leaks).Execution) (who : Player)
    (response : (application setup leaks).Action) : (application setup leaks).PlayerEntry :=
  ⟨execution.observe (application setup leaks) who, response,
    response.transmission.map (sentEnvelope setup leaks execution who)⟩

variable (setup leaks) in
/-- The recall of `who` at the protocol state splits around `entry`. -/
def RecordsEntry (who : Player) (entry : (application setup leaks).PlayerEntry) :
    (application setup leaks).ProtocolState → Prop
  | none => False
  | some control => ∃ earlier later, control.execution.recall who = earlier ++ entry :: later

/-- A response records its own entry. -/
theorem recordsEntry_respond (execution : (application setup leaks).Execution) (who : Player)
    (response : (application setup leaks).Action) (remaining : Nat)
    (actor : Option Player) :
    RecordsEntry setup leaks who (respondEntry setup leaks execution who response)
      (some ⟨remaining, actor, execution.respond (application setup leaks) who response⟩) := by
  refine ⟨execution.recall who, [], ?_⟩
  rw [respond_recall, ite_eq_left rfl]
  rfl

/-- **Recorded entries stay recorded.** Every protocol transition, under
arbitrary responses and scheduler choices, keeps a recorded entry in place. -/
theorem recordsEntry_transition (who : Player) (entry : (application setup leaks).PlayerEntry)
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (before after : (application setup leaks).ProtocolState)
    (joint : Player → Option (application setup leaks).Action)
    (holds : RecordsEntry setup leaks who entry before)
    (reached : after ∈ ((application setup leaks).transition initial horizon scheduler before
      joint).support) :
    RecordsEntry setup leaks who entry after := by
  cases before with
  | none => exact holds.elim
  | some control =>
      obtain ⟨next, rfl, recalls⟩ := (application setup leaks).transition_recall_prefix
        initial horizon scheduler control after joint reached
      obtain ⟨earlier, later, split⟩ := holds
      obtain ⟨tail, retained⟩ := recalls who
      refine ⟨earlier, later ++ tail, ?_⟩
      rw [← retained, split]
      simp only [List.append_assoc, List.cons_append]


/-- A decision state is reached from an idle state by activating its actor,
which changes neither the application state nor any recall. -/
theorem decision_predecessor {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {state : (application setup leaks).ProtocolState}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      state)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (current : state = some ⟨remaining, some who, execution⟩) :
    ∃ previous : (application setup leaks).Execution,
      Nonempty (((application setup leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some ⟨remaining + 1, none, previous⟩)) ∧
      previous.application = execution.application ∧ previous.recall = execution.recall := by
  match state, trace, current with
  | _, .start, current => cases current
  | _, .extend (source := before) prior joint _ realized, current =>
      subst current
      cases before with
      | none =>
          obtain ⟨_, _, same⟩ := PMF.support_map .. ▸ realized
          cases same
      | some control =>
          rcases control with ⟨priorRemaining, actor, priorExecution⟩
          cases actor with
          | some responder => cases (PMF.mem_support_pure_iff _ _).mp realized
          | none =>
              cases priorRemaining with
              | zero => cases (PMF.mem_support_pure_iff _ _).mp realized
              | succ priorRemaining =>
                  obtain ⟨command, _, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ realized)
                  obtain ⟨next, supported, same⟩ := PMF.support_map .. ▸ moved
                  cases command with
                  | activate activated =>
                      cases same
                      obtain ⟨updated, chosen, rfl⟩ := PMF.support_map .. ▸ supported
                      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ chosen
                      exact ⟨priorExecution, ⟨prior⟩, rfl, rfl⟩
                  | «include» id => cases same
                  | wait => cases same
                  | application command => cases same

section OnePacket

variable [Fintype Player] (bounds : MessageBounds (graph setup))

omit [Fintype Player] in
/-- The entry of a transmitting response records its envelope. -/
theorem respondEntry_of_transmission (execution : (application setup leaks).Execution)
    (who : Player) (response : (application setup leaks).Action)
    (material : (application setup leaks).Submission)
    (submits : response.transmission = some material) :
    respondEntry setup leaks execution who response =
      ⟨execution.observe (application setup leaks) who, response,
        some (sentEnvelope setup leaks execution who material)⟩ := by
  unfold respondEntry
  rw [submits]
  rfl

end OnePacket

end Vegas
