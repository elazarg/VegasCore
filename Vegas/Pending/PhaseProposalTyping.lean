/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalObservation
import Vegas.Pending.PhaseCountUniqueness
import Vegas.Pending.PhaseCountMenu
import Vegas.Pending.ReactiveCountedSurvivor

/-! # Every counted opening proposal has its publication field's type

The signed content verdict supplies this property even for an old, rejected or
still-pending packet. It does not require the event to remain ready or the
packet's physical attempt to remain current.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Typed wire proposals cannot be dropped by publication-type decoding on a
counted history. The verdict alone gives the matching declared field type. -/
theorem permitted_proposal_typed
    (traffic : List (Message Player (CommitAttemptPacket graph)))
    (message : Message Player (CommitAttemptPacket graph))
    (allowed : PhaseCount.Permits traffic message)
    (coordinate : CommitAttemptEvent graph) (raw : Raw L)
    (proposed : packetProposal? message.payload = some (coordinate, raw)) :
    ∃ (payload : L.Ty) (value : L.Val payload),
      graph.outputLayout coordinate.event = .publication payload ∧ raw = ⟨payload, value⟩ := by
  obtain ⟨_, candidate, call⟩ := opening_of_packetProposal message.payload coordinate raw proposed
  have correct := allowed.2.1
  unfold CountCallCorrect at correct
  dsimp only [PhaseCount.nativeMessage] at correct
  rw [call] at correct
  have resolves := correct.2
  cases node : nodeView graph coordinate.event with
  | bind owner payload outputEq codeEq =>
      rw [node] at resolves
      exact resolves.elim
  | sample payload law outputEq codeEq =>
      rw [node] at resolves
      exact resolves.elim
  | resolve owner payload binding checks outputEq codeEq =>
      rw [node] at resolves
      rcases raw with ⟨ty, value⟩
      have typed : ty = payload := resolves.2.1
      subst ty
      exact ⟨payload, value, outputEq, rfl⟩

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every member of the actual counted submitted archive is a typed opening
for its declared publication, independently of acceptance and retirement. -/
theorem archive_publication_typed [Fintype Player] (bounds : MessageBounds graph)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      initial horizon scheduler).Trace (some control))
    (coordinate : CommitAttemptEvent graph) (raw : Raw L)
    (member : (coordinate, raw) ∈ archive control.execution.network.inputs) :
    ∃ (payload : L.Ty) (value : L.Val payload),
      graph.outputLayout coordinate.event = .publication payload ∧ raw = ⟨payload, value⟩ := by
  obtain ⟨message, submitted, proposed⟩ := (mem_archive _ _).mp member
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  exact permitted_proposal_typed control.execution.network.inputs message
    ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message submitted)) coordinate raw proposed

end Vegas.EventGraphRuntime.PhaseProposal
