/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCertificateField
import Vegas.Game.OnePacketSwapGuard

/-! # Accepted handles of the one-packet game are injective

Along every history of the one-packet game, no handle is accepted at two
fields (`Vegas.acceptedInjective_of_trace`). A handle accepted for an initial
binding input is that input's fixed initial handle, so distinct inputs accept
distinct handles. A handle accepted for a binding event was named by a
commitment of its owner, so it is a prepared handle, never an initial one, and
two commitments never name one handle for two events.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  (bounds : MessageBounds (graph setup))

/-- **Accepted handles are injective.** Along every history of the one-packet
game, the table of accepted handles never accepts one handle at two fields. -/
theorem acceptedInjective_of_trace {horizon : Nat}
    {scheduler : (application setup runtime leaks).Scheduler}
    {control : (application setup runtime leaks).Control}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some
      control)) :
    AcceptedInjective control.execution.application.accepted := by
  have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have signed := signedCommitments_history runtime leaks (initialLaw setup)
    (serviceInitialLaw_initialized setup) horizon scheduler rawTrace
  have prepared (event : (graph setup).EventId) (handle : Handle (graph setup))
      (accepted : control.execution.application.accepted (.inr event) = some handle) :
      ∃ committed ∈ control.execution.network.inputs,
        committed.payload.call = .commitment event handle ∧
          ∃ serial, handle.2 = .prepared serial := by
    obtain ⟨committed, output, call⟩ := signed.acceptedSigned event handle accepted
    have input := output_mem_inputs_of_trace (runtime := runtime) bounds trace _ committed output
    obtain ⟨_, serial, _⟩ :=
      commitment_facts_of_trace (runtime := runtime) bounds trace committed input event handle call
    exact ⟨committed, input, call, serial⟩
  intro left right handle leftAccepted rightAccepted
  cases left with
  | inl leftInput =>
      have leftInitial := signed.inputHandles leftInput handle leftAccepted
      cases right with
      | inl rightInput =>
          have rightInitial := signed.inputHandles rightInput handle rightAccepted
          rw [leftInitial] at rightInitial
          cases rightInitial
          rfl
      | inr rightEvent =>
          obtain ⟨_, _, _, serial, rightPrepared⟩ := prepared rightEvent handle rightAccepted
          rw [leftInitial] at rightPrepared
          cases rightPrepared
  | inr leftEvent =>
      obtain ⟨leftCommitted, leftInput, leftCall, serial, leftPrepared⟩ :=
        prepared leftEvent handle leftAccepted
      cases right with
      | inl rightInput =>
          have rightInitial := signed.inputHandles rightInput handle rightAccepted
          rw [leftPrepared] at rightInitial
          cases rightInitial
      | inr rightEvent =>
          obtain ⟨rightCommitted, rightInput, rightCall, _⟩ :=
            prepared rightEvent handle rightAccepted
          rw [commitment_unique_of_trace (runtime := runtime) bounds trace leftCommitted leftInput
            rightCommitted
            rightInput leftEvent rightEvent handle leftCall rightCall]

end Vegas
