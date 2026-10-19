/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSwapInformation
import Interaction.ReactiveRoundTrace

/-! # Literal evidence aliases under foreign candidate substitution

An actor's unavailable requests stay literal. A raw certificate request for
another owner's changed handle cannot test that handle; no syntactic fixedness
condition is imposed on the requested foreign plaintext.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Fixing the sender's own raw handle maps suffices to preserve every actual
emitted certificate. Inert aliases referring to a changed foreign handle are
retained exactly, rather than normalized or removed. -/
theorem WitnessedSubmission.emit_swap_of_own_handles
    (swap : HiddenSwap graph) (submission : WitnessedSubmission graph)
    (state : State graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph)))
    (handles : ∀ slot, swap.raw (who, slot) = id) :
    (submission.swap swap).emit (state.swap swap) who known = submission.emit state who known := by
  cases evidence : submission.evidence with
  | none =>
      apply submission.emit_swap swap state who known
      simp only [evidence, EvidenceRequest.FixedBy]
  | forward id =>
      apply submission.emit_swap swap state who known
      simp only [evidence, EvidenceRequest.FixedBy]
  | owned fact =>
      by_cases owned : fact.handle.1 = who
      · apply submission.emit_swap swap state who known
        have named : fact.handle = (who, fact.handle.2) := Prod.ext owned rfl
        simp only [evidence, EvidenceRequest.FixedBy]
        rw [named, handles]
        rfl
      · simp only [WitnessedSubmission.emit, WitnessedSubmission.swap, evidence,
          Submission.swap_packet, State.swap_publicView, owned, false_and, ↓reduceIte]

/-- The phase-tagged wire packet, namespace token and evidence remain the
same for every literal request when only foreign candidate meanings change. -/
theorem PhaseRuntimeState.emit_swap_of_own_handles
    (swap : HiddenSwap graph) (state : PhaseRuntimeState graph) (who : Player)
    (known : List (Message Player (CommitAttemptPacket graph)))
    (submission : WitnessedSubmission graph)
    (handles : ∀ slot, swap.raw (who, slot) = id) :
    (state.swap swap).emit who known (submission.swap swap) = state.emit who known submission := by
  unfold PhaseRuntimeState.emit RecoveryState.emit
  simp only [PhaseRuntimeState.swap_current, RecoveryState.swap_native]
  rw [WitnessedSubmission.emit_swap_of_own_handles swap submission state.current.native who _
    handles]
  rfl


namespace HiddenSwap

variable {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

/-- Whole physical response replay needs only unchanged own handle maps,
not fixed syntax for each unavailable certificate request. -/
theorem respond_phaseExecution_of_own_handles (swap : HiddenSwap graph)
    (current : (phaseApplication runtime leaks).Execution) (who : Player)
    (response : (phaseApplication runtime leaks).Action)
    (handles : ∀ slot, swap.raw (who, slot) = id) :
    (swap.phaseExecution current).respond (phaseApplication runtime leaks) who
        (swap.phaseAction response) =
      swap.phaseExecution (current.respond (phaseApplication runtime leaks) who response) := by
  apply swap.respond_phaseExecution current who response
  intro submission _sent
  exact PhaseRuntimeState.emit_swap_of_own_handles swap
    (current.application.submit who submission) who (current.network.known who) submission handles

/-- An actual counted foreign response is retained literally, including its
private preparation and inert evidence aliases, under a change confined to
another owner's prepared candidate. -/
theorem respond_phaseExecution_of_onePacket [Fintype Player] (swap : HiddenSwap graph)
    (bounds : MessageBounds graph)
    (current : (phaseApplication runtime leaks).Execution) (who : Player)
    (response : (phaseApplication runtime leaks).Action)
    (handles : ∀ slot, swap.raw (who, slot) = id)
    (offered : response ∈ PhaseCount.onePacketActions runtime leaks bounds who
      (current.recall who) (current.observe (phaseApplication runtime leaks) who)) :
    (swap.phaseExecution current).respond (phaseApplication runtime leaks) who response =
      swap.phaseExecution (current.respond (phaseApplication runtime leaks) who response) := by
  have exactAction := swap.phaseAction_eq_of_onePacket bounds who handles _ _ response offered
  simpa only [exactAction] using swap.respond_phaseExecution_of_own_handles current who response
    handles

/-- The literal foreign response constructs a real counted target extension.
The input equality follows from actual observer readback; it is not supplied
as a desired policy or response-law equality. -/
theorem phase_respond_trace_of_own_handles [Fintype Player] (swap : HiddenSwap graph)
    (bounds : MessageBounds graph) (initial : PMF (phaseApplication runtime leaks).State)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (remaining : Nat) (who : Player) (current : (phaseApplication runtime leaks).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some ⟨remaining, some who, current⟩))
    (imageTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some ⟨remaining, some who, swap.phaseExecution current⟩))
    (fields : ∀ field, graph.fieldVisibleTo who field → swap.values.value field = id)
    (actions : ∀ event, graph.actor? event = some who → swap.values.action event = id)
    (handles : ∀ slot, swap.raw (who, slot) = id)
    (response : (phaseApplication runtime leaks).Action)
    (offered : response ∈ PhaseCount.onePacketActions runtime leaks bounds who
      (current.recall who) (current.observe (phaseApplication runtime leaks) who)) :
    Nonempty (((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).Trace (some ⟨remaining, none,
        swap.phaseExecution (current.respond (phaseApplication runtime leaks) who response)⟩)) := by
  have input := swap.phaseInput_eq_of_fixed bounds initial horizon scheduler
    ⟨remaining, some who, current⟩ trace who fields actions handles
  have remembered : (swap.phaseExecution current).recall who = current.recall who :=
    congrArg Prod.fst input
  have observed : (swap.phaseExecution current).observe (phaseApplication runtime leaks) who =
      current.observe (phaseApplication runtime leaks) who := congrArg Prod.snd input
  have targetLegal : response ∈ PhaseCount.onePacketActions runtime leaks bounds who
      ((swap.phaseExecution current).recall who)
      ((swap.phaseExecution current).observe (phaseApplication runtime leaks) who) := by
    rw [remembered, observed]
    exact offered
  have target := (PhaseCount.onePacketMenu runtime leaks bounds).trace_respond initial horizon
    scheduler remaining (swap.phaseExecution current) who response imageTrace targetLegal
  rw [swap.respond_phaseExecution_of_onePacket bounds current who response handles offered]
    at target
  exact target

end HiddenSwap

end Vegas.EventGraphRuntime
