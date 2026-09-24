/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveSafety
import Interaction.ReactiveReceipts

/-! # Successful opening receipts authenticate immutable candidate values

An application may validate an opening and then store publication failure.
The public success receipt still certifies the opening's fixed meaning.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem handle_opening_verified (runtime : EventGraphRuntime graph)
    (state next : State graph) (id : MessageId Player) (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L)
    (accepted : handle runtime state ⟨id, .opening event candidate raw⟩ = some next) :
    state.candidates.lookup candidate = .openable raw := by
  classical
  by_contra different
  have unverified : state.candidates.verify candidate raw ≠ true := by
    intro verified
    exact different ((CommitmentCandidates.verify_eq_true_iff _ _ _).mp verified)
  cases view : nodeView graph event <;> simp [handle, view, unverified] at accepted

def Payload.Authenticates (candidate : Handle graph) (raw : Raw L)
    (packet : Payload graph) : Prop :=
  ∀ event opened, packet = .opening event candidate opened → opened = raw

theorem handle_authenticates (runtime : EventGraphRuntime graph) (state next : State graph)
    (message : Message Player (Payload graph)) (candidate : Handle graph) (raw : Raw L)
    (fixed : state.candidates.lookup candidate = .openable raw)
    (accepted : handle runtime state message = some next) :
    message.payload.Authenticates candidate raw := by
  intro event opened same
  rcases message with ⟨id, packet⟩
  cases same
  have verified := handle_opening_verified runtime state next id event candidate opened accepted
  rw [fixed] at verified
  exact (CommitmentCandidate.openable.inj verified).symm

theorem reactiveCandidateInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (candidate : Handle graph) (raw : Raw L) :
    (runtime.reactiveApplication leaks).Invariant
      (fun state => state.candidates.lookup candidate = .openable raw) where
  submit state who material fixed := by
    have stable := runtime.reactive_respond_candidate_fixed leaks
      (.initial (runtime.reactiveApplication leaks) state) who
      ⟨some (.submit material)⟩ candidate (by
        change state.candidates.lookup candidate ≠ .fresh
        rw [fixed]
        simp)
    exact stable.trans fixed
  handle state message next fixed accepted :=
    (handle_lookup_of_not_fresh runtime state next ⟨message.id, message.payload.call⟩ candidate
      (by rw [fixed]; simp) accepted).trans fixed
  environment state command next fixed supported := by
    rw [(environmentStep_tables runtime state next command supported).2]
    exact fixed

/-- Sound at every legal history, irrespective of player strategies. -/
theorem reactiveOpeningEvidence (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (candidate : Handle graph) (raw : Raw L)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    (runtime.reactiveApplication leaks).ServiceInvariant scheduler
      (fun execution => execution.application.candidates.lookup candidate = .openable raw ∧
        execution.ReceiptsSound (runtime.reactiveApplication leaks)
          (fun packet => packet.call.Authenticates candidate raw)) :=
  (runtime.reactiveApplication leaks).receiptServiceInvariant _ _
    (runtime.reactiveCandidateInvariant leaks candidate raw)
    (fun state message next fixed accepted =>
      handle_authenticates runtime state next ⟨message.id, message.payload.call⟩
        candidate raw fixed accepted) scheduler

/-- A successful receipt for this opening occurs in the observer's public ledger. -/
def openingObserved (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (candidate : Handle graph) (raw : Raw L) : Prop :=
  ∃ event id evidence, (⟨id, ⟨.opening event candidate raw, evidence⟩⟩, (id, true)) ∈
    view.messages.ledger.zip view.receipts

/-- A visible success receipt identifies the immutable meaning, independently
of the hidden history or any assessment beliefs. -/
theorem observed_opening_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (candidate : Handle graph) (fixed opened : Raw L)
    (sound : execution.ReceiptsSound (runtime.reactiveApplication leaks)
      (fun packet => packet.call.Authenticates candidate fixed))
    (observed : runtime.openingObserved leaks
      (execution.observe (runtime.reactiveApplication leaks) who) candidate opened) :
    opened = fixed := by
  obtain ⟨event, id, evidence, accepted⟩ := observed
  exact sound.certifies (runtime.reactiveApplication leaks) _ execution
    ⟨id, ⟨.opening event candidate opened, evidence⟩⟩ id accepted event opened rfl

end Vegas.EventGraphRuntime
