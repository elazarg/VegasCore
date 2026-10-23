/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochScheduler

/-! # Physical packet processing at a reserved epoch

These laws concern actual pending envelopes and actual receipt entries. They
make no correctness assumption about the packet or its application result.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem include_head (execution : (app).Execution)
    (message : Message Player (app).Payload)
    (rest : List (Message Player (app).Payload))
    (pending : execution.network.pending = message :: rest) :
    (execution.includePending app message.id).network.pending = rest ∧
      (execution.includePending app message.id).network.ledger =
        execution.network.ledger ++ [message] ∧
      (execution.includePending app message.id).receipts =
        execution.receipts ++
          [(message.id, ((app).handle execution.application message).isSome)] := by
  have found : execution.network.lookup message.id = some message := by
    simp [MessageNetwork.lookup, pending]
  simp [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    found, pending, MessagePool.removeFirst]

theorem process_dispatch (players : Player → (app).Policy) (execution : (app).Execution)
    (message : Message Player (app).Payload)
    (rest : List (Message Player (app).Payload))
    (pending : execution.network.pending = message :: rest) :
    (app).dispatch players (process runtime leaks (execution.observeEnvironment app)) execution =
      PMF.pure { execution.includePending app message.id with
        environmentRecall := execution.environmentRecall ++
          [⟨execution.observeEnvironment app, .include message.id⟩] } := by
  have selected := processing_head runtime leaks (execution.observeEnvironment app)
    message rest pending
  rw [selected]
  simp [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume]

/-- A processing step creates no further traffic and preserves every own recall. -/
theorem process_step (players : Player → (app).Policy) (execution next : (app).Execution)
    (message : Message Player (app).Payload)
    (rest : List (Message Player (app).Payload))
    (pending : execution.network.pending = message :: rest)
    (reached : next ∈ ((app).dispatch players
      (process runtime leaks (execution.observeEnvironment app)) execution).support) :
    next.network.pending = rest ∧ next.network.ledger = execution.network.ledger ++ [message] ∧
      (∃ accepted, (message.id, accepted) ∈ next.receipts) ∧
      next.recall = execution.recall ∧
      next.environmentRecall.length = execution.environmentRecall.length + 1 := by
  rw [process_dispatch runtime leaks players execution message rest pending] at reached
  cases (PMF.mem_support_pure_iff _ _).mp reached
  have physical := include_head runtime leaks execution message rest pending
  refine ⟨physical.1, physical.2.1, ?_, ?_, ?_⟩
  · refine ⟨((app).handle execution.application message).isSome, ?_⟩
    rw [physical.2.2]
    simp
  · have found : execution.network.lookup message.id = some message := by
      simp [MessageNetwork.lookup, pending]
    simp [ReactiveApplication.Execution.includePending, MessageNetwork.includePending, found]
  · simp

end Vegas.EventGraphRuntime.ReservedEpoch
