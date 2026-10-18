/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastFirstLateProvenance
import Vegas.Examples.CommitSeedBroadcastProtected
import Vegas.Examples.CommitSeedBroadcastCallbackReplay
import Vegas.Pending.PhaseAttemptCheckpoint

/-! # An empty receipt word at a bad first-late callback excludes early traffic -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem idle_original_empty_receipts_snapshot (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (app.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (original : execution.application.attempt = originalAttempt)
    (past : 11 ≤ execution.environmentRecall.length) (empty : execution.receipts = []) :
    EmptyEarlySnapshot execution := by
  intro snapshot member
  have selected : execution.environmentRecall[3]? = some snapshot := Option.mem_def.mp member
  cases inputs : snapshot.beforeView.network.inputs with
  | nil => rfl
  | cons message later =>
      have input : message ∈ snapshot.beforeView.network.inputs := by
        rw [inputs]
        exact List.mem_cons_self
      obtain ⟨entry, recalled, _material, _transmitted, emitted, attempted, _zero⟩ :=
        snapshot_packet_original_clock_zero seed remaining execution trace snapshot selected
          message.sender message input rfl
      have addressed : message.payload.attempt = originalAttempt :=
        (phase_recalled_emission_attempt runtime leaks initial horizon (family seed) trace
          message.sender entry recalled message emitted).trans attempted
      obtain ⟨accepted, received⟩ := original_snapshot_submission_receipt seed
        ⟨remaining, none, execution⟩ trace original past snapshot selected message.sender message
          input rfl addressed
      rw [empty] at received
      cases received

/-- This classification concerns every actual raw history, including either
accepting or rejecting earlier native handlers. A rejected early packet also
leaves a receipt and therefore cannot hide inside the empty-ledger case. -/
theorem original_empty_receipts_snapshot (seed : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seed)).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt)
    (past : 11 ≤ current.execution.environmentRecall.length)
    (empty : current.execution.receipts = []) : EmptyEarlySnapshot current.execution := by
  rcases current with ⟨remaining, actor, execution⟩
  cases actor with
  | none =>
      exact idle_original_empty_receipts_snapshot seed remaining execution trace original past empty
  | some owner =>
      obtain ⟨responded⟩ := app.raw_trace_respond initial horizon (family seed) remaining
        execution owner ⟨none⟩ trace
      have snapshot := idle_original_empty_receipts_snapshot seed remaining
        (execution.respond app owner ⟨none⟩) responded original
        (by simpa only [app.respond_environmentRecall] using past)
        (by simpa only [app.respond_receipts] using empty)
      simpa only [EmptyEarlySnapshot, app.respond_environmentRecall] using snapshot

/-- The bad original seed at a first-late empty-receipt input is necessarily
on the original quiet subevent. The good-seed portion can additionally contain
pre-middle helper histories and is retained in the posterior denominator. -/
theorem bad_firstLate_empty_receipts_snapshot (seed : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seed)).Trace (some current))
    (owner : Player) (active : current.actor = some owner)
    (original : current.execution.application.attempt = originalAttempt)
    (clock : current.execution.application.current.native.clock = 2)
    (bad : seed.2 owner = false) (empty : current.execution.receipts = []) :
    EmptyEarlySnapshot current.execution := by
  have past := (original_first_late_bad_iff seed current trace owner active original clock).mp bad
  exact original_empty_receipts_snapshot seed current trace original (by omega) empty

end Vegas.Examples.CommitSeedBroadcast
