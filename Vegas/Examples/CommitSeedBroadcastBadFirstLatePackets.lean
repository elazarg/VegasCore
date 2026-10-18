/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperPublicPackets
import Interaction.ReactiveReceiptIdentity

/-! # The original public packet signal at the bad first-late callback -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- At the unfavorable first-late turn, the complete receipt signal is
nonempty exactly when the fixed original clock-zero packet word is nonempty.
Later pending declarations and all hidden preparations remain unrestricted. -/
theorem bad_firstLate_receipts_empty_iff_initial_packets (seed : Seeds)
    (current : app.Control) (trace : (app.protocol initial horizon (family seed)).Trace
      (some current))
    (owner : Player) (active : current.actor = some owner)
    (original : current.execution.application.attempt = originalAttempt)
    (clock : current.execution.application.current.native.clock = 2)
    (bad : seed.2 owner = false) :
    current.execution.receipts = [] ↔ initialPublicPackets current.execution = ∅ := by
  classical
  have bounded := (original_first_late_bad_iff seed current trace owner active original clock).mp
    bad
  let snapshot := current.execution.environmentRecall[3]'(by omega)
  have selected : current.execution.environmentRecall[3]? = some snapshot :=
    List.getElem?_eq_getElem (by omega)
  have ledger := bad_firstLate_ledger_packets seed current trace owner active original clock bad
    snapshot selected
  have packets : initialPublicPackets current.execution =
      current.execution.network.ledger.toFinset := by
    simp only [initialPublicPackets, selected, Option.map_some, Option.getD_some]
    exact ledger.symm
  have identifiers := app.receipt_identifiers_history initial horizon (family seed) current trace
  have emptyIff : current.execution.receipts = [] ↔ current.execution.network.ledger = [] := by
    constructor
    · intro empty
      rw [empty, List.map_nil] at identifiers
      exact List.map_eq_nil_iff.mp identifiers.symm
    · intro empty
      rw [empty, List.map_nil] at identifiers
      exact List.map_eq_nil_iff.mp identifiers
  rw [emptyIff, packets]
  constructor
  · intro empty
    rw [empty]
    rfl
  · intro empty
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro message member
    have present := List.mem_toFinset.mpr member
    rw [empty] at present
    exact Finset.notMem_empty _ present

/-- The initial public word is an immutable part of the original actual past. -/
theorem runRounds_initialPublicPackets (selected : app.Scheduler)
    (players : Player → app.Policy) (count : Nat) (before after : app.Execution)
    (past : 4 ≤ before.environmentRecall.length)
    (reached : after ∈ (app.runRounds selected players count before).support) :
    initialPublicPackets after = initialPublicPackets before := by
  obtain ⟨later, recalled, _length⟩ := app.runRounds_environmentRecall_append selected players
    count before after reached
  simp only [initialPublicPackets, recalled,
    List.getElem?_append_left (by omega : 3 < before.environmentRecall.length)]

end Vegas.Examples.CommitSeedBroadcast
