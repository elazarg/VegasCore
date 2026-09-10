/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedPolicyPrivacy
import Interaction.MessageApplicationNoDelivery

/-! # Foreign replay locality for canonical no-delivery executions -/

noncomputable section

namespace Vegas.WindowedApplication

open Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Foreign public packets are safe to replay when the current ordered handler
rejects them. Ledger membership alone is deliberately not included: a packet
may have been rejected as premature and become active later. -/
def ForeignLedgerInert (runtime : WindowedApplication P L) (who : P)
    (state : runtime.application.State) : Prop :=
  ∀ message ∈ state.pool.ledger, message.sender ≠ who →
    runtime.handle state.application message = none

/-- In a no-delivery execution, a foreign packet known to the broadcaster is
public. If foreign public packets are inert on both related sides, including a
replayed copy preserves the focal policy agreement, including ledger and
rejection receipt equality. -/
theorem PolicyAgreement.include_foreign_known
    (runtime : WindowedApplication P L) (who : P)
    {left right : runtime.application.PolicyExecution}
    (h : PolicyAgreement runtime who left right)
    (hleftProvenance : left.native.pool.NoDeliveryProvenance)
    (hleftInert : runtime.ForeignLedgerInert who left.native)
    (hrightInert : runtime.ForeignLedgerInert who right.native)
    (id : MessageId P) (message : Message P (ApplicationImage.Payload P L))
    (hknown : (left.native.pool.observe who).known? id = some message)
    (hforeign : message.sender ≠ who)
    (hlookup : left.native.pool.lookup id = some message) :
    PolicyAgreement runtime who
      { left with native := runtime.application.includePending left.native id }
      { right with native := runtime.application.includePending right.native id } := by
  have hledger : message ∈ left.native.pool.ledger :=
    hleftProvenance.known_foreign_mem_ledger who id message hknown hforeign
  have hrightLookup : right.native.pool.lookup id = some message := h.pool ▸ hlookup
  have hrightLedger : message ∈ right.native.pool.ledger := h.pool ▸ hledger
  have hleftReject := hleftInert message hledger hforeign
  have hrightReject := hrightInert message hrightLedger hforeign
  rw [MessageApplication.includePending_reject _ _ _ _ hlookup hleftReject,
    MessageApplication.includePending_reject _ _ _ _ hrightLookup hrightReject]
  exact ⟨h.state, by rw [h.pool], by rw [h.pool, h.receipts], h.history⟩

end Vegas.WindowedApplication
