/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedPolicyPrivacy
import Interaction.MessageInvariant

/-! # Foreign replay locality at completed source checkpoints -/

noncomputable section

namespace Vegas.WindowedApplication

open Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Every foreign packet known to any observer is inert at the current handler.
This includes sent, delivered, and publicly included copies. -/
def ForeignKnownInert (runtime : WindowedApplication P L) (who : P)
    (state : runtime.application.State) : Prop :=
  ∀ observer id message, (state.pool.observe observer).known? id = some message →
    message.sender ≠ who →
    runtime.handle state.application message = none

/-- If foreign known packets are inert on both related sides, including a
replayed copy preserves focal policy agreement, including the public ledger and
rejection receipt. No empty-inbox or prior-inclusion premise is required. -/
theorem PolicyAgreement.include_foreign_known
    (runtime : WindowedApplication P L) (who : P)
    {left right : runtime.application.PolicyExecution}
    (h : PolicyAgreement runtime who left right)
    (hleftInert : runtime.ForeignKnownInert who left.native)
    (hrightInert : runtime.ForeignKnownInert who right.native)
    (id : MessageId P) (message : Message P (ApplicationImage.Payload P L))
    (hknown : (left.native.pool.observe who).known? id = some message)
    (hforeign : message.sender ≠ who)
    (hlookup : left.native.pool.lookup id = some message) :
    PolicyAgreement runtime who
      { left with native := runtime.application.includePending left.native id }
      { right with native := runtime.application.includePending right.native id } := by
  have hrightLookup : right.native.pool.lookup id = some message := h.pool ▸ hlookup
  have hrightKnown : (right.native.pool.observe who).known? id = some message := h.pool ▸ hknown
  have hleftReject := hleftInert who id message hknown hforeign
  have hrightReject := hrightInert who id message hrightKnown hforeign
  rw [MessageApplication.includePending_reject _ _ _ _ hlookup hleftReject,
    MessageApplication.includePending_reject _ _ _ _ hrightLookup hrightReject]
  exact ⟨h.state, by rw [h.pool], by rw [h.pool, h.receipts], h.history⟩

end Vegas.WindowedApplication
