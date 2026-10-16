/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingMemoryFreshness
import Vegas.Game.PhaseTimingPools

/-! # Literal operational timing data under actual binding memory reconstruction -/

noncomputable section

namespace Vegas

open EventGraph EventGraphRuntime Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The owner observes the same physical fresh slots after all-value
reconstruction. Private candidate meanings and accepted failures may differ. -/
theorem phaseOperationalView_memory (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (left right : (app).Execution)
    (application : left.application = memory.phased owner right.application)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts) :
    phaseOperationalView runtime leaks (left.observe app owner) =
      phaseOperationalView runtime leaks (right.observe app owner) := by
  change (⟨left.application.publicView, left.network.observe owner, left.receipts,
      fun slot => match left.application.current.native.candidates.lookup (owner, slot) with
        | .fresh => true | _ => false⟩ : PhaseOperationalView graph) =
    ⟨right.application.publicView, right.network.observe owner, right.receipts,
      fun slot => match right.application.current.native.candidates.lookup (owner, slot) with
        | .fresh => true | _ => false⟩
  rw [network, receipts, application, BindingShadow.phased_publicView owned]
  congr 1
  funext slot
  simp only [BindingShadow.phased, BindingShadow.recovery, BindingShadow.native,
    CommitmentCandidates.lookup, ↓reduceIte]
  change (match memory.candidate slot
      (right.application.current.native.candidates.lookup (owner, slot)) with
    | .fresh => true | _ => false) =
      (match right.application.current.native.candidates.lookup (owner, slot) with
        | .fresh => true | _ => false)
  have iffFresh := memory.candidate_fresh_iff valid slot
    (right.application.current.native.candidates.lookup (owner, slot))
  cases before : right.application.current.native.candidates.lookup (owner, slot) <;>
    cases after : memory.candidate slot _ <;> simp_all

/-- The operational candidate constraint is derived after the genuine physical
response; no independent freshness-preservation premise is imposed on its update. -/
theorem phaseBindingResponse_memory_candidates_not_fresh (memory : BindingShadow graph)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (execution : (app).Execution) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat) :
    let after := execution.respond app owner
      (phaseBindingResponse runtime leaks owner event payload result serial)
    ∀ slot, (memory.rememberCandidate (.prepared serial)
      (after.application.current.native.candidates.lookup (owner, .prepared serial))).candidates
        slot ≠ some .fresh := by
  intro after
  exact memory.rememberCandidate_candidates_not_fresh valid _ _
    (BindingShadow.response_candidate_not_fresh runtime leaks execution owner event payload
      result serial)

end Vegas
