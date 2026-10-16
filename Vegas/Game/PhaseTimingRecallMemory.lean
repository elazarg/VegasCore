/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingBindingKey

/-! # The actual operational response word under all-value binding reconstruction -/

noncomputable section

namespace Vegas

open EventGraph EventGraphRuntime Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Equal actual before observations and physical emission ledgers preserve
one chronological operational record, even when its private raw actions differ.
The ledger equality is supplied by the actual coupled response step. -/
theorem phaseOperationalRecall_response
    (left right : (app).Execution) (owner : Player) (first second : (app).Action)
    (network : left.network = right.network)
    (past : (left.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
      (right.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)))
    (current : phaseOperationalView runtime leaks (left.observe app owner) =
      phaseOperationalView runtime leaks (right.observe app owner))
    (moved : (left.respond app owner first).network = (right.respond app owner second).network) :
    ((left.respond app owner first).recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
      ((right.respond app owner second).recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) := by
  classical
  rcases first with ⟨first⟩
  rcases second with ⟨second⟩
  cases first with
  | none =>
      cases second with
      | none =>
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.map_append,
            List.map_cons, List.map_nil]
          rw [past, current]
      | some material =>
          have sizes := congrArg (fun pool => pool.inputs.length) moved
          have oldSizes := congrArg (fun pool => pool.inputs.length) network
          simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit,
            List.length_append, List.length_singleton] at sizes
          omega
  | some firstMaterial =>
      cases second with
      | none =>
          have sizes := congrArg (fun pool => pool.inputs.length) moved
          have oldSizes := congrArg (fun pool => pool.inputs.length) network
          simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit,
            List.length_append, List.length_singleton] at sizes
          omega
      | some secondMaterial =>
          have ledger := congrArg MessageNetwork.inputs moved
          simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit] at ledger
          rw [congrArg MessageNetwork.inputs network] at ledger
          have emitted := (List.cons.inj (List.append_cancel_left ledger)).1
          simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit, ↓reduceIte,
            List.map_append, List.map_cons, List.map_nil]
          rw [past, current, emitted]

/-- A genuine same-slot response derives the next complete physical memory and
its whole operational own word. Both arbitrary typed results, including failure,
are retained privately, while the literal signed emission is identical. -/
theorem phaseTimingRecall_binding_memory (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (left right : (app).Execution)
    (application : left.application = memory.phased owner right.application)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (past : (left.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
      (right.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)))
    (archive : right.application.retired = []) (event : graph.EventId) (payload : L.Ty)
    (firstResult secondResult : PublicationResult (L.Val payload)) (serial : Nat)
    (fresh : right.application.current.native.candidates.lookup (owner, .prepared serial) = .fresh)
    (savedFresh : right.application.entry.native.candidates.lookup (owner, .prepared serial) =
      .fresh) :
    let first := left.respond app owner
      (phaseBindingResponse runtime leaks owner event payload firstResult serial)
    let second := right.respond app owner
      (phaseBindingResponse runtime leaks owner event payload secondResult serial)
    let remembered := memory.rememberCandidate (.prepared serial)
      (first.application.current.native.candidates.lookup (owner, .prepared serial))
    remembered.OwnBindings owner ∧
      (∀ slot, remembered.candidates slot ≠ some .fresh) ∧
      first.application = remembered.phased owner second.application ∧
      first.network = second.network ∧ first.receipts = second.receipts ∧
      first.environmentRecall = second.environmentRecall ∧
      (∀ who, who ≠ owner → first.recall who = second.recall who) ∧
      (first.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
      (second.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) := by
  classical
  intro first second remembered
  obtain ⟨nextOwned, nextState, nextNetwork, nextReceipts, nextService, nextRecall⟩ :=
    BindingShadow.respond_binding_memory runtime leaks memory owner owned left right application
      network receipts
      service recalled archive event payload firstResult secondResult serial fresh savedFresh
  have nextValid : ∀ slot, remembered.candidates slot ≠ some .fresh :=
    phaseBindingResponse_memory_candidates_not_fresh runtime leaks memory valid left owner event
      payload firstResult serial
  refine ⟨nextOwned, nextValid, nextState, nextNetwork, nextReceipts, nextService, nextRecall, ?_⟩
  exact phaseOperationalRecall_response runtime leaks left right owner _ _ network past
    (phaseOperationalView_memory runtime leaks memory owner owned valid left right application
      network receipts) nextNetwork

end Vegas
