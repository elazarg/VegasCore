/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingInclusionMemory

/-! # Actual all-value responses with evolving private catalogue memory -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Repeated nonmissing same-slot responses reconstruct complete saved and live
states with the updated catalogue memory. All prior remembered values remain;
the full emitted envelope, network and nonowner response words are identical. -/
theorem respond_binding_memory (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner) (left right : (app).Execution)
    (application : left.application = memory.phased owner right.application)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (archive : right.application.retired = [])
    (event : graph.EventId) (payload : L.Ty)
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
      first.application = remembered.phased owner second.application ∧
      first.network = second.network ∧ first.receipts = second.receipts ∧
      first.environmentRecall = second.environmentRecall ∧
      (∀ who, who ≠ owner → first.recall who = second.recall who) := by
  classical
  intro first second remembered
  let material (result : PublicationResult (L.Val payload)) : WitnessedSubmission graph :=
    ⟨⟨.commitment event (owner, .prepared serial), match result with
      | .failure => none
      | .success value => some ⟨payload, value⟩⟩, .none⟩
  have prepared := binding_preparation_memory memory right.application.current.native owner event
    serial (material firstResult).call.opening (material secondResult).call.opening fresh
  have firstNative : first.application.current.native =
      submitStep ((material firstResult).call.register left.application.current.native owner)
        owner (material firstResult).call.packet := rfl
  have saved := rememberCandidate_native_fresh memory right.application.entry.native owner
    (.prepared serial)
      (first.application.current.native.candidates.lookup (owner, .prepared serial)) savedFresh
  have reconstructed : remembered.phased owner second.application = first.application := by
    change remembered.phased owner (right.application.submit owner (material secondResult)) =
      left.application.submit owner (material firstResult)
    rw [application]
    change (⟨right.application.phases, right.application.generation,
      remembered.recovery owner right.application.entry,
      remembered.recovery owner (right.application.current.submit owner (material secondResult)),
      right.application.retired.map fun prior =>
        ⟨prior.attempt, remembered.native owner prior.state⟩⟩ : PhaseRuntimeState graph) = _
    have prepared' : remembered.native owner
        (right.application.current.submit owner (material secondResult)).native =
      ((memory.recovery owner right.application.current).submit owner
        (material firstResult)).native := by
      dsimp only [remembered]
      rw [firstNative, application]
      exact prepared
    dsimp only [PhaseRuntimeState.submit, phased, recovery]
    rw [saved, prepared', archive]
    rfl
  have publics : left.application.publicView = right.application.publicView := by
    rw [application]
    exact phased_publicView owned _
  have nativePublic : left.application.current.native.publicView =
      right.application.current.native.publicView := by
    rw [application]
    exact native_publicView owned _
  have attempts := congrArg PhasePublicView.attempt publics
  change left.application.attempt = right.application.attempt at attempts
  have emitted : (left.application.submit owner (material firstResult)).emit owner
        (left.network.known owner) (material firstResult) =
      (right.application.submit owner (material secondResult)).emit owner
        (right.network.known owner) (material secondResult) := by
    rw [PhaseCount.emit_after_submit, PhaseCount.emit_after_submit]
    simp only [material, EvidenceRequest.resolve]
    rw [publics, nativePublic, attempts]
  refine ⟨owned.rememberCandidate _ _, reconstructed.symm, ?_, ?_, ?_, ?_⟩
  · change (left.network.submit owner
        ((left.application.submit owner (material firstResult)).emit owner
          (left.network.known owner) (material firstResult))).2 =
      (right.network.submit owner
        ((right.application.submit owner (material secondResult)).emit owner
          (right.network.known owner) (material secondResult))).2
    rw [emitted, network]
  · exact receipts
  · exact service
  · intro who different
    exact ((app).respond_recall_other left owner who different _).trans
      ((recalled who different).trans ((app).respond_recall_other right owner who different _).symm)

end Vegas.EventGraphRuntime.BindingShadow
