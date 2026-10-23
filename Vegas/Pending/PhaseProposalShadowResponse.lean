/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalShadowNormalization
import Vegas.Pending.PhaseResponseNormalization

/-! # Raw preparation changes preserving the entire external input prefix

Only the repairing owner's private candidate meaning and own response change.
The submitted opaque packet, receipts, environment word and every other
owner's literal recall and current view remain equal.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Real same-slot binding responses with arbitrary private preparations,
including missing or mistyped material. Saved private catalogues need not be
rewritten, and no clear attempt or empty retired archive is required. -/
theorem respond_binding_external (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner) (left right : (app).Execution)
    (frame : PhaseStateFrame memory owner left.application right.application)
    (supported : memory.CompletedAt right.application.current.native.config)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (event : graph.EventId) (serial : Nat) (first second : Option (Raw L))
    (fresh : right.application.current.native.candidates.lookup (owner, .prepared serial) = .fresh)
    (savedFresh : right.application.entry.native.candidates.lookup (owner, .prepared serial) =
      .fresh) :
    let firstMaterial : WitnessedSubmission graph :=
      ⟨⟨.commitment event (owner, .prepared serial), first⟩, .none⟩
    let secondMaterial : WitnessedSubmission graph :=
      ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩
    let before := left.respond app owner ⟨some firstMaterial⟩
    let after := right.respond app owner ⟨some secondMaterial⟩
    let remembered := memory.rememberCandidate (.prepared serial)
      (before.application.current.native.candidates.lookup (owner, .prepared serial))
    remembered.OwnBindings owner ∧ PhaseStateFrame remembered owner
      before.application after.application ∧
      remembered.CompletedAt after.application.current.native.config ∧
      before.network = after.network ∧
      phaseExternalObservation runtime leaks owner before =
        phaseExternalObservation runtime leaks owner after := by
  classical
  intro firstMaterial secondMaterial before after remembered
  have prepared := binding_preparation_memory memory right.application.current.native owner event
    serial first second fresh
  have firstNative : before.application.current.native =
      submitStep (firstMaterial.call.register left.application.current.native owner) owner
        firstMaterial.call.packet := rfl
  have current : before.application.current = remembered.recovery owner
      after.application.current := by
    have native : remembered.native owner after.application.current.native =
        before.application.current.native := by
      dsimp only [remembered]
      rw [firstNative, frame.current]
      exact prepared
    change (⟨before.application.current.native, left.application.current.excluded⟩ :
      RecoveryState graph) = ⟨remembered.native owner after.application.current.native,
        right.application.current.excluded⟩
    rw [native, frame.current]
    rfl
  have saved := rememberCandidate_native_fresh memory right.application.entry.native owner
    (.prepared serial) (before.application.current.native.candidates.lookup
      (owner, .prepared serial)) savedFresh
  have nextOwned : remembered.OwnBindings owner := owned.rememberCandidate _ _
  have nextFrame : PhaseStateFrame remembered owner before.application after.application := by
    refine ⟨frame.phases, frame.generation, ?_, current, frame.retired⟩
    exact frame.entry.trans (congrArg (fun native =>
      RecoveryState.mk native right.application.entry.excluded) saved).symm
  have nextSupported : remembered.CompletedAt after.application.current.native.config := by
    change memory.CompletedAt
      (submitStep (secondMaterial.call.register right.application.current.native owner) owner
        secondMaterial.call.packet).config
    rw [submitStep_config, (secondMaterial.call.register_facts owner _).1]
    exact supported
  have publicEq := frame.publicView owned
  have nativePublic : left.application.current.native.publicView =
      right.application.current.native.publicView := by
    rw [frame.current]
    exact native_publicView owned _
  have attempts : left.application.attempt = right.application.attempt :=
    congrArg PhasePublicView.attempt publicEq
  have emitted : (left.application.submit owner firstMaterial).emit owner
      (left.network.known owner) firstMaterial =
      (right.application.submit owner secondMaterial).emit owner
        (right.network.known owner) secondMaterial := by
    rw [PhaseCount.emit_after_submit, PhaseCount.emit_after_submit]
    simp only [firstMaterial, secondMaterial, EvidenceRequest.resolve]
    rw [publicEq, nativePublic, attempts]
  have nextNetwork : before.network = after.network := by
    change (left.network.submit owner
      ((left.application.submit owner firstMaterial).emit owner
        (left.network.known owner) firstMaterial)).2 =
      (right.network.submit owner
        ((right.application.submit owner secondMaterial).emit owner
          (right.network.known owner) secondMaterial)).2
    rw [emitted, network]
  have nextReceipts : before.receipts = after.receipts := receipts
  have nextService : before.environmentRecall = after.environmentRecall := service
  have nextRecall (who : Player) (different : who ≠ owner) : before.recall who =
      after.recall who :=
    ((app).respond_recall_other left owner who different _).trans
      ((recalled who different).trans ((app).respond_recall_other right owner who different _).symm)
  refine ⟨nextOwned, nextFrame, nextSupported, nextNetwork, ?_⟩
  exact phaseExternalObservation_congr runtime leaks before after owner nextNetwork nextReceipts
    nextService (nextFrame.publicView nextOwned) (nextFrame.playerView_other nextOwned) nextRecall

variable [Fintype Player]

/-- A counted raw evidence alias is retained in its author's actual recall.
Its operational normalization supplies the same physical step; only the
repairing response uses the empty evidence request. -/
theorem respond_binding_raw_external (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner) (left right : (app).Execution)
    (frame : PhaseStateFrame memory owner left.application right.application)
    (supported : memory.CompletedAt right.application.current.native.config)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (input : left.InputRecall app) (bounds : MessageBounds graph)
    (event : graph.EventId) (serial : Nat) (first second : Option (Raw L))
    (evidence : EvidenceRequest graph)
    (freshLeft : left.application.current.native.candidates.lookup
      (owner, .prepared serial) = .fresh)
    (freshRight : right.application.current.native.candidates.lookup
      (owner, .prepared serial) = .fresh)
    (savedFresh : right.application.entry.native.candidates.lookup
      (owner, .prepared serial) = .fresh)
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), first⟩, evidence⟩⟩ :
      (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds owner
        (left.recall owner) (left.observe app owner)) :
    let source : (app).Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), first⟩, evidence⟩⟩
    let target : (app).Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩⟩
    let before := left.respond app owner source
    let after := right.respond app owner target
    let remembered := memory.rememberCandidate (.prepared serial)
      (before.application.current.native.candidates.lookup (owner, .prepared serial))
    remembered.OwnBindings owner ∧ PhaseStateFrame remembered owner
      before.application after.application ∧
      remembered.CompletedAt after.application.current.native.config ∧
      before.network = after.network ∧
      phaseExternalObservation runtime leaks owner before =
        phaseExternalObservation runtime leaks owner after := by
  classical
  let call : Submission graph := ⟨.commitment event (owner, .prepared serial), first⟩
  let material : WitnessedSubmission graph := ⟨call, evidence⟩
  let source : (app).Action := ⟨some material⟩
  let canonical : (app).Action := ⟨some ⟨call, .none⟩⟩
  have permitted : PhaseCount.permits ((app).outputs (left.recall owner))
      (PhaseCount.localEnvelope runtime leaks owner (left.recall owner)
        (left.observe app owner) material) = true := by
    rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds owner (left.recall owner)
      (left.observe app owner) source).mp member).2 with impossible | ⟨other, sent, allowed⟩
    · cases impossible
    · cases Option.some.inj sent
      exact allowed
  have normalized : (PhaseCount.normalization runtime leaks).action owner (left.recall owner)
      (left.observe app owner) source = canonical := by
    have absent := PhaseCount.normalize_binding_evidence_none runtime leaks owner
      (left.recall owner) (left.observe app owner) material event
        (owner, .prepared serial) rfl permitted
    have effective : openingEffective owner (left.observe app owner).application.1
        (.commitment event (owner, .prepared serial)) := ⟨rfl, freshLeft⟩
    have calls : ((PhaseCount.normalization runtime leaks).normalize owner
        (left.observe app owner).application
        (ReactiveApplication.ResponseMenu.knownPackets (left.recall owner)
          (left.observe app owner)) material).call = call :=
      Submission.normalizeReactive_effective _ _ _ effective
    exact congrArg (fun value => (⟨some value⟩ : (app).Action))
      (congrArg₂ WitnessedSubmission.mk calls absent)
  have effects := (PhaseCount.normalization runtime leaks).effects left owner source input
  rw [normalized] at effects
  have paired := respond_binding_external runtime leaks memory owner owned left right frame
    supported network receipts service recalled event serial first second freshRight savedFresh
  dsimp only at paired ⊢
  have sameMemory : memory.rememberCandidate (.prepared serial)
      ((left.respond app owner canonical).application.current.native.candidates.lookup
        (owner, .prepared serial)) =
      memory.rememberCandidate (.prepared serial)
        ((left.respond app owner source).application.current.native.candidates.lookup
          (owner, .prepared serial)) := by rw [effects.1]
  change _ ∧ PhaseStateFrame _ owner (left.respond app owner source).application _ ∧
    _ ∧ (left.respond app owner source).network = _ ∧ _
  rw [sameMemory] at paired
  refine ⟨paired.1, ?_, paired.2.2.1, effects.2.1.symm.trans paired.2.2.2.1, ?_⟩
  · rw [← effects.1]
    exact paired.2.1
  · have sameExternal : phaseExternalObservation runtime leaks owner
        (left.respond app owner canonical) = phaseExternalObservation runtime leaks owner
          (left.respond app owner source) :=
      phaseExternalObservation_congr runtime leaks _ _ owner effects.2.1 effects.2.2.1
        effects.2.2.2.1 (congrArg PhaseRuntimeState.publicView effects.1)
        (fun who _ => congrArg (fun state => state.playerView who) effects.1)
        effects.2.2.2.2
    exact sameExternal.symm.trans paired.2.2.2.2

end Vegas.EventGraphRuntime.BindingShadow
