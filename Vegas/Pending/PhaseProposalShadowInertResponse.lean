/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalShadowForeignResponse
import Vegas.Pending.PhaseBindingInertResponse

/-! # Counted inert responses through general phase recovery shadows -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A counted inert response retains its literal raw syntax. Its actual
emitted packet, reconstructed output word and signed serial give target menu
membership without equating the repairing owner's private observations. -/
theorem respond_inert_external (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner) (left right : (app).Execution)
    (frame : PhaseStateFrame memory owner left.application right.application)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (bounds : MessageBounds graph)
    (leftRecall : PhaseCount.CountRecall runtime leaks left)
    (rightRecall : PhaseCount.CountRecall runtime leaks right)
    (material : WitnessedSubmission graph)
    (leftInert : (left.respond app owner ⟨some material⟩).application = left.application)
    (rightInert : (right.respond app owner ⟨some material⟩).application = right.application)
    (emitted : left.application.emit owner (left.network.known owner) material =
      right.application.emit owner (right.network.known owner) material)
    (member : (⟨some material⟩ : (app).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds owner (left.recall owner)
        (left.observe app owner)) :
    let first := left.respond app owner ⟨some material⟩
    let second := right.respond app owner ⟨some material⟩
    (⟨some material⟩ : (app).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds owner (right.recall owner)
        (right.observe app owner) ∧
      PhaseStateFrame memory owner first.application second.application ∧
      first.network = second.network ∧
      phaseExternalObservation runtime leaks owner first =
        phaseExternalObservation runtime leaks owner second := by
  classical
  intro first second
  have packets : (app).packet ((app).submit left.application owner material) owner
      (left.network.known owner) material =
      (app).packet ((app).submit right.application owner material) owner
        (right.network.known owner) material := by
    change (left.respond app owner ⟨some material⟩).application.emit owner
        (left.network.known owner) material =
      (right.respond app owner ⟨some material⟩).application.emit owner
        (right.network.known owner) material
    rw [leftInert, rightInert]
    exact emitted
  have envelopes : PhaseCount.localEnvelope runtime leaks owner (left.recall owner)
      (left.observe app owner) material =
      PhaseCount.localEnvelope runtime leaks owner (right.recall owner)
        (right.observe app owner) material := by
    rw [PhaseCount.localEnvelope_eq_of_recall runtime leaks left leftRecall.1 leftRecall.2.1,
      PhaseCount.localEnvelope_eq_of_recall runtime leaks right rightRecall.1 rightRecall.2.1,
      packets]
    exact congrArg (fun serial =>
      (⟨(owner, serial), (app).packet ((app).submit right.application owner material) owner
        (right.network.known owner) material⟩ : Message Player (CommitAttemptPacket graph)))
      (congrArg (fun pool : MessageNetwork Player (CommitAttemptPacket graph) =>
        pool.nextSerial owner) network)
  have legal := (PhaseBindingRepair.inert_response_menu_iff network bounds leftRecall
    rightRecall material envelopes).mp member
  have nextNetwork : first.network = second.network := by
    change (left.network.submit owner _).2 = (right.network.submit owner _).2
    rw [packets, network]
  have nextFrame : PhaseStateFrame memory owner first.application second.application := by
    rw [leftInert, rightInert]
    exact frame
  refine ⟨legal, nextFrame, nextNetwork, ?_⟩
  apply phaseExternalObservation_congr runtime leaks first second owner nextNetwork receipts service
    (nextFrame.publicView owned) (nextFrame.playerView_other owned)
  intro who different
  rw [(app).respond_recall_other left owner who different,
    (app).respond_recall_other right owner who different]
  exact recalled who different

end Vegas.EventGraphRuntime.BindingShadow
