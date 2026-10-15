/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingRepairedResponse
import Vegas.Pending.PhaseBindingOpeningRead

/-! # Counted inert owner responses through paired physical frontiers -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

omit [Fintype Player] in
/-- The physical authorization masks are functions of the public phase data. -/
theorem emit_mask (state : PhaseRuntimeState graph) (who : Player)
    (known : List (Message Player (CommitAttemptPacket graph)))
    (material : WitnessedSubmission graph) :
    state.emit who known material = ⟨state.attempt, PhaseCount.maskPacket state.publicView
      (material.emit state.current.native who (known.map PhaseCount.nativeMessage))⟩ := by
  unfold PhaseRuntimeState.emit RecoveryState.emit PhaseCount.maskPacket
  rw [PhaseCount.allows_publicView, PhaseCount.excludedCall_publicView]
  let packet := material.emit state.current.native who (known.map PhaseCount.nativeMessage)
  let masked := if state.current.excludedCall packet.call then { packet with token := none }
    else packet
  change (⟨state.attempt, if state.allows masked.call then masked else
    { masked with token := none }⟩ : CommitAttemptPacket graph) =
      ⟨state.attempt, if state.allows packet.call then masked else { masked with token := none }⟩
  have calls : masked.call = packet.call := by
    dsimp only [masked]
    split <;> rfl
  rw [calls]

namespace Frame

variable {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- An unchanged inert raw response preserves both semantic checkpoints and
actual foreign recall. Count support follows from the source menu, the actual
emitted packet, and the permanent physical output word. -/
theorem inert_response (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph)
    (left : PhaseCount.CountRecall runtime leaks original)
    (right : PhaseCount.CountRecall runtime leaks repaired)
    (material : WitnessedSubmission graph)
    (leftInert : (original.respond (phaseApplication runtime leaks) owner
      ⟨some material⟩).application = original.application)
    (rightInert : (repaired.respond (phaseApplication runtime leaks) owner
      ⟨some material⟩).application = repaired.application)
    (nativePacket : material.emit original.application.current.native owner
        ((original.network.known owner).map PhaseCount.nativeMessage) =
      material.emit repaired.application.current.native owner
        ((repaired.network.known owner).map PhaseCount.nativeMessage))
    (member : (⟨some material⟩ : (phaseApplication runtime leaks).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds owner (original.recall owner)
        (original.observe (phaseApplication runtime leaks) owner)) :
    let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
    let remembered := memory.record runtime (nativeLeaks (graph := graph))
      (memory.shadow.inputView runtime (nativeLeaks (graph := graph))
        ((execution runtime leaks repaired).observe nativeApp owner))
      (action runtime leaks ⟨some material⟩)
    (⟨some material⟩ : (phaseApplication runtime leaks).Action) ∈
        PhaseCount.onePacketActions runtime leaks bounds owner (repaired.recall owner)
          (repaired.observe (phaseApplication runtime leaks) owner) ∧
      Frame runtime leaks remembered owner
        (original.respond (phaseApplication runtime leaks) owner ⟨some material⟩)
        (repaired.respond (phaseApplication runtime leaks) owner ⟨some material⟩) := by
  let app := phaseApplication runtime leaks
  let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
  let response : app.Action := ⟨some material⟩
  let remembered := memory.record runtime (nativeLeaks (graph := graph))
    (memory.shadow.inputView runtime (nativeLeaks (graph := graph))
      ((execution runtime leaks repaired).observe nativeApp owner))
    (action runtime leaks response)
  have packet : app.packet (app.submit original.application owner material) owner
      (original.network.known owner) material =
      app.packet (app.submit repaired.application owner material) owner
        (repaired.network.known owner) material := by
    change (original.respond app owner response).application.emit owner
        (original.network.known owner) material =
      (repaired.respond app owner response).application.emit owner
        (repaired.network.known owner) material
    rw [leftInert, rightInert, emit_mask, emit_mask, nativePacket]
    have attempts : original.application.attempt = repaired.application.attempt :=
      congrArg PhasePublicView.attempt frame.publicView
    rw [attempts, frame.publicView]
  have envelopes : PhaseCount.localEnvelope runtime leaks owner (original.recall owner)
      (original.observe app owner) material =
      PhaseCount.localEnvelope runtime leaks owner (repaired.recall owner)
        (repaired.observe app owner) material := by
    rw [PhaseCount.localEnvelope_eq_of_recall runtime leaks original left.1 left.2.1,
      PhaseCount.localEnvelope_eq_of_recall runtime leaks repaired right.1 right.2.1,
      packet]
    exact congrArg (fun serial =>
      (⟨(owner, serial), app.packet (app.submit repaired.application owner material) owner
        (repaired.network.known owner) material⟩ : Message Player (CommitAttemptPacket graph)))
      (congrArg (fun pool : MessageNetwork Player (CommitAttemptPacket graph) =>
        pool.nextSerial owner) frame.network)
  have legal : response ∈ PhaseCount.onePacketActions runtime leaks bounds owner
      (repaired.recall owner) (repaired.observe app owner) := by
    have allowed := member
    rw [PhaseCount.mem_onePacketActions] at allowed ⊢
    refine ⟨?_, ?_⟩
    · have knownLeft : original.network.known owner =
          ReactiveApplication.ResponseMenu.knownPackets (original.recall owner)
            (original.observe app owner) := app.known_from_recall original owner left.1
      have knownRight : repaired.network.known owner =
          ReactiveApplication.ResponseMenu.knownPackets (repaired.recall owner)
            (repaired.observe app owner) := app.known_from_recall repaired owner right.1
      have rawAllowed := allowed.1
      rw [PhaseCount.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at rawAllowed
      rw [PhaseCount.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
      change material ∈ bounds.submissions _
      change material ∈ bounds.submissions _ at rawAllowed
      rw [← knownLeft, frame.network, knownRight] at rawAllowed
      exact rawAllowed
    · rcases allowed.2 with impossible | ⟨other, transmitted, permitted⟩
      · cases impossible
      · cases Option.some.inj transmitted
        right
        refine ⟨material, rfl, ?_⟩
        rw [← frame.outputs left.1 right.1 owner, ← envelopes]
        exact permitted
  refine ⟨legal, ?_⟩
  have leftNative : nativeApp.submit original.application.current.native owner material =
      original.application.current.native := congrArg (fun state => state.current.native) leftInert
  have rightNative : nativeApp.submit repaired.application.current.native owner material =
      repaired.application.current.native := congrArg (fun state => state.current.native) rightInert
  have emitted : material.emit (execution runtime leaks original).application owner
      ((execution runtime leaks original).network.known owner) =
      material.emit (execution runtime leaks repaired).application owner
        ((execution runtime leaks repaired).network.known owner) := by
    change material.emit original.application.current.native owner
        ((PhaseBindingRepair.network original.network).known owner) =
      material.emit repaired.application.current.native owner
        ((PhaseBindingRepair.network repaired.network).known owner)
    rw [network_known, network_known]
    exact nativePacket
  have live : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) remembered owner
      (execution runtime leaks (original.respond app owner response))
      (execution runtime leaks (repaired.respond app owner response)) := by
    rw [execution_respond_of_onePacket runtime leaks bounds original owner response member,
      execution_respond_of_onePacket runtime leaks bounds repaired owner response legal]
    exact frame.live.inert_submission material material leftNative rightNative emitted
  have savedLeft : (checkpoint runtime leaks (original.respond app owner response)).application =
      (checkpoint runtime leaks original).application :=
    congrArg (fun state : PhaseRuntimeState graph =>
      { state.entry.native with candidates := state.current.native.candidates }) leftInert
  have savedRight : (checkpoint runtime leaks (repaired.respond app owner response)).application =
      (checkpoint runtime leaks repaired).application :=
    congrArg (fun state : PhaseRuntimeState graph =>
      { state.entry.native with candidates := state.current.native.candidates }) rightInert
  have saved : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) remembered owner
      (checkpoint runtime leaks (original.respond app owner response))
      (checkpoint runtime leaks (repaired.respond app owner response)) := by
    apply checkpointFrame live
      (checkpoint runtime leaks (original.respond app owner response)).application
      (checkpoint runtime leaks (repaired.respond app owner response)).application
    · rw [savedRight, savedLeft]
      exact congrArg ReactiveApplication.PlayerView.application frame.saved.observed
    · rw [savedLeft, savedRight]
      exact frame.saved.views
    · rw [savedLeft, savedRight]
      exact frame.saved.slots
    · rw [savedLeft, savedRight]
      exact frame.saved.successful
  refine ⟨live, saved, ?_, ?_, ?_, ?_, ?_, ?_, ?_, frame.service, ?_⟩
  · rw [leftInert, rightInert]
    exact frame.phases
  · rw [leftInert, rightInert]
    exact frame.generation
  · rw [leftInert]
    exact frame.clearOriginal
  · rw [rightInert]
    exact frame.clearRepaired
  · rw [leftInert]
    exact frame.archiveOriginal
  · rw [rightInert]
    exact frame.archiveRepaired
  · change (original.network.submit owner _).2 = (repaired.network.submit owner _).2
    exact congrArg₂ (fun pool message => (pool.submit owner message).2) frame.network packet
  · intro who different
    rw [app.respond_recall_other original owner who different,
      app.respond_recall_other repaired owner who different]
    exact frame.foreignRecall who different

end Frame

end Vegas.EventGraphRuntime.PhaseBindingRepair
