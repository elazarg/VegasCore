/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

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

variable {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- Exact physical envelope agreement transports both directions of the
counted inert raw menu. No probability law or source-view equality is assumed. -/
theorem inert_response_menu_iff (network : original.network = repaired.network)
    (bounds : MessageBounds graph)
    (left : PhaseCount.CountRecall runtime leaks original)
    (right : PhaseCount.CountRecall runtime leaks repaired) (material : WitnessedSubmission graph)
    (envelopes : PhaseCount.localEnvelope runtime leaks owner (original.recall owner)
      (original.observe (phaseApplication runtime leaks) owner) material =
        PhaseCount.localEnvelope runtime leaks owner (repaired.recall owner)
          (repaired.observe (phaseApplication runtime leaks) owner) material) :
    (⟨some material⟩ : (phaseApplication runtime leaks).Action) ∈
        PhaseCount.onePacketActions runtime leaks bounds owner (original.recall owner)
          (original.observe (phaseApplication runtime leaks) owner) ↔
      (⟨some material⟩ : (phaseApplication runtime leaks).Action) ∈
        PhaseCount.onePacketActions runtime leaks bounds owner (repaired.recall owner)
          (repaired.observe (phaseApplication runtime leaks) owner) := by
  let app := phaseApplication runtime leaks
  have knownLeft : original.network.known owner =
      ReactiveApplication.ResponseMenu.knownPackets (original.recall owner)
        (original.observe app owner) := app.known_from_recall original owner left.1
  have knownRight : repaired.network.known owner =
      ReactiveApplication.ResponseMenu.knownPackets (repaired.recall owner)
        (repaired.observe app owner) := app.known_from_recall repaired owner right.1
  have outputs : app.outputs (original.recall owner) = app.outputs (repaired.recall owner) := by
    rw [← left.1 owner, ← right.1 owner, network]
  have raw : (⟨some material⟩ : app.Action) ∈
      (PhaseCount.rawMenu runtime leaks bounds).actions owner (original.recall owner)
        (original.observe app owner) ↔
    (⟨some material⟩ : app.Action) ∈
      (PhaseCount.rawMenu runtime leaks bounds).actions owner (repaired.recall owner)
        (repaired.observe app owner) := by
    rw [PhaseCount.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem,
      ReactiveApplication.ResponseMenu.fromSubmissions_mem]
    change material ∈ bounds.submissions _ ↔ material ∈ bounds.submissions _
    rw [← knownLeft, network, knownRight]
  rw [PhaseCount.mem_onePacketActions, PhaseCount.mem_onePacketActions]
  constructor
  · rintro ⟨rawMember, silent | ⟨other, transmitted, permitted⟩⟩
    · cases silent
    · cases Option.some.inj transmitted
      refine ⟨raw.mp rawMember, Or.inr ⟨material, rfl, ?_⟩⟩
      rw [← outputs, ← envelopes]
      exact permitted
  · rintro ⟨rawMember, silent | ⟨other, transmitted, permitted⟩⟩
    · cases silent
    · cases Option.some.inj transmitted
      refine ⟨raw.mpr rawMember, Or.inr ⟨material, rfl, ?_⟩⟩
      rw [outputs, envelopes]
      exact permitted

namespace Frame

variable {memory : BindingMemory runtime (nativeLeaks (graph := graph))}

end Frame

end Vegas.EventGraphRuntime.PhaseBindingRepair
