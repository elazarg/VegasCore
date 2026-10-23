/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionCountMenu

/-! # Agreement of bounded menus before exclusion

The recovery menus retain every default bounded choice while the current
exclusion set is empty. Full recall is projected without erasing any envelope.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.Recovery

open Interaction

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (bounds : MessageBounds graph)

omit [Fintype Player] in
theorem projectedAction_injective :
    Function.Injective (RecoveryProjection.action runtime leaks) := by
  intro first second same
  have transmission := congrArg ReactiveApplication.Action.transmission same
  cases first
  cases second
  cases transmission
  rfl

omit [Fintype Player] in
theorem normalization_projected (who : Player)
    (past : List (runtime.recoveryApplication leaks).PlayerEntry)
    (view : (runtime.recoveryApplication leaks).PlayerView)
    (response : (runtime.recoveryApplication leaks).Action) :
    RecoveryProjection.action runtime leaks
        ((normalization runtime leaks).action who past view response) =
      (runtime.reactiveNormalization leaks).action who
        (past.map (RecoveryProjection.playerEntry runtime leaks))
        (RecoveryProjection.playerView runtime leaks view)
        (RecoveryProjection.action runtime leaks response) := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material =>
      simp only [ReactiveApplication.SubmissionNormalization.action,
        RecoveryProjection.action, normalization, reactiveNormalization,
        RecoveryProjection.knownPackets]
      rfl

theorem rawMenu_projected (who : Player)
    (past : List (runtime.recoveryApplication leaks).PlayerEntry)
    (view : (runtime.recoveryApplication leaks).PlayerView)
    (response : (runtime.recoveryApplication leaks).Action) :
    response ∈ (rawMenu runtime leaks bounds).actions who past view ↔
      RecoveryProjection.action runtime leaks response ∈
        (bounds.rawMenu runtime leaks).actions who
          (past.map (RecoveryProjection.playerEntry runtime leaks))
          (RecoveryProjection.playerView runtime leaks view) := by
  rw [rawMenu, MessageBounds.rawMenu,
    ReactiveApplication.ResponseMenu.fromSubmissions_mem,
    ReactiveApplication.ResponseMenu.fromSubmissions_mem,
    RecoveryProjection.knownPackets]
  rcases response with ⟨transmission⟩
  cases transmission <;> rfl

theorem menu_projected (who : Player)
    (past : List (runtime.recoveryApplication leaks).PlayerEntry)
    (view : (runtime.recoveryApplication leaks).PlayerView)
    (response : (runtime.recoveryApplication leaks).Action) :
    response ∈ (menu runtime leaks bounds).actions who past view ↔
      RecoveryProjection.action runtime leaks response ∈
        (bounds.menu runtime leaks).actions who
          (past.map (RecoveryProjection.playerEntry runtime leaks))
          (RecoveryProjection.playerView runtime leaks view) := by
  rw [menu, ReactiveApplication.SubmissionNormalization.menu_mem_iff_of_closed
    _ _ _ _ _ (rawMenu_closed runtime leaks bounds who past view),
    MessageBounds.menu, ReactiveApplication.SubmissionNormalization.menu_mem_iff_of_closed
      _ _ _ _ _ (bounds.rawMenu_closed runtime leaks who _ _), rawMenu_projected]
  apply and_congr_right
  intro _
  constructor
  · intro same
    have mapped := congrArg (RecoveryProjection.action runtime leaks) same
    rwa [normalization_projected] at mapped
  · intro same
    apply projectedAction_injective runtime leaks
    rwa [normalization_projected]

omit [Fintype Player] in
theorem maskPacket_empty (packet : WitnessedPacket graph) :
    maskPacket (∅ : Finset Player) packet = packet := by
  unfold maskPacket
  cases packet.call.event? graph with
  | none => rfl
  | some event => simp

omit [Fintype Player] in
theorem localEnvelope_of_empty (who : Player)
    (past : List (runtime.recoveryApplication leaks).PlayerEntry)
    (view : (runtime.recoveryApplication leaks).PlayerView)
    (empty : view.application.2 = ∅)
    (material : (runtime.recoveryApplication leaks).Submission) :
    localEnvelope runtime leaks who past view material =
      runtime.localEnvelope leaks who
        (past.map (RecoveryProjection.playerEntry runtime leaks))
        (RecoveryProjection.playerView runtime leaks view) material := by
  let envelope := runtime.localEnvelope leaks who
    (past.map (RecoveryProjection.playerEntry runtime leaks))
    (RecoveryProjection.playerView runtime leaks view) material
  change Message.mk envelope.id (maskPacket view.application.2 envelope.payload) = envelope
  rw [empty]
  exact congrArg (Message.mk envelope.id) (maskPacket_empty envelope.payload)

omit [Fintype Player] in
theorem onePacketResponse_of_empty (who : Player)
    (past : List (runtime.recoveryApplication leaks).PlayerEntry)
    (view : (runtime.recoveryApplication leaks).PlayerView)
    (empty : view.application.2 = ∅)
    (response : (runtime.recoveryApplication leaks).Action) :
    OnePacketResponse runtime leaks who past view response ↔
      runtime.OnePacketResponse leaks who
        (past.map (RecoveryProjection.playerEntry runtime leaks))
        (RecoveryProjection.playerView runtime leaks view)
        (RecoveryProjection.action runtime leaks response) := by
  unfold OnePacketResponse EventGraphRuntime.OnePacketResponse
  simp only [RecoveryProjection.outputs, RecoveryProjection.action]
  constructor
  · rintro ⟨material, sent, permitted⟩
    exact ⟨material, sent, by rwa [← localEnvelope_of_empty runtime leaks who past view empty]⟩
  · rintro ⟨material, sent, permitted⟩
    exact ⟨material, sent, by rwa [localEnvelope_of_empty runtime leaks who past view empty]⟩

theorem onePacketMenu_projected_of_empty (who : Player)
    (past : List (runtime.recoveryApplication leaks).PlayerEntry)
    (view : (runtime.recoveryApplication leaks).PlayerView)
    (empty : view.application.2 = ∅)
    (response : (runtime.recoveryApplication leaks).Action) :
    response ∈ (onePacketMenu runtime leaks bounds).actions who past view ↔
      RecoveryProjection.action runtime leaks response ∈
        (bounds.onePacketMenu runtime leaks).actions who
          (past.map (RecoveryProjection.playerEntry runtime leaks))
          (RecoveryProjection.playerView runtime leaks view) := by
  change response ∈ onePacketActions runtime leaks bounds who past view ↔ _
  rw [mem_onePacketActions]
  change _ ↔ RecoveryProjection.action runtime leaks response ∈
    bounds.onePacketActions runtime leaks who _ _
  rw [MessageBounds.mem_onePacketActions, menu_projected,
    onePacketResponse_of_empty runtime leaks who past view empty]
  rfl

end Vegas.EventGraphRuntime.Recovery
