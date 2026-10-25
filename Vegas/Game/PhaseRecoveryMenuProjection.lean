/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseRecoveryInformation
import Vegas.Pending.PhaseResponseNormalization

/-! # Bounded response syntax under phase metadata erasure

Raw submissions and their existing operational normal forms project exactly to
the recovery menus. The count-permission filters and reachable-history dynamics
are separate obligations; this comparison does not assert equilibrium transport.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRecoveryProjection

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (recoveryLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "P" => phaseApplication runtime leaks
local notation "R" => runtime.recoveryApplication recoveryLeaks

theorem action_injective : Function.Injective (action runtime leaks recoveryLeaks) := by
  intro first second same
  simpa only [phaseAction_action] using congrArg (phaseAction runtime leaks recoveryLeaks) same

/-- Existing operational response normalization commutes with tag erasure. -/
theorem normalization_projected (who : Player) (past : List (P).PlayerEntry)
    (view : (P).PlayerView) (response : (P).Action) :
    action runtime leaks recoveryLeaks
        ((PhaseCount.normalization runtime leaks).action who past view response) =
      (Recovery.normalization runtime recoveryLeaks).action who
        (past.map (playerEntry runtime leaks recoveryLeaks))
        (playerView runtime leaks recoveryLeaks view)
        (action runtime leaks recoveryLeaks response) := by
  cases response with
  | mk transmission =>
      cases transmission with
      | none => rfl
      | some material =>
          simp only [ReactiveApplication.SubmissionNormalization.action, action,
            PhaseCount.normalization, Recovery.normalization, knownPackets]
          rfl

variable [Fintype Player] (bounds : MessageBounds graph)

/-- The full bounded submission syntax is unchanged by attempt metadata. -/
theorem rawMenu_projected (who : Player) (past : List (P).PlayerEntry)
    (view : (P).PlayerView) (response : (P).Action) :
    response ∈ (PhaseCount.rawMenu runtime leaks bounds).actions who past view ↔
      action runtime leaks recoveryLeaks response ∈
        (Recovery.rawMenu runtime recoveryLeaks bounds).actions who
          (past.map (playerEntry runtime leaks recoveryLeaks))
          (playerView runtime leaks recoveryLeaks view) := by
  rw [PhaseCount.rawMenu, Recovery.rawMenu,
    ReactiveApplication.ResponseMenu.fromSubmissions_mem,
    ReactiveApplication.ResponseMenu.fromSubmissions_mem, knownPackets]
  cases response with
  | mk transmission => cases transmission <;> rfl

/-- Canonical bounded menus agree before imposing either contract's count filter. -/
theorem normalizedMenu_projected (who : Player) (past : List (P).PlayerEntry)
    (view : (P).PlayerView) (response : (P).Action) :
    response ∈ ((PhaseCount.normalization runtime leaks).menu
        (PhaseCount.rawMenu runtime leaks bounds)).actions who past view ↔
      action runtime leaks recoveryLeaks response ∈
        (Recovery.menu runtime recoveryLeaks bounds).actions who
          (past.map (playerEntry runtime leaks recoveryLeaks))
          (playerView runtime leaks recoveryLeaks view) := by
  rw [Recovery.menu, ReactiveApplication.SubmissionNormalization.menu_mem,
    ReactiveApplication.SubmissionNormalization.menu_mem]
  constructor
  · rintro ⟨original, member, same⟩
    refine ⟨action runtime leaks recoveryLeaks original,
      (rawMenu_projected runtime leaks recoveryLeaks bounds who past view original).mp member, ?_⟩
    rw [← normalization_projected, same]
  · rintro ⟨original, member, same⟩
    refine ⟨phaseAction runtime leaks recoveryLeaks original, ?_, ?_⟩
    · apply (rawMenu_projected runtime leaks recoveryLeaks bounds who past view _).mpr
      simpa only [action_phaseAction] using member
    · apply action_injective runtime leaks recoveryLeaks
      rw [normalization_projected, action_phaseAction]
      exact same

end Vegas.EventGraphRuntime.PhaseRecoveryProjection
