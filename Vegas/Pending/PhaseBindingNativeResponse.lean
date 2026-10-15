/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingRepairFrame
import Vegas.Pending.ReactiveBindingSubmissionFrame

/-! # Admitted physical responses use the existing native repair semantics -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks
local notation "nativeApp" => runtime.reactiveApplication (nativeLeaks (graph := graph))

theorem network_known (physical : MessageNetwork Player (CommitAttemptPacket graph))
    (who : Player) :
    (network physical).known who = (physical.known who).map PhaseCount.nativeMessage := by
  simp only [MessageNetwork.known, network, List.map_append, List.filter_map]
  rfl

theorem network_submit (physical : MessageNetwork Player (CommitAttemptPacket graph))
    (who : Player) (attempt : CommitAttemptId) (packet : WitnessedPacket graph) :
    network (physical.submit who ⟨attempt, packet⟩).2 =
      ((network physical).submit who packet).2 := by
  simp only [network, MessageNetwork.submit, List.map_append, List.map_cons, List.map_nil]
  rfl

/-- Both public masks are discharged on an admitted local call. The native
projection therefore retains its actual certificate, not a reconstructed substitute. -/
theorem emit_admitted (state : PhaseRuntimeState graph) (who : Player)
    (known : List (Message Player (CommitAttemptPacket graph)))
    (material : WitnessedSubmission graph)
    (allowed : state.allows material.call.packet = true)
    (unexcluded : state.current.excludedCall material.call.packet = false) :
    (state.emit who known material).packet =
      material.emit state.current.native who (known.map PhaseCount.nativeMessage) := by
  let packet := material.emit state.current.native who (known.map PhaseCount.nativeMessage)
  let masked := if state.current.excludedCall packet.call then
    { packet with token := none } else packet
  change (if state.allows masked.call then masked else { masked with token := none }) = packet
  simp only [masked, packet, WitnessedSubmission.emit_call, allowed, unexcluded,
    Bool.false_eq_true, ↓reduceIte]

/-- An actual admitted response projects to the native response used in the
existing frame. The result includes every physical own-recall entry. -/
theorem execution_respond (physical : (app).Execution) (who : Player) (response : (app).Action)
    (admitted : ∀ material, response.transmission = some material →
      physical.application.allows material.call.packet = true ∧
        physical.application.current.excludedCall material.call.packet = false) :
    execution runtime leaks (physical.respond (app) who response) =
      (execution runtime leaks physical).respond (nativeApp) who (action runtime leaks response) :=
  by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      simp only [ReactiveApplication.Execution.respond, execution, action]
      congr 1
      funext observer
      by_cases same : observer = who
      · subst observer
        simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil]
        rfl
      · simp only [same, ↓reduceIte]
  | some material =>
      obtain ⟨allowed, unexcluded⟩ := admitted material rfl
      have sent := emit_admitted (physical.application.submit who material) who
        (physical.network.known who) material allowed unexcluded
      have known := network_known (graph := graph) physical.network who
      simp only [ReactiveApplication.Execution.respond, execution, action]
      change (⟨_, network (physical.network.submit who
          ((physical.application.submit who material).emit who
            (physical.network.known who) material)).2, _, _, _⟩ : (nativeApp).Execution) = _
      have packetEq : ((physical.application.submit who material).emit who
          (physical.network.known who) material) =
          ⟨physical.application.attempt,
            material.emit (physical.application.submit who material).current.native who
              ((physical.network.known who).map PhaseCount.nativeMessage)⟩ := by
        cases emitted : (physical.application.submit who material).emit who
            (physical.network.known who) material with
        | mk attempt packet =>
            have packetValue := sent
            rw [emitted] at packetValue
            have address : attempt = physical.application.attempt := by
              have raw : ((physical.application.submit who material).emit who
                  (physical.network.known who) material).attempt =
                  physical.application.attempt := rfl
              rwa [emitted] at raw
            cases address
            exact congrArg (CommitAttemptPacket.mk physical.application.attempt) packetValue
      have actualPacket : (app).packet ((app).submit physical.application who material) who
          (physical.network.known who) material =
          ⟨physical.application.attempt,
            (nativeApp).packet ((nativeApp).submit physical.application.current.native
              who material) who
              ((physical.network.known who).map PhaseCount.nativeMessage) material⟩ := packetEq
      rw [packetEq, network_submit]
      simp only [known, actualPacket]
      congr 1
      funext observer
      by_cases same : observer = who
      · subst observer
        simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil, entry]
        rw [← observe runtime leaks physical who]
        rfl
      · simp only [same, ↓reduceIte]

end Vegas.EventGraphRuntime.PhaseBindingRepair
