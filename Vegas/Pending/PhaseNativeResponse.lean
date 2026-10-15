/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativeCursor

/-! # Count-admitted responses commute with native physical execution -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph) (bounds : MessageBounds graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

private theorem authorized_of_onePacket (current : (P).Execution)
    (recalled : PhaseCount.CountRecall runtime leaks current) (who : Player)
    (material : WitnessedSubmission graph)
    (permitted : (⟨some material⟩ : (P).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds
      who (current.recall who) (current.observe P who)) :
    ((current.application.submit who material).emit who (current.network.known who)
      material).packet.tokenValid = true := by
  rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds who _ _ _).mp permitted).2 with
    silent | ⟨actual, same, admitted⟩
  · cases silent
  · have materialEq : material = actual := Option.some.inj same
    subst actual
    rw [PhaseCount.localEnvelope_eq_of_recall runtime leaks current recalled.1 recalled.2.1]
      at admitted
    exact ((PhaseCount.permits_eq_true_iff _ _).mp admitted).1

/-- The actual count menu removes precisely the emission masks that would
obstruct erasing physical phase addresses. Every remaining response commutes. -/
theorem respond_of_onePacket (current : (P).Execution)
    (recalled : PhaseCount.CountRecall runtime leaks current) (who : Player)
    (response : (P).Action)
    (permitted : response ∈ PhaseCount.onePacketActions runtime leaks bounds who
      (current.recall who) (current.observe P who)) :
    execution runtime leaks plan (current.respond P who response) =
      (execution runtime leaks plan current).respond N who
        (action runtime leaks plan response) := by
  cases response with
  | mk transmission =>
      cases transmission with
      | none =>
          simp only [ReactiveApplication.Execution.respond, execution, action]
          congr 1
          funext observer
          split <;> simp_all only [List.map_append, List.map_cons, List.map_nil,
            playerEntry, playerView]
          rfl
      | some material =>
          have authorized := authorized_of_onePacket runtime leaks bounds current recalled who
            material permitted
          have packet := emit_of_authorized runtime leaks plan current.application who
            (current.network.known who) material authorized
          have network := congrArg Prod.snd (MessageNetwork.mapPayload_submit
            CommitAttemptPacket.packet current.network who
              ((current.application.submit who material).emit who (current.network.known who)
                material))
          change (current.network.submit who
              ((current.application.submit who material).emit who (current.network.known who)
                material)).2.mapPayload CommitAttemptPacket.packet =
            ((current.network.mapPayload CommitAttemptPacket.packet).submit who
              ((current.application.submit who material).emit who (current.network.known who)
                material).packet).2 at network
          have emitted := congrArg Prod.fst (MessageNetwork.mapPayload_submit
            CommitAttemptPacket.packet current.network who
              ((current.application.submit who material).emit who (current.network.known who)
                material))
          change Message.mapPayload CommitAttemptPacket.packet
              (current.network.submit who
                ((current.application.submit who material).emit who (current.network.known who)
                  material)).1 =
            ((current.network.mapPayload CommitAttemptPacket.packet).submit who
              ((current.application.submit who material).emit who (current.network.known who)
                material).packet).1 at emitted
          have nativeKnown := known runtime leaks plan current who
          change (current.network.mapPayload CommitAttemptPacket.packet).known who =
            (current.network.known who).map (Message.mapPayload CommitAttemptPacket.packet)
              at nativeKnown
          erw [packet, ← nativeKnown] at emitted
          simp only [ReactiveApplication.Execution.respond, execution, action]
          erw [network, packet, ← nativeKnown]
          congr 1
          funext observer
          split <;> simp_all only [List.map_append, List.map_cons, List.map_nil,
            playerEntry, playerView]
          simp only [Option.map_some]
          erw [emitted]
          rfl

end Vegas.EventGraphRuntime.PhaseNativeProjection
