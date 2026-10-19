/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochOriginalWord
import Vegas.Pending.PhaseReadyResolution
import Interaction.ReactiveOwnerSelection

/-! # Foreign original acceptance words survive another owner's current response -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
private theorem response_request_iff (execution : (app).Execution) (actor : Player)
    (response : (app).Action) (owner : Player) (coordinate : CommitAttemptEvent graph) :
    (execution.respond app actor response).application.SeedRequest owner coordinate ↔
      execution.application.SeedRequest owner coordinate := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material =>
      have config : (execution.application.submit actor material).current.native.config =
          execution.application.current.native.config := by
        change (submitStep _ actor _).config = _
        rw [submitStep_config, (material.call.register_facts actor _).1]
      change (execution.application.submit actor material).SeedRequest owner coordinate ↔ _
      unfold PhaseRuntimeState.SeedRequest
      rw [config]
      rfl

omit [Fintype Player] in
theorem response_foreign_pending (execution : (app).Execution) (actor owner : Player)
    (different : owner ≠ actor) (response : (app).Action)
    (message : Message Player (CommitAttemptPacket graph)) (authored : message.sender = owner) :
    message ∈ (execution.respond app actor response).network.pending ↔
      message ∈ execution.network.pending := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material =>
      let packet := (app).packet ((app).submit execution.application actor material) actor
        (execution.network.known actor) material
      change message ∈ execution.network.pending ++
        [⟨(actor, execution.network.nextSerial actor), packet⟩] ↔ _
      rw [List.mem_append, List.mem_singleton]
      constructor
      · rintro (old | fresh)
        · exact old
        · have sender : message.sender = actor := congrArg Message.sender fresh
          exact (different (authored.symm.trans sender)).elim
      · exact Or.inl

/-- The pure frontier event does not inspect another owner's new packet,
private preparation, own response word or newly occupied slot. -/
theorem frontierQualification_respond_foreign {length : Nat} (tape : Tape Player length)
    (execution : (app).Execution) (actor owner : Player) (different : owner ≠ actor)
    (response : (app).Action) (frontier : graph.EventId) :
    frontierQualification runtime leaks tape (execution.respond app actor response) owner frontier ↔
      frontierQualification runtime leaks tape execution owner frontier := by
  have recalled := (app).respond_recall_other execution actor owner different response
  have cursor := (app).respond_environmentRecall execution actor response
  have attempt : (execution.respond app actor response).application.attempt =
      execution.application.attempt := by
    rcases response with ⟨transmission⟩
    cases transmission <;> rfl
  have activated : (execution.respond app actor response).application.current.native.activatedAt =
      execution.application.current.native.activatedAt := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some material =>
        have visible := PhaseCount.submit_publicView execution.application actor material
        exact congrArg (fun view : PhasePublicView graph => view.native.activatedAt) visible
  unfold frontierQualification
  dsimp only
  rw [recalled, cursor, attempt, activated]
  apply exists_congr
  intro entered
  apply and_congr_right
  intro _stamp
  split_ifs with unsent
  · rfl
  · constructor
    · rintro ⟨message, pending, candidate, sender, call, address, epoch⟩
      exact ⟨message, (response_foreign_pending runtime leaks execution actor owner different
        response message sender).mp pending, candidate, sender, call, address, epoch⟩
    · rintro ⟨message, pending, candidate, sender, call, address, epoch⟩
      exact ⟨message, (response_foreign_pending runtime leaks execution actor owner different
        response message sender).mpr pending, candidate, sender, call, address, epoch⟩

/-- The full foreign owned word, including inherited acceptance and all old
frontier cases, is unchanged by an arbitrary current response of another owner.
This is a joint deterministic word identity, not a probability-independence claim. -/
theorem ownedAcceptanceWord_respond_foreign {length : Nat} (tape : Tape Player length)
    (execution : (app).Execution) (actor owner : Player) (different : owner ≠ actor)
    (response : (app).Action) (event : graph.EventId) :
    ownedAcceptanceWord runtime leaks tape (execution.respond app actor response) owner event ↔
      ownedAcceptanceWord runtime leaks tape execution owner event := by
  have excluded : (execution.respond app actor response).application.current.excluded =
      execution.application.current.excluded := by
    rcases response with ⟨transmission⟩
    cases transmission <;> rfl
  have accepted : (execution.respond app actor response).application.current.native.accepted =
      execution.application.current.native.accepted := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some material =>
        change (submitStep _ actor _).accepted = _
        rw [submitStep_accepted, Submission.register_accepted]
  have attempt : (execution.respond app actor response).application.attempt =
      execution.application.attempt := by
    rcases response with ⟨transmission⟩
    cases transmission <;> rfl
  unfold ownedAcceptanceWord
  rw [excluded, accepted, attempt]
  split_ifs with blocked
  · rfl
  · apply forall_congr'
    intro frontier
    exact imp_congr (response_request_iff runtime leaks execution actor response owner _)
      (or_congr Iff.rfl (frontierQualification_respond_foreign runtime leaks tape execution actor
        owner different response frontier))

end Vegas.EventGraphRuntime.ReservedEpoch
