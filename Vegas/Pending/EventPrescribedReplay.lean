/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventResolutionOrigin
import Vegas.Pending.EventReplay
import Vegas.Pending.EventDisclosure
import Vegas.Pending.EventCompletionObservation

/-! # Replay of prescribed opening packets

An opening sent by an unchanged player discloses its successful publication
result. Packet provenance makes this fact available without equating either
player's hidden binding store with the other execution's store.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- A prescribed opening carries the successful result of the retained
checks, rather than an unchecked candidate value. -/
theorem resolutionSubmission_opening_result (runtime : EventGraphRuntime graph)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : runtime.application.View)
    (candidate : Handle graph) (raw : Raw L)
    (submission : runtime.resolutionSubmission owner event payload binding checks outputEq
      action view = .submit (.opening event candidate raw)) :
    ∃ value : L.Val payload, raw = ⟨payload, value⟩ ∧
      cast (congrArg EventField.Action outputEq) action = true ∧
      EventCode.resolveOutput? binding checks true view.application.observation.store =
        some (.success value) := by
  unfold resolutionSubmission resolutionPayload at submission
  dsimp only at submission
  split at submission
  · rename_i disclose
    split at submission
    · rename_i value result
      split at submission
      · rename_i handle found
        split at submission
        · have packetEq := MessageInterface.PlayerCommand.submit.inj submission
          have rawEq := (Payload.opening.inj packetEq).2.2
          exact ⟨value, rawEq.symm, disclose, result⟩
        · cases submission
      · cases submission
    · cases submission
    · cases submission
  · cases submission

/-- Provenance identifies an accepted prescribed opening with a successful
graph resolution. This includes disclosures of initial binding fields. -/
theorem handle_prescribed_opening_eq (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (owner : Player)
    (origins : ResolutionOrigins runtime execution owner)
    (invariant : execution.native.application.BindingInvariant)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewNode : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (ready : execution.native.application.config.cut.Ready event)
    (timely : execution.native.application.WithinDeadline runtime event)
    (nonce : Nat) (candidate : Handle graph) (raw : Raw L)
    (pending : (⟨(owner, nonce), .opening event candidate raw⟩ :
      Message Player (Payload graph)) ∈ execution.native.pool.pending) :
    ∃ (action : graph.Action event) (value : L.Val payload),
      raw = ⟨payload, value⟩ ∧
      runtime.handle execution.native.application
          ⟨(owner, nonce), .opening event candidate raw⟩ =
        some (execution.native.application.complete event ready action
          (cast (congrArg EventField.Value outputEq.symm) (.success value))) := by
  obtain ⟨action, cached, submission⟩ := origins.pending_resolutionSubmission runtime
    execution owner event payload owner binding checks outputEq codeEq viewNode ready
    ⟨(owner, nonce), .opening event candidate raw⟩ pending rfl rfl
  obtain ⟨value, rawEq, disclose, resolved⟩ := runtime.resolutionSubmission_opening_result
    owner event payload binding checks outputEq action
    (MessageApplication.State.observe runtime.application execution.native owner)
    candidate raw submission
  obtain ⟨result, packet, actualResult, actualSubmission, handled⟩ :=
    runtime.handle_resolutionSubmission_eq execution.native event owner payload binding checks
      outputEq codeEq viewNode ready timely action cached invariant nonce
  have packetEq := MessageInterface.PlayerCommand.submit.inj
    (actualSubmission.symm.trans submission)
  have resultEq : result = .success value := by
    rw [disclose] at actualResult
    change EventCode.resolveOutput? binding checks true
      (graph.playerStore owner execution.native.application.config.store) = _ at resolved
    rw [EventCode.resolveOutput?_playerStore] at resolved
    exact Option.some.inj (actualResult.symm.trans resolved)
  refine ⟨action, value, rawEq, ?_⟩
  simpa only [packetEq, resultEq] using handled

/-- A common pending opening from an unchanged opponent has the same
observable handler result in paired executions. Candidate provenance, not
equality of foreign private state, justifies acceptance on both sides. -/
theorem NativeReplay.handle_prescribed_opening
    (runtime : EventGraphRuntime graph) (focal owner : Player) (different : owner ≠ focal)
    {left right : runtime.application.PolicyExecution}
    (replay : NativeReplay runtime focal left right)
    (leftOrigins : ResolutionOrigins runtime left owner)
    (rightOrigins : ResolutionOrigins runtime right owner)
    (leftBinding : left.native.application.BindingInvariant)
    (rightBinding : right.native.application.BindingInvariant)
    (event : graph.EventId) (nonce : Nat) (candidate : Handle graph) (raw : Raw L)
    (pending : (⟨(owner, nonce), .opening event candidate raw⟩ :
      Message Player (Payload graph)) ∈ left.native.pool.pending) :
    Option.map (fun state => state.playerView focal)
        (runtime.handle left.native.application ⟨(owner, nonce), .opening event candidate raw⟩) =
      Option.map (fun state => state.playerView focal)
        (runtime.handle right.native.application
          ⟨(owner, nonce), .opening event candidate raw⟩) := by
  have cutEq := cut_eq_of_completionOrder_eq left.native.application.config
    right.native.application.config
    (congrArg PlayerObservation.completionOrder replay.observation)
  have clockEq := congrArg PublicView.clock replay.publicView
  have activatedEq := congrArg PublicView.activatedAt replay.publicView
  have timelyEq : left.native.application.WithinDeadline runtime event ↔
      right.native.application.WithinDeadline runtime event := by
    unfold State.WithinDeadline
    rw [show left.native.application.activatedAt = right.native.application.activatedAt
        from activatedEq,
      show left.native.application.clock = right.native.application.clock from clockEq]
  by_cases leftReady : left.native.application.config.cut.Ready event
  · have rightReady : right.native.application.config.cut.Ready event := by
      simpa only [← cutEq] using leftReady
    by_cases leftTimely : left.native.application.WithinDeadline runtime event
    · have rightTimely := timelyEq.mp leftTimely
      cases viewNode : nodeView graph event with
      | bind nodeOwner payload outputEq codeEq | sample payload law outputEq codeEq =>
          simp [handle, leftReady, rightReady, leftTimely, rightTimely, viewNode]
      | resolve nodeOwner payload binding checks outputEq codeEq =>
          by_cases sender : owner = nodeOwner
          · subst nodeOwner
            have rightPending : (⟨(owner, nonce), .opening event candidate raw⟩ :
                Message Player (Payload graph)) ∈ right.native.pool.pending := by
              rw [← replay.pool]
              exact pending
            obtain ⟨leftAction, leftValue, leftRaw, leftHandled⟩ :=
              runtime.handle_prescribed_opening_eq left owner leftOrigins leftBinding
                event payload binding checks outputEq codeEq viewNode leftReady leftTimely
                nonce candidate raw pending
            obtain ⟨rightAction, rightValue, rightRaw, rightHandled⟩ :=
              runtime.handle_prescribed_opening_eq right owner rightOrigins rightBinding
                event payload binding checks outputEq codeEq viewNode rightReady rightTimely
                nonce candidate raw rightPending
            have values : leftValue = rightValue := by
              have decoded := congrArg (fun raw : Raw L => raw.as? payload)
                (leftRaw.symm.trans rightRaw)
              simpa only [Raw.as?_mk, Option.some.injEq] using decoded
            have actor : graph.actor? event = some owner := by
              have castActor := EventCode.actor_cast outputEq (graph.nodes event)
              rw [codeEq] at castActor
              exact castActor.symm
            rw [leftHandled, rightHandled]
            simp only [Option.map_some, Option.some.injEq]
            apply State.complete_playerView_congr _ _ focal replay.publicView replay.observation
              replay.remembered replay.candidates event leftReady rightReady
              leftAction rightAction
            · intro _
              rw [values]
            · intro owned
              exact (different (Option.some.inj (actor.symm.trans owned))).elim
          · simp [handle, leftReady, rightReady, leftTimely, rightTimely, viewNode,
              Message.sender, sender]
    · have rightTimely : ¬ right.native.application.WithinDeadline runtime event :=
        fun timely => leftTimely (timelyEq.mpr timely)
      simp [handle, leftReady, rightReady, leftTimely, rightTimely]
  · have rightReady : ¬ right.native.application.config.cut.Ready event := by
      simpa only [← cutEq] using leftReady
    simp [handle, leftReady, rightReady]

end Vegas.EventGraphRuntime
