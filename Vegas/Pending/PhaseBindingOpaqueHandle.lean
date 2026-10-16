/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingClearObservation
import Vegas.Pending.PhaseBindingCompletionSymmetry

/-! # All-value opaque packet handling through actual phase normalization -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRuntimeState

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem handle_binding_external_congr (runtime : EventGraphRuntime graph)
    (left right : PhaseRuntimeState graph) (hidden : Player)
    (phases : left.phases = right.phases) (generation : left.generation = right.generation)
    (retired : left.retired.map (fun prior => (prior.attempt, prior.state.publicView)) =
      right.retired.map (fun prior => (prior.attempt, prior.state.publicView)))
    (publicEq : left.current.native.publicView = right.current.native.publicView)
    (views : ∀ who, who ≠ hidden →
      left.current.native.playerView who = right.current.native.playerView who)
    (leftClear : left.current.excluded = ∅) (rightClear : right.current.excluded = ∅)
    (message : Message Player (CommitAttemptPacket graph))
    (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate) :
    (left.handle runtime message).map (fun next => (next.publicView,
        fun who => if who = hidden then none else some (next.playerView who))) =
      (right.handle runtime message).map (fun next => (next.publicView,
        fun who => if who = hidden then none else some (next.playerView who))) := by
  classical
  have attempts : left.attempt = right.attempt := by simp only [attempt, phases, generation]
  have allowed : left.allows message.payload.packet.call =
      right.allows message.payload.packet.call :=
    by simp only [allows, phases]
  have excluded : left.current.excludedCall message.payload.packet.call =
      right.current.excludedCall message.payload.packet.call := by
    simp only [RecoveryState.excludedCall, RecoveryState.excludedEvent, leftClear, rightClear]
  have decision := handle_commitment_publicView_congr runtime left.current.native
    right.current.native publicEq message.id event candidate
  rw [← call] at decision
  simp only [handle, attempts, allowed, excluded]
  split
  · cases first : EventGraphRuntime.handle runtime left.current.native
        ⟨message.id, message.payload.packet.call⟩ with
    | none =>
        cases second : EventGraphRuntime.handle runtime right.current.native
            ⟨message.id, message.payload.packet.call⟩ with
        | none => rfl
        | some next =>
            simp only [first, second, Option.map_none, Option.map_some] at decision
            cases decision
    | some firstNext =>
        cases second : EventGraphRuntime.handle runtime right.current.native
            ⟨message.id, message.payload.packet.call⟩ with
        | none =>
            simp only [first, second, Option.map_none, Option.map_some] at decision
            cases decision
        | some secondNext =>
            have nativePublic : firstNext.publicView = secondNext.publicView :=
              Option.some.inj (by simpa only [first, second, Option.map_some] using decision)
            have rawClearLeft : (left.current.inclusionResult message.payload.packet.call
                firstNext).excluded = ∅ := by simpa only [call, RecoveryState.inclusionResult]
                  using leftClear
            have rawClearRight : (right.current.inclusionResult message.payload.packet.call
                secondNext).excluded = ∅ := by simpa only [call, RecoveryState.inclusionResult]
                  using rightClear
            have normalized := normalize_publicView_congr_of_clear
              ({left with current := (left.current.inclusionResult
                message.payload.packet.call firstNext)} : PhaseRuntimeState graph)
              ({right with current := (right.current.inclusionResult
                message.payload.packet.call secondNext)} : PhaseRuntimeState graph)
              phases generation retired nativePublic rawClearLeft rawClearRight
            have nativeViews (who : Player) (different : who ≠ hidden) :
                firstNext.playerView who = secondNext.playerView who := by
              have same := handle_commitment_playerView_congr runtime left.current.native
                right.current.native who message.id event candidate (views who different)
              rw [← call, first, second, Option.map_some, Option.map_some] at same
              exact Option.some.inj same
            simp only [Option.map_some]
            apply congrArg some
            apply Prod.ext normalized
            funext who
            by_cases same : who = hidden
            · simp only [same, ite_true]
            · simp only [same, ite_false]
              apply congrArg some
              apply Prod.ext
              · have leftCurrent := (settle_of_clear left.phases left.generation left.entry
                  (left.current.inclusionResult message.payload.packet.call firstNext)
                    left.retired rawClearLeft).1
                have rightCurrent := (settle_of_clear right.phases right.generation right.entry
                  (right.current.inclusionResult message.payload.packet.call secondNext)
                    right.retired rawClearRight).1
                change State.playerView
                  (settle left.phases left.generation left.entry
                    (left.current.inclusionResult message.payload.packet.call firstNext)
                      left.retired).current.native who =
                    State.playerView
                      (settle right.phases right.generation right.entry
                        (right.current.inclusionResult message.payload.packet.call secondNext)
                          right.retired).current.native who
                rw [leftCurrent, rightCurrent]
                exact nativeViews who same
              · exact normalized
  · rfl

private theorem opening_rejected_in_commitment (runtime : EventGraphRuntime graph)
    (state : PhaseRuntimeState graph)
    (bindingPhase : ∀ phase ∈ state.phases.head?, phase.kind = .commitment)
    (message : Message Player (CommitAttemptPacket graph))
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (call : message.payload.packet.call = .opening event candidate raw) :
    state.handle runtime message = none := by
  classical
  unfold handle
  split
  · rename_i admitted
    have allowed := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp admitted).1).2
    rw [allows, call] at allowed
    cases head : state.phases.head? with
    | none =>
        simp only [head] at allowed
        cases allowed
    | some phase =>
        simp only [head, Payload.event?, decide_eq_true_eq] at allowed
        have kind := bindingPhase phase head
        obtain ⟨lower, upper⟩ := (phase.mem_events event).mp allowed
        have matched := phase.fields event lower upper
        rw [kind] at matched
        obtain ⟨owner, payload, bindingKind⟩ := matched
        cases node : nodeView graph event with
        | sample ty law outputEq codeEq => cases outputEq.symm.trans bindingKind
        | resolve owner ty binding checks outputEq codeEq =>
            cases outputEq.symm.trans bindingKind
        | bind owner ty outputEq codeEq =>
            simp only [call, EventGraphRuntime.handle, node]
            split <;> simp
  · rfl

/-- Every packet step in an opaque commitment phase has the same optional
joint external observation under all-value hidden binding changes. Invalid and
stale authorization, rejected calls and final clean normalization are included. -/
theorem handle_opaque_external_congr (runtime : EventGraphRuntime graph)
    (left right : PhaseRuntimeState graph) (hidden : Player)
    (phases : left.phases = right.phases) (generation : left.generation = right.generation)
    (retired : left.retired.map (fun prior => (prior.attempt, prior.state.publicView)) =
      right.retired.map (fun prior => (prior.attempt, prior.state.publicView)))
    (publicEq : left.current.native.publicView = right.current.native.publicView)
    (views : ∀ who, who ≠ hidden →
      left.current.native.playerView who = right.current.native.playerView who)
    (leftClear : left.current.excluded = ∅) (rightClear : right.current.excluded = ∅)
    (bindingPhase : ∀ phase ∈ left.phases.head?, phase.kind = .commitment)
    (message : Message Player (CommitAttemptPacket graph)) :
    (left.handle runtime message).map (fun next => (next.publicView,
        fun who => if who = hidden then none else some (next.playerView who))) =
      (right.handle runtime message).map (fun next => (next.publicView,
        fun who => if who = hidden then none else some (next.playerView who))) := by
  have otherOpaque : ∀ phase ∈ right.phases.head?, phase.kind = .commitment := by
    rwa [← phases]
  cases call : message.payload.packet.call with
  | commitment event candidate =>
      exact handle_binding_external_congr runtime left right hidden phases generation retired
        publicEq views leftClear rightClear message event candidate call
  | malformed raw => simp only [handle, call, EventGraphRuntime.handle, Option.map_none, ite_self]
  | opening event candidate raw =>
      rw [opening_rejected_in_commitment runtime left bindingPhase message event candidate raw call,
        opening_rejected_in_commitment runtime right otherOpaque message event candidate raw call]

end Vegas.EventGraphRuntime.PhaseRuntimeState
