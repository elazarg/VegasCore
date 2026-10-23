/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseValueSwap

/-! # Actual phased application operations under the existing hidden swap -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace RecoveryState

omit [DecidableEq Player] in
/-- Public disclosure failure is fixed even when private binding data changes. -/
theorem publicationFailed_swap (swap : HiddenSwap graph) (native : State graph)
    (event : graph.EventId) :
    publicationFailed (native.swap swap) event = publicationFailed native event := by
  cases node : nodeView graph event with
  | bind => simp only [publicationFailed, node]
  | sample => simp only [publicationFailed, node]
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [publicationFailed, node, State.swap, Config.swap,
        swap.values.value_public (.inr event)
          (show (graph.outputLayout event).IsPublic by rw [outputEq]; trivial),
        Option.map_id, id_eq]

/-- An accepted unusable binding remains latent; public exclusion changes in
exactly the same way under a hidden swap. -/
theorem inclusionResult_swap (swap : HiddenSwap graph) (state : RecoveryState graph)
    (call : Payload graph) (native : State graph) :
    (state.swap swap).inclusionResult call (native.swap swap) =
      (state.inclusionResult call native).swap swap := by
  cases call <;> simp only [inclusionResult, publicationFailed_swap, RecoveryState.swap]

theorem submit_swap (swap : HiddenSwap graph) (state : RecoveryState graph) (who : Player)
    (submission : WitnessedSubmission graph) :
    (state.swap swap).submit who (submission.swap swap) = (state.submit who submission).swap swap :=
    by
  exact congrArg (fun native => RecoveryState.mk native state.excluded)
    (submission.submit_swap swap state.native who)

theorem emit_swap (swap : HiddenSwap graph) (state : RecoveryState graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph))) (submission : WitnessedSubmission graph)
    (fixed : submission.evidence.FixedBy swap) :
    (state.swap swap).emit who known (submission.swap swap) = state.emit who known submission := by
  unfold emit
  simp only [RecoveryState.swap_native]
  rw [WitnessedSubmission.emit_swap swap submission state.native who known fixed]
  rfl

end RecoveryState

namespace PhaseRuntimeState

omit [DecidableEq Player] in
@[simp] theorem swap_allows (swap : HiddenSwap graph) (state : PhaseRuntimeState graph)
    (call : Payload graph) : (state.swap swap).allows call = state.allows call := rfl

omit [DecidableEq Player] in
@[simp] theorem swap_commandAllowed (swap : HiddenSwap graph) (state : PhaseRuntimeState graph)
    (command : EnvironmentCommand graph) :
    (state.swap swap).commandAllowed command = state.commandAllowed command := rfl

/-- Physical submission changes the same permanent candidate slot under swap. -/
theorem submit_swap (swap : HiddenSwap graph) (state : PhaseRuntimeState graph) (who : Player)
    (submission : WitnessedSubmission graph) :
    (state.swap swap).submit who (submission.swap swap) = (state.submit who submission).swap swap :=
    by
  change ({ state.swap swap with current :=
    (state.current.swap swap).submit who (submission.swap swap) } : PhaseRuntimeState graph) = _
  rw [RecoveryState.submit_swap]
  rfl

/-- The complete emitted attempt-tagged packet is identical, including token,
identifier data and requested opening evidence. -/
theorem emit_swap (swap : HiddenSwap graph) (state : PhaseRuntimeState graph) (who : Player)
    (known : List (Message Player (CommitAttemptPacket graph)))
    (submission : WitnessedSubmission graph) (fixed : submission.evidence.FixedBy swap) :
    (state.swap swap).emit who known (submission.swap swap) = state.emit who known submission := by
  unfold emit
  simp only [PhaseRuntimeState.swap_current]
  rw [RecoveryState.emit_swap swap state.current who _ submission fixed]
  rfl

/-- The real handler, local drain, rollback and saved checkpoint all commute
with one native hidden swap under the native binding and disclosure guards. -/
theorem handle_swap (runtime : EventGraphRuntime graph) (swap : HiddenSwap graph)
    (state : PhaseRuntimeState graph) (message : Message Player (CommitAttemptPacket graph))
    (expiry : ∀ event, swap.values.ExpiryFixed event)
    (compatible : message.payload.tokenValid state.attempt = true → ∀ next event candidate,
      EventGraphRuntime.handle runtime state.current.native
        ⟨message.id, message.payload.packet.call⟩ = some next →
      message.payload.packet.call = .commitment event candidate →
        BindCompatible swap event candidate)
    (fixed : message.payload.tokenValid state.attempt = true → ∀ event,
      (∃ candidate raw, message.payload.packet.call = .opening event candidate raw) →
      state.current.native.config.cut.Ready event → RevealFixed swap state.current.native event) :
    (state.swap swap).handle runtime message = (state.handle runtime message).map
      (PhaseRuntimeState.swap swap) := by
  unfold handle
  change (if message.payload.tokenValid state.attempt && state.allows message.payload.packet.call &&
      !state.current.excludedCall message.payload.packet.call then _ else _) = _
  split
  · rename_i allowed
    have valid := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).1
    simp only [PhaseRuntimeState.swap_current, RecoveryState.swap_native]
    rw [EventGraphRuntime.handle_swap runtime swap state.current.native
      ⟨message.id, message.payload.packet.call⟩ (compatible valid) (fixed valid),
      Option.map_map, Option.map_map]
    congr 1
    funext native
    have updated : ({ state.swap swap with current :=
        (state.current.swap swap).inclusionResult message.payload.packet.call (native.swap swap) } :
          PhaseRuntimeState graph) =
        ({ state with current :=
          state.current.inclusionResult message.payload.packet.call native } :
          PhaseRuntimeState graph).swap swap := by
      rw [RecoveryState.inclusionResult_swap]
      rfl
    simp only [Function.comp_apply]
    rw [updated, normalize_swap swap _ expiry]
  · rfl

end PhaseRuntimeState
end Vegas.EventGraphRuntime
