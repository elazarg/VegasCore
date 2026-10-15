/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseStoredCheckpoint
import Vegas.Pending.PhaseAcceptedOrder

/-! # Saved semantic invariants before physical phase normalization -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRuntimeState

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A real inclusion preserves the saved and live binding interpretations before
closure can retire the phase containing the newly completed output. -/
theorem BindingRecord.inclusionResult (runtime : EventGraphRuntime graph)
    (state : PhaseRuntimeState graph) (valid : state.BindingRecord)
    (message : Message Player (Payload graph)) (native : State graph)
    (handled : EventGraphRuntime.handle runtime state.current.native message = some native) :
    BindingRecord { state with current := state.current.inclusionResult message.payload native } :=
  ⟨valid.saved, handle_bindingInvariant runtime _ native message valid.active handled,
    fun candidate savedFixed => by
      have activeFixed : state.current.native.candidates.lookup candidate ≠ .fresh := by
        rw [valid.fixed candidate savedFixed]
        exact savedFixed
      exact (handle_lookup_of_not_fresh runtime _ native message candidate activeFixed
        handled).trans (valid.fixed candidate savedFixed)⟩

/-- Chance, clock and expiry retain the catalogue meaning of the saved checkpoint. -/
theorem BindingRecord.environmentResult (runtime : EventGraphRuntime graph)
    (state : PhaseRuntimeState graph) (valid : state.BindingRecord)
    (command : EnvironmentCommand graph) (native : State graph)
    (reached : native ∈ (environmentStep runtime state.current.native command).support) :
    BindingRecord { state with current := state.current.environmentResult command native } := by
  refine ⟨valid.saved,
    environmentStep_bindingInvariant runtime _ native command valid.active reached, ?_⟩
  intro candidate savedFixed
  change native.candidates.lookup candidate = state.entry.native.candidates.lookup candidate
  rw [(environmentStep_tables runtime _ native command reached).2]
  exact valid.fixed candidate savedFixed

/-- Stored checkpoint cells survive an actual inclusion before any closure. -/
theorem StoredCheckpoint.inclusionResult (runtime : EventGraphRuntime graph)
    (state : PhaseRuntimeState graph) (valid : state.StoredCheckpoint)
    (message : Message Player (Payload graph)) (native : State graph)
    (handled : EventGraphRuntime.handle runtime state.current.native message = some native) :
    StoredCheckpoint
      { state with current := state.current.inclusionResult message.payload native } := by
  intro field value present
  exact handle_store_of_some runtime _ native message handled field value
    (valid field value present)

/-- Stored checkpoint cells survive every actual environment result before closure. -/
theorem StoredCheckpoint.environmentResult (runtime : EventGraphRuntime graph)
    (state : PhaseRuntimeState graph) (valid : state.StoredCheckpoint)
    (command : EnvironmentCommand graph) (native : State graph)
    (reached : native ∈ (environmentStep runtime state.current.native command).support) :
    StoredCheckpoint { state with current := state.current.environmentResult command native } := by
  intro field value present
  exact environmentStep_store_of_some runtime _ native command reached field value
    (valid field value present)

end Vegas.EventGraphRuntime.PhaseRuntimeState

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (ordered : graph.RevealRelaxedOrdered) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

include ordered

/-- A real initialized history supplies all typed checkpoint evidence at a
permitted native inclusion endpoint, before closure can retire that endpoint. -/
theorem phase_inclusion_checkpoint_history {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (message : Message Player (Payload graph)) (native : State graph)
    (authorized : control.execution.application.allows message.payload = true)
    (notExcluded : control.execution.application.current.excludedCall message.payload = false)
    (handled : EventGraphRuntime.handle runtime control.execution.application.current.native
      message = some native) :
    let image := { control.execution.application with current :=
      control.execution.application.current.inclusionResult message.payload native }
    image.BindingRecord ∧ image.StoredCheckpoint ∧ image.ReceiptRecord := by
  exact ⟨(phaseBindingRecord_history runtime leaks plan inputs horizon scheduler
      trace).inclusionResult
      runtime _ message native handled,
    (phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler
      trace).inclusionResult
      runtime _ message native handled,
    (phaseReceiptRecord_history runtime leaks ordered plan inputs horizon scheduler
      trace).inclusionResult
      runtime _ message native authorized notExcluded handled ordered⟩

/-- Actual supported environment outcomes retain the same three checked
checkpoint invariants, including public omission and automatic exclusion. -/
theorem phase_environment_checkpoint_history {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (command : EnvironmentCommand graph) (native : State graph)
    (authorized : control.execution.application.commandAllowed command = true)
    (reached : native ∈ (environmentStep runtime
      control.execution.application.current.native command).support) :
    let image := { control.execution.application with current :=
      control.execution.application.current.environmentResult command native }
    image.BindingRecord ∧ image.StoredCheckpoint ∧ image.ReceiptRecord := by
  exact ⟨(phaseBindingRecord_history runtime leaks plan inputs horizon scheduler
      trace).environmentResult
      runtime _ command native reached,
    (phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler
      trace).environmentResult
      runtime _ command native reached,
    (phaseReceiptRecord_history runtime leaks ordered plan inputs horizon scheduler
      trace).environmentResult
      runtime _ command native authorized reached⟩

end Vegas.EventGraphRuntime
