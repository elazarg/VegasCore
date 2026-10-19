/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalNormalizationFrame
import Vegas.Pending.EventStore

/-! # Actual external anchors for raw states entering phase normalization -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The actual accepted packet, before automatic normalization, provides its
own origin frame. The signed envelope is retained even if this handler excludes
its author or records a failing guard. -/
theorem NormalizationFrame.inclusion (anchor : (app).Control)
    (origins : ExecutionOpeningOrigins runtime leaks anchor.execution)
    (message : Message Player (CommitAttemptPacket graph))
    (present : message ∈ anchor.execution.network.inputs)
    (result : EventGraphRuntime.State graph)
    (handled : EventGraphRuntime.handle runtime anchor.execution.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = some result) :
    NormalizationFrame runtime leaks anchor
      {anchor.execution.application with
        current := (anchor.execution.application.current.inclusionResult
          message.payload.packet.call result)} := by
  refine ⟨le_rfl, origins.2, origins.1.handle runtime message present result handled, ?_⟩
  intro _same
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro field value stored
  exact handle_store_of_some runtime anchor.execution.application.current.native result
    ⟨message.id, message.payload.packet.call⟩ handled field value stored

/-- The actual environment result supplies a frame before its automatic
normalization. Sampling and expiry disclose no new true publication action. -/
theorem NormalizationFrame.environment (anchor : (app).Control)
    (origins : ExecutionOpeningOrigins runtime leaks anchor.execution)
    (command : EnvironmentCommand graph) (result : EventGraphRuntime.State graph)
    (supported : result ∈ (environmentStep runtime
      anchor.execution.application.current.native command).support) :
    NormalizationFrame runtime leaks anchor
      {anchor.execution.application with
        current := (anchor.execution.application.current.environmentResult command result)} := by
  refine ⟨le_rfl, origins.2, origins.1.environment runtime command result supported, ?_⟩
  intro _same
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro field value stored
  exact environmentStep_store_of_some runtime anchor.execution.application.current.native result
    command supported field value stored

end Vegas.EventGraphRuntime.PhaseProposal
