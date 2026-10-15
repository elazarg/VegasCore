/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingCountTransport

/-! # Reusing live physical repair data at a saved semantic checkpoint -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- Physical recall, receipts and packets come from the live frame. Replacing
only its application state requires precisely the saved private observations,
freshness and successful-store refinement already carried at that checkpoint. -/
theorem checkpointFrame
    (live : BindingMemory.Frame runtime leaks memory owner original repaired)
    (left right : State graph)
    (observed : memory.shadow.view (right.playerView owner) = left.playerView owner)
    (foreignViews : ∀ who, who ≠ owner → left.playerView who = right.playerView who)
    (slots : ∀ query, left.candidates.lookup (owner, query) = .fresh ↔
      right.candidates.lookup (owner, query) = .fresh)
    (successful : left.config.store.BindingRefines right.config.store) :
    BindingMemory.Frame runtime leaks memory owner
      { original with application := left } { repaired with application := right } := by
  refine ⟨live.past, ?_, live.lengths, live.network, live.service,
    foreignViews, live.recall, slots, successful, live.submissions⟩
  change (⟨repaired.network.observe owner, memory.shadow.view (right.playerView owner),
    repaired.receipts⟩ : (runtime.reactiveApplication leaks).PlayerView) =
      ⟨original.network.observe owner, left.playerView owner, original.receipts⟩
  rw [observed, live.network, live.receipts]

end Vegas.EventGraphRuntime.PhaseBindingRepair
