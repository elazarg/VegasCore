/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveBindingFrameOpening

/-! # Response windows in the actual repaired implementation

Finite activation windows use the existing scheduler and passive observation
rule. Original own responses are silent in this segment; foreign
responses remain arbitrary. Complete private recall is retained on both sides.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

theorem foreign_observed (frame : Frame runtime leaks memory owner original repaired)
    (actor : Player) (different : actor ≠ owner) :
    original.observe (runtime.reactiveApplication leaks) actor =
      repaired.observe (runtime.reactiveApplication leaks) actor := by
  let app := runtime.reactiveApplication leaks
  change (⟨original.network.observe actor, app.observePlayer original.application actor,
    original.receipts⟩ : app.PlayerView) =
      ⟨repaired.network.observe actor, app.observePlayer repaired.application actor,
        repaired.receipts⟩
  rw [frame.network, frame.receipts]
  exact congrArg (fun current => (⟨repaired.network.observe actor, current,
    repaired.receipts⟩ : app.PlayerView)) (frame.views actor different)

end Vegas.EventGraphRuntime.BindingMemory.Frame
