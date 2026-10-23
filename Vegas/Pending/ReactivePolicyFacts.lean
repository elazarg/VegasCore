/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactivePolicy

/-! # Prescribed submissions, recovery choices, and initialized law equality -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveResolutionPacket_event {owner : Player} (who : Player) (event : graph.EventId)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : PlayerView graph) (packet : Payload graph)
    (sent : reactiveResolutionPacket who event payload binding checks outputEq action view =
      some packet) :
    packet.event? graph = some event := by
  dsimp only [reactiveResolutionPacket] at sent
  repeat' split at sent
  all_goals first
    | cases sent; rfl
    | cases sent

end Vegas.EventGraphRuntime
