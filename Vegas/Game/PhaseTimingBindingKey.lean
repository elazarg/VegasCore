/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingMemory
import Vegas.Pending.EventPublicState

/-! # The literal erased key at a genuine current binding callback -/

noncomputable section

namespace Vegas

open EventGraph EventGraphRuntime Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- At an actual ready binding, the timing key has no delivered opening value.
The owner-turn attribution is derived from the approved reveal-relaxed order. -/
theorem phaseDeliveredValue_eq_none_of_binding (ordered : graph.RevealRelaxedOrdered)
    (execution : (app).Execution) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩) :
    phaseDeliveredValue runtime leaks owner (execution.observe app owner) = none := by
  classical
  have turn : execution.application.current.native.publicView.ownTurn? owner = some event := by
    apply PublicView.ownTurn?_of_ownTurn
    exact State.ownTurn_of_ready _ ordered owner event
      ((execution.application.current.native.publicView_eventReady event).mpr request.2.2.1)
      request.2.2.2.1
  have observedTurn : (execution.observe app owner).application.2.native.ownTurn? owner =
      some event := turn
  unfold phaseDeliveredValue
  rw [observedTurn]
  cases node : nodeView graph event with
  | bind => simp only [node]
  | sample ty law outputEq codeEq => cases outputEq.symm.trans binding
  | resolve who ty bound checks outputEq codeEq => cases outputEq.symm.trans binding

/-- The actual complete key agrees for a current binding when its earlier
operational word agrees. This earlier-word equality is the chronological
induction invariant, not an information-fiber or posterior premise. -/
theorem phaseTimingKey_binding_memory (ordered : graph.RevealRelaxedOrdered)
    (memory : BindingShadow graph) (owner : Player) (owned : memory.OwnBindings owner)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (left right : (app).Execution)
    (application : left.application = memory.phased owner right.application)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (past : (left.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
      (right.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)))
    (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (request : right.application.SeedRequest owner ⟨right.application.attempt, event⟩) :
    phaseTimingKey runtime leaks owner (some (left.recall owner, left.observe app owner)) =
      phaseTimingKey runtime leaks owner (some (right.recall owner, right.observe app owner)) := by
  have firstRequest : left.application.SeedRequest owner ⟨left.application.attempt, event⟩ := by
    rw [application]
    exact request
  have firstDelivered := phaseDeliveredValue_eq_none_of_binding runtime leaks ordered left owner
    event payload binding firstRequest
  have secondDelivered := phaseDeliveredValue_eq_none_of_binding runtime leaks ordered right owner
    event payload binding request
  simp only [phaseTimingKey, firstDelivered, secondDelivered, past,
    phaseOperationalView_memory runtime leaks memory owner owned valid left right application
      network receipts]

end Vegas
