/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedCalendar
import Vegas.Pending.EventPublicState

/-! # Actual local seed requests activate the selected source event

Reveal-relaxed ordering makes a ready owned event its owner's unique current
turn. This discharges event attribution for the actual activate-owner command;
the command itself contains only the owner identifier.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every genuine operational query names the unique event served when its
reply activates the owner, including a newly installed retry attempt. -/
theorem request_ownTurn (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (execution : (app).Execution) {inputs : graph.Inputs}
    (valid : execution.application.Invariant inputs) (ordered : graph.RevealRelaxedOrdered)
    {coordinate : PhaseSeedAddress graph} {query : PhaseSeedOperationalInput graph}
    (requested : (controller runtime leaks delay bound priority).request rest
      execution.environmentRecall (execution.observeEnvironment app) = some (coordinate, query)) :
    ∃ owner, execution.application.SeedRequest owner coordinate.1 ∧
      execution.application.current.native.publicView.ownTurn? owner = some coordinate.1.event := by
  obtain ⟨owner, request⟩ := request_sound runtime leaks delay bound priority rest execution
    valid requested
  refine ⟨owner, request, ?_⟩
  apply PublicView.ownTurn?_of_ownTurn
  exact State.ownTurn_of_ready execution.application.current.native ordered owner
    coordinate.1.event
    ((execution.application.current.native.publicView_eventReady coordinate.1.event).mpr
      request.2.2.1) request.2.2.2.1

end Vegas.EventGraphRuntime.PhaseSeedCalendar
