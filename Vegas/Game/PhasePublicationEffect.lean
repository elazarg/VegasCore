/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseCountedOpeningSubmission

/-! # Counted publication responses retain the entire application state

Raw private material is still part of the action and recall. At an actual
publication request it cannot register a new candidate or change an accepted
binding: a nonsilent counted call is an opening, whose submission is inert.
-/

noncomputable section

namespace Vegas

open EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A genuine counted publication response changes the network and own recall,
but its submission preserves the full application state, including all private
candidate meanings, accepted handles, failure controls and semantic stores. -/
theorem phase_counted_publication_response_application
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (remaining : Nat) (owner : Player)
    (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (event : graph.EventId) (payload : L.Ty)
    (publication : graph.outputLayout event = .publication payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (action : (app).Action)
    (offered : action ∈ (PhaseCount.onePacketMenu runtime leaks bounds).actions owner
      (execution.recall owner) (execution.observe app owner)) :
    (execution.respond app owner action).application = execution.application := by
  cases action with
  | mk transmission =>
      cases transmission with
      | none => rfl
      | some material =>
          obtain ⟨candidate, raw, opening⟩ :=
            PhaseCount.submitted_opening_packet runtime leaks bounds plan ordered inputs horizon
              scheduler remaining owner execution trace event payload publication request material
              offered
          rcases material with ⟨⟨packet, preparation⟩, evidence⟩
          change packet = .opening event candidate raw at opening
          subst packet
          cases preparation <;> rfl

end Vegas
