/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseOpeningMenuShape

/-! # Raw opening-packet shape of an actual counted submission -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A genuine publication request and an admitted nonsilent submission
determine its actual raw opening call. This projection needs no typed binding
reference, guard list, or candidate readback. -/
theorem submitted_opening_packet (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (event : graph.EventId) (payload : L.Ty)
    (publication : graph.outputLayout event = .publication payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : (app).Action) ∈
      (onePacketMenu runtime leaks bounds).actions owner (execution.recall owner)
        (execution.observe (app) owner)) :
    ∃ candidate raw, material.call.packet = .opening event candidate raw := by
  have member : (⟨some material⟩ : (app).Action) ∈ onePacketActions runtime leaks bounds owner
      (execution.recall owner) (execution.observe (app) owner) := offered
  have named := onePacket_event_of_request runtime leaks bounds plan ordered inputs horizon
    scheduler remaining owner execution trace ⟨execution.application.attempt, event⟩ request
      material member
  have permitted : permits ((app).outputs (execution.recall owner))
      (localEnvelope runtime leaks owner (execution.recall owner) (execution.observe (app) owner)
        material) = true := by
    rcases ((mem_onePacketActions runtime leaks bounds owner _ _ _).mp member).2 with
      impossible | ⟨other, transmitted, allowed⟩
    · cases impossible
    · cases Option.some.inj transmitted
      exact allowed
  have correct := ((permits_eq_true_iff _ _).mp permitted).2.1
  have callEq : (localEnvelope runtime leaks owner (execution.recall owner)
      (execution.observe (app) owner) material).payload.packet.call = material.call.packet :=
    maskPacket_call _ _
  cases call : material.call.packet with
  | malformed raw => rw [call] at named; cases named
  | commitment other candidate =>
      rw [call] at named
      have same : other = event := Option.some.inj named
      subst other
      simp only [CountCallCorrect, nativeMessage, callEq, call, bindingOwnedBy, publication,
        Bool.false_eq_true, false_and] at correct
  | opening other candidate raw =>
      rw [call] at named
      have same : other = event := Option.some.inj named
      subst other
      exact ⟨candidate, raw, rfl⟩

end Vegas.EventGraphRuntime.PhaseCount
