/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseBindingResponseWitness
import Vegas.Pending.PhaseBindingIdleMenu

/-! # Actual callback alternatives inside an opaque commitment phase -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A callback without an unsent current request has only the silent response.
This includes both absent requests and requests already represented in recall. -/
theorem onePacketActions_eq_singleton_of_no_unsent (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (absent : ¬∃ coordinate, execution.application.SeedRequest owner coordinate ∧
      ∀ message ∈ (app).outputs (execution.recall owner),
        event? message.payload ≠ some coordinate) :
    onePacketActions runtime leaks bounds owner (execution.recall owner)
      (execution.observe app owner) = {⟨none⟩} := by
  apply Finset.ext
  intro response
  constructor
  · intro offered
    apply Finset.mem_singleton.mpr
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some material =>
        obtain ⟨coordinate, request⟩ := onePacket_request_of_nonsilent runtime leaks bounds plan
          inputs horizon scheduler remaining owner execution trace material offered
        exact (absent ⟨coordinate, request, unsent_of_nonsilent runtime leaks bounds plan ordered
          inputs horizon scheduler remaining owner execution trace coordinate request material
            offered⟩).elim
  · intro silent
    rw [Finset.mem_singleton.mp silent]
    exact silence_onePacket runtime leaks bounds owner _ _

end Vegas.EventGraphRuntime.PhaseCount
