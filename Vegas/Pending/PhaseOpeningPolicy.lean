/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseOpeningCoverage

/-! # Globally legal physical realization of local disclosure laws -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

local notation "app" => phaseApplication runtime leaks

open Classical in
/-- Evaluate a disclosure law using only the actual local input. A successful
surviving binding opens its accepted handle, subject to the complete raw menu. -/
def phaseOpeningPolicy (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (opens : List (app).PlayerEntry → (app).PlayerView → PMF Bool) : (app).Policy :=
  fun past view =>
    match binding.get? view.application.1.observation.store,
        view.application.1.publicView.accepted binding.field with
    | some (.success value), some candidate =>
        let opening := phaseOpeningResponse runtime leaks event candidate ⟨payload, value⟩
        if opening ∈ onePacketActions runtime leaks bounds owner past view then
          (opens past view).map fun disclose => if disclose then opening else ⟨none⟩
        else PMF.pure ⟨none⟩
    | _, _ => PMF.pure ⟨none⟩

/-- The complete opening component is legal at every input, including
unrealized or malformed local observations. -/
theorem phaseOpeningPolicy_covered (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (opens : List (app).PlayerEntry → (app).PlayerView → PMF Bool)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action)
    (supported : response ∈
      (phaseOpeningPolicy runtime leaks bounds owner event payload binding opens
        past view).support) :
    response ∈ onePacketActions runtime leaks bounds owner past view := by
  classical
  unfold phaseOpeningPolicy at supported
  split at supported
  · dsimp only at supported
    split at supported
    · rename_i value candidate _ _ allowed
      obtain ⟨disclose, _, rfl⟩ := PMF.support_map .. ▸ supported
      cases disclose
      · exact silence_onePacket runtime leaks bounds owner past view
      · exact allowed
    · cases (PMF.mem_support_pure_iff _ _).mp supported
      exact silence_onePacket runtime leaks bounds owner past view
  · cases (PMF.mem_support_pure_iff _ _).mp supported
    exact silence_onePacket runtime leaks bounds owner past view

/-- At an actual unsent ready site with a successful binding, the guarded
policy realizes exactly the requested Boolean disclosure law, without truncation. -/
theorem phaseOpeningPolicy_of_history
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall owner),
      event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (value : L.Val payload)
    (stored : binding.get? control.execution.application.current.native.config.store =
      some (.success value))
    (values : (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (opens : List (app).PlayerEntry → (app).PlayerView → PMF Bool) :
    ∃ candidate,
      control.execution.application.current.native.accepted binding.field = some candidate ∧
      phaseOpeningPolicy runtime leaks bounds owner event payload binding opens
          (control.execution.recall owner) (control.execution.observe app owner) =
        (opens (control.execution.recall owner) (control.execution.observe app owner)).map
          (fun disclose => if disclose then
            phaseOpeningResponse runtime leaks event candidate ⟨payload, value⟩ else ⟨none⟩) := by
  classical
  obtain ⟨candidate, accepted, _, _, available⟩ := phaseOpeningResponse_of_history
    runtime leaks bounds plan inputs horizon scheduler trace owner event payload binding checks
    outputEq codeEq node request unsent value stored values
  have localStored : binding.get?
      (control.execution.observe app owner).application.1.observation.store =
        some (.success value) := by
    change binding.get? (graph.playerStore owner
      control.execution.application.current.native.config.store) = _
    rw [binding.get?_playerStore owner _ (by simp only [EventField.VisibleTo]), stored]
  have localAccepted : (control.execution.observe app owner).application.1.publicView.accepted
      binding.field = some candidate := accepted
  refine ⟨candidate, accepted, ?_⟩
  unfold phaseOpeningPolicy
  rw [localStored, localAccepted]
  exact ite_eq_left available

end Vegas.EventGraphRuntime.PhaseCount
