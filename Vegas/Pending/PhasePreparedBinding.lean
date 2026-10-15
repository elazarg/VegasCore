/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseCandidateSupply
import Vegas.Pending.PhaseCountMenu
import Vegas.Pending.ReactiveFiniteCompiler

/-! # Typed binding choices in the actual phased raw response menu

The fresh candidate is selected from the permanent physical catalogue. Every
source binding result, including accepted unusable bindings, is represented
without resampling or conditioning its value law.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- One physical submission registers a fresh typed result and emits its
handle. Failure here is an accepted unusable binding, distinct from silence. -/
def phaseBindingResponse (who : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat) :
    (phaseApplication runtime leaks).Action where
  transmission := some ⟨⟨.commitment event (who, .prepared serial), match result with
    | .failure => none
    | .success value => some ⟨payload, value⟩⟩, .none⟩

/-- The actual post-response catalogue has exactly the submitted result,
including failure, without changing the physical namespace. -/
theorem phaseBindingResponse_result (execution : (phaseApplication runtime leaks).Execution)
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat)
    (fresh : execution.application.current.native.candidates.lookup (who, .prepared serial) =
      .fresh) :
    let next := execution.respond (phaseApplication runtime leaks) who
      (phaseBindingResponse runtime leaks who event payload result serial)
    next.application.current.native.bindingResult (who, .prepared serial) payload = result := by
  cases result with
  | failure =>
      change (submitStep execution.application.current.native who
        (.commitment event (who, .prepared serial))).bindingResult _ _ = _
      rw [submitStep_bindingResult]
      simp only [State.bindingResult, fresh]
  | success value =>
      change (submitStep
        (Submission.register ⟨.commitment event (who, .prepared serial), some ⟨payload, value⟩⟩
          execution.application.current.native who) who
            (.commitment event (who, .prepared serial))).bindingResult
              (who, .prepared serial) payload = .success value
      simp only [Submission.register, ↓reduceIte]
      rw [submitStep_bindingResult]
      simp only [State.bindingResult, CommitmentCandidates.lookup_prepare_self,
        fresh, Raw.as?_mk, Option.elim_some]

/-- Sampling any original typed source law and performing its actual response
retains that law exactly in the persistent candidate catalogue. -/
theorem phaseBindingResponse_result_law
    (execution : (phaseApplication runtime leaks).Execution)
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (law : PMF (PublicationResult (L.Val payload))) (serial : Nat)
    (fresh : execution.application.current.native.candidates.lookup (who, .prepared serial) =
      .fresh) :
    (law.map (phaseBindingResponse runtime leaks who event payload · serial)).map
      (fun response =>
        let next := execution.respond (phaseApplication runtime leaks) who response
        next.application.current.native.bindingResult (who, .prepared serial) payload) = law := by
  rw [PMF.map_comp]
  calc
    _ = law.map id := by
      apply congrArg (fun f => law.map f)
      funext result
      exact phaseBindingResponse_result runtime leaks execution who event payload result serial
        fresh
    _ = law := PMF.map_id _

section FiniteMenu

variable [Fintype Player] (bounds : MessageBounds graph)

theorem phaseBindingResponse_available (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (result : PublicationResult (L.Val payload)) (serial : Nat)
    (bounded : serial < bounds.candidateCount) :
    phaseBindingResponse runtime leaks who event payload result serial ∈
      (PhaseCount.rawMenu runtime leaks bounds).actions who past view := by
  rw [PhaseCount.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  change (⟨⟨.commitment event (who, .prepared serial), _⟩, .none⟩ : WitnessedSubmission graph) ∈ _
  rw [bounds.submissions_mem]
  refine ⟨⟨bounded, ?_⟩, trivial⟩
  cases result with
  | failure => trivial
  | success value => exact values value

/-- Every actual active physical history has a bounded fresh prepared slot
representing every source result. Earlier arbitrary raw actions and rollback
are accounted for by the actual response-count and catalogue invariants. -/
theorem exists_phaseBindingResponse_of_history
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount)
    (control : (phaseApplication runtime leaks).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control)) (who : Player) (active : control.actor = some who)
    (event : graph.EventId) (payload : L.Ty)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    ∃ serial, serial < horizon ∧ ∀ result : PublicationResult (L.Val payload),
      phaseBindingResponse runtime leaks who event payload result serial ∈
        (PhaseCount.rawMenu runtime leaks bounds).actions who (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who) ∧
      let next := control.execution.respond (phaseApplication runtime leaks) who
        (phaseBindingResponse runtime leaks who event payload result serial)
      next.application.current.native.bindingResult (who, .prepared serial) payload = result := by
  have raw := menu.toRawTrace (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  obtain ⟨serial, bounded, selected⟩ := PhaseCandidates.reactiveFreshSlot_lt_horizon runtime leaks
    plan inputs horizon scheduler control raw who active
  refine ⟨serial, bounded, fun result => ⟨?_, ?_⟩⟩
  · exact phaseBindingResponse_available runtime leaks bounds who _ _ event payload values
      result serial (bounded.trans_le capacity)
  · exact phaseBindingResponse_result runtime leaks control.execution who event payload result
      serial (reactiveFreshSlot_spec _ serial selected)

end FiniteMenu
end Vegas.EventGraphRuntime
