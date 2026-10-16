/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ArchiveBindingRecord
import Vegas.Pending.PhaseArchivedInputs
import Vegas.Pending.CompletedBindingReadback

/-! # Retired private field observations from permanent owned candidates -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PublicView

/-- Recover an old owner-masked store. Initial private fields are immutable;
retired public fields are already public, and hidden owned bindings are read
from accepted handles using only the owner's permanent candidate catalogue. -/
def recoverPlayerStore (view : PublicView graph) (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (current : Store graph.layout) : Store graph.layout := fun field =>
  match field with
  | .inl input => current (.inl input)
  | .inr event =>
      match nodeView graph event with
      | .bind owner payload outputEq _ =>
          if owner = who then
            if event ∈ view.observation.completionOrder then
              cast (congrArg (fun kind => Option kind.Value) outputEq.symm)
                (some ((view.accepted (.inr event)).elim .failure
                  (fun handle => candidateResult (candidates handle.2) payload)))
            else none
          else none
      | .resolve .. | .sample .. => view.observation.store (.inr event)

end PublicView

namespace State

/-- A later owner catalogue interprets every accepted archived binding exactly
as it was interpreted at the archived image, including unusable accepted handles. -/
private theorem BindingInvariant.accepted_result_current {state current : State graph}
    (valid : state.BindingInvariant) (fixed : KeepsFixedCandidates state current)
    (event : graph.EventId) (who : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding who payload) :
    (state.accepted (.inr event)).elim .failure
        (fun handle => state.bindingResult handle payload) =
      (state.accepted (.inr event)).elim .failure
        (fun handle => candidateResult ((current.playerView who).candidates handle.2) payload) := by
  cases accepted : state.accepted (.inr event) with
  | none => rfl
  | some candidate =>
      obtain ⟨ty, typed⟩ := valid.accepted_typed (.inr event) candidate accepted
      have owned : candidate.1 = who :=
        (EventField.binding.inj (typed.symm.trans binding)).1
      simp only [Option.elim_some, State.bindingResult_eq]
      rw [← fixed candidate (valid.accepted_fixed (.inr event) candidate accepted)]
      change candidateResult (current.candidates.lookup candidate) payload =
        candidateResult (current.candidates.lookup (who, candidate.2)) payload
      rw [← owned]

/-- The full archived masked store is determined by the public archived image,
the current private initial fields, and the permanent owned candidate catalogue. -/
theorem BindingInvariant.recoverPlayerStore_eq {state current : State graph}
    (valid : state.BindingInvariant) (fixed : KeepsFixedCandidates state current)
    (inputs : state.config.inputs = current.config.inputs) (who : Player) :
    state.publicView.recoverPlayerStore who (current.playerView who).candidates
        (graph.playerObserve who current.config).store =
      (graph.playerObserve who state.config).store := by
  funext field
  cases field with
  | inl input =>
      change graph.playerStore who current.config.store (.inl input) =
        graph.playerStore who state.config.store (.inl input)
      unfold EventGraph.playerStore
      split
      · change some (current.config.inputs input) = some (state.config.inputs input)
        rw [inputs]
      · rfl
  | inr event =>
      cases descriptor : nodeView graph event with
      | bind owner payload outputEq codeEq =>
          by_cases same : owner = who
          · subst owner
            have visible : graph.fieldVisibleTo who (.inr event) := by
              change (graph.outputLayout event).VisibleTo who
              rw [outputEq]
              rfl
            rw [show (graph.playerObserve who state.config).store (.inr event) =
              state.config.outputs event from graph.playerStore_of_visible who
                state.config.store (.inr event) visible]
            simp only [PublicView.recoverPlayerStore, descriptor, ↓reduceIte]
            have completed : event ∈ state.publicView.observation.completionOrder ↔
                event ∈ state.config.cut.completed := state.config.history_exact event
            by_cases present : event ∈ state.config.cut.completed
            · rw [ite_eq_left (completed.mpr present)]
              let ref : FieldRef graph.layout (.binding who payload) := ⟨.inr event, outputEq⟩
              have read := valid.binding_read ref event rfl present
              rw [valid.accepted_result_current fixed event who payload outputEq] at read
              have recovered := congrArg
                (cast (congrArg (fun kind => Option kind.Value) outputEq.symm)) read
              dsimp only [FieldRef.get?, ref] at recovered
              simp only [cast_cast, cast_eq] at recovered
              exact recovered.symm
            · rw [ite_eq_right (fun member => present (completed.mp member))]
              have absent : state.config.outputs event = none := by
                cases output : state.config.outputs event with
                | none => rfl
                | some value =>
                    exact (present ((state.config.output_available event).mp
                      (by rw [output]; rfl))).elim
              exact absent.symm
          · have hidden : ¬ graph.fieldVisibleTo who (.inr event) := by
              change ¬ (graph.outputLayout event).VisibleTo who
              rw [outputEq]
              exact same
            simp only [PublicView.recoverPlayerStore, descriptor, same, ↓reduceIte]
            exact (graph.playerStore_of_hidden who state.config.store (.inr event) hidden).symm
      | resolve owner payload ref checks outputEq codeEq =>
          have visible : graph.fieldVisibleTo who (.inr event) := by
            change (graph.outputLayout event).VisibleTo who
            rw [outputEq]
            trivial
          have publicField : graph.fieldPublic (.inr event) := by
            change (graph.outputLayout event).IsPublic
            rw [outputEq]
            trivial
          simp only [PublicView.recoverPlayerStore, descriptor, State.publicView,
            EventGraph.publicObserve, EventGraph.playerObserve]
          rw [graph.publicStore_of_public _ _ publicField,
            graph.playerStore_of_visible _ _ _ visible]
      | sample payload law outputEq codeEq =>
          have visible : graph.fieldVisibleTo who (.inr event) := by
            change (graph.outputLayout event).VisibleTo who
            rw [outputEq]
            trivial
          have publicField : graph.fieldPublic (.inr event) := by
            change (graph.outputLayout event).IsPublic
            rw [outputEq]
            trivial
          simp only [PublicView.recoverPlayerStore, descriptor, State.publicView,
            EventGraph.publicObserve, EventGraph.playerObserve]
          rw [graph.publicStore_of_public _ _ publicField,
            graph.playerStore_of_visible _ _ _ visible]

end State

/-- At every authentic initialized raw history, each retired masked store has
this exact reconstruction from the original current player observation. -/
theorem phaseArchivedPlayerStore_observed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (record : RetiredCommitAttempt graph) (member : record ∈ control.execution.application.retired)
    (who : Player) :
    record.state.publicView.recoverPlayerStore who
        (control.execution.application.current.native.playerView who).candidates
        ((graph.playerObserve who control.execution.application.current.native.config).store) =
      (graph.playerObserve who record.state.config).store := by
  obtain ⟨binding, _native, fixed⟩ :=
    phaseRetiredBindings_history runtime leaks plan inputs horizon scheduler trace record member
  have original := phaseRetiredInputs_history runtime leaks plan inputs horizon scheduler trace
    record member
  exact binding.recoverPlayerStore_eq fixed original who

/-- Equal actual player observations determine every retired masked store,
including private owned results in voided attempts. -/
theorem phaseArchivedPlayerStores_eq_of_observed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {first second}
    (firstTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some first))
    (secondTrace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some second))
    (who : Player)
    (observed : first.execution.observe (phaseApplication runtime leaks) who =
      second.execution.observe (phaseApplication runtime leaks) who) :
    first.execution.application.retired.map (fun record =>
        (record.attempt, (graph.playerObserve who record.state.config).store)) =
      second.execution.application.retired.map (fun record =>
        (record.attempt, (graph.playerObserve who record.state.config).store)) := by
  let recover : (phaseApplication runtime leaks).PlayerView →
      List (CommitAttemptId × Store graph.layout) := fun view =>
    view.application.2.retired.map fun record =>
      (record.1, record.2.recoverPlayerStore who view.application.1.candidates
        view.application.1.observation.store)
  have read {control}
      (trace : ((phaseApplication runtime leaks).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
      recover (control.execution.observe (phaseApplication runtime leaks) who) =
        control.execution.application.retired.map (fun record =>
          (record.attempt, (graph.playerObserve who record.state.config).store)) := by
    change (control.execution.application.retired.map
      (fun record => (record.attempt, record.state.publicView))).map _ = _
    rw [List.map_map]
    apply List.map_congr_left
    intro record member
    exact congrArg (fun store => (record.attempt, store))
      (phaseArchivedPlayerStore_observed runtime leaks plan inputs horizon scheduler trace
        record member who)
  exact (read firstTrace).symm.trans ((congrArg recover observed).trans (read secondTrace))

end Vegas.EventGraphRuntime
