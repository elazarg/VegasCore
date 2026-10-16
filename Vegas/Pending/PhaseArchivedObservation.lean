/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ArchiveBindingRecord
import Vegas.Pending.PhaseArchivedBindingInterval
import Vegas.Pending.PhaseArchivedRecall

/-! # Whole archived own action words from the actual player observation -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhasePublicView

/-- Insert the publicly archived binding attempts into the current private
own action word. Only the owner's permanent catalogue interprets hidden handles. -/
def archivedOwnHistory (view : PhasePublicView graph) (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (effective : List graph.Completion) : List graph.Completion :=
  view.retired.foldr (fun record word =>
    word.filter (fun completion => completion.event.val < record.1.phase) ++
      record.2.bindingHistory who candidates record.1.phase ++
      word.filter (fun completion => record.1.phase ≤ completion.event.val)) effective

end PhasePublicView

namespace PhaseRuntimeState

omit [DecidableEq Player] in
/-- The archived suffix lies entirely in its named commitment interval. -/
theorem RetiredBindingInterval.binding_fields
    {retired : List (RetiredCommitAttempt graph)} (valid : RetiredBindingInterval retired)
    (record : RetiredCommitAttempt graph) (member : record ∈ retired)
    (completion : graph.Completion) (recorded : completion ∈ record.state.config.history)
    (lower : record.attempt.phase ≤ completion.event.val) (who : Player)
    (acting : graph.actor? completion.event = some who) :
    ∃ payload, graph.outputLayout completion.event = .binding who payload := by
  obtain ⟨phase, address, kind, closed⟩ := valid record member
  have completed : completion.event ∈ record.state.config.cut.completed :=
    (record.state.config.history_exact completion.event).mp (List.mem_map.mpr
      ⟨completion, recorded, rfl⟩)
  have upper := (closed.2 completion.event).mp completed
  have inside := phase.fields completion.event (by simpa only [← address] using lower) upper
  rw [kind] at inside
  obtain ⟨owner, payload, binding⟩ := inside
  have same := Option.some.inj ((graph.actor?_of_outputLayout_binding binding).symm.trans acting)
  subst owner
  exact ⟨payload, binding⟩

private theorem archivedHistory_readout (retired : List (RetiredCommitAttempt graph))
    (effective : List graph.Completion) (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (read : ∀ record ∈ retired,
      record.state.publicView.bindingHistory who candidates record.attempt.phase =
        graph.ownCompletions who (record.state.config.history.filter fun completion =>
          record.attempt.phase ≤ completion.event.val)) :
    (retired.map fun record => (record.attempt, record.state.publicView)).foldr
        (fun record word =>
          word.filter (fun completion => completion.event.val < record.1.phase) ++
            record.2.bindingHistory who candidates record.1.phase ++
            word.filter (fun completion => record.1.phase ≤ completion.event.val))
        (graph.ownCompletions who effective) =
      graph.ownCompletions who (archivedHistory retired effective) := by
  induction retired with
  | nil => rfl
  | cons record remaining ih =>
      have recordRead := read record (List.mem_cons_self ..)
      have tailRead : ∀ other ∈ remaining,
          other.state.publicView.bindingHistory who candidates other.attempt.phase =
            graph.ownCompletions who
              (other.state.config.history.filter fun completion =>
                other.attempt.phase ≤ completion.event.val) :=
        fun other member => read other (List.mem_cons_of_mem record member)
      simp only [List.map_cons, List.foldr_cons]
      rw [recordRead, ih tailRead]
      simp only [archivedHistory, List.foldr_cons, RetiredCommitAttempt.insertHistory,
        EventGraph.ownCompletions, List.filter_append, List.filter_filter]
      simp only [Bool.and_comm]

/-- The entire recovered native own word is determined by the archived public
views, current own action word and permanent private candidate catalogue. -/
theorem archivedHistory_observed (state : PhaseRuntimeState graph) (who : Player)
    (bindings : RetiredBindings state.current.native state.retired)
    (intervals : RetiredBindingInterval state.retired) :
    state.publicView.archivedOwnHistory who (state.current.native.playerView who).candidates
        (graph.playerObserve who state.current.native.config).ownActions =
      graph.ownCompletions who
        (archivedHistory state.retired state.current.native.config.history) := by
  have read : ∀ record ∈ state.retired,
      record.state.publicView.bindingHistory who (state.current.native.playerView who).candidates
        record.attempt.phase = graph.ownCompletions who
          (record.state.config.history.filter fun completion =>
            record.attempt.phase ≤ completion.event.val) := by
    intro record member
    obtain ⟨valid, ⟨inputs, native⟩, fixed⟩ := bindings record member
    exact valid.bindingHistory_eq native.reachable fixed who record.attempt.phase
      (fun completion recorded lower acting =>
        intervals.binding_fields record member completion recorded lower who acting)
  exact archivedHistory_readout state.retired state.current.native.config.history who
    (state.current.native.playerView who).candidates read

end PhaseRuntimeState

/-- Every actual initialized raw history exposes its entire archived own native
word in the original full player observation, without revealing foreign values. -/
theorem phaseArchivedHistory_observed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (who : Player) :
    control.execution.application.publicView.archivedOwnHistory who
        (control.execution.application.current.native.playerView who).candidates
        ((graph.playerObserve who control.execution.application.current.native.config).ownActions) =
      graph.ownCompletions who (PhaseRuntimeState.archivedHistory
        control.execution.application.retired
        control.execution.application.current.native.config.history) :=
  PhaseRuntimeState.archivedHistory_observed _ who
    (phaseRetiredBindings_history runtime leaks plan inputs horizon scheduler trace)
    (phaseRetiredBindingInterval_history runtime leaks plan inputs horizon scheduler trace)

end Vegas.EventGraphRuntime
