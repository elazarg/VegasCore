/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCommitRecallWordOrder
import Vegas.Game.CommitPrefixReadyRecall

/-! # The actual current-attempt word is the completed source own history -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  {start finish : SourceCtx Player L} {startOpen finishOpen : Finset VarId}
  (block : CommitPrefix start startOpen finish finishOpen) (low generation : Nat)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (who : Player) (word : DecisionView who finish)

local notation "app" => phaseApplication runtime leaks

/-- Filling only hidden foreign cells appends precisely the actual current
attempt's parsed raw sends to the saved source history. The compiler action
identity and saved frontier are structural checkpoint facts; no desired word
identity or observation-likelihood premise is supplied. -/
theorem phaseCommitRecallWord_fill_history
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (earlier : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (earlier.prepend suffix))
    (rank : ∀ index, (embedding.event index).val = low + index.val)
    (entryNative : EventGraphRuntime.State (serviceGraph setup mode))
    (entry : SourceProgram.Config Player L Γ)
    (retained : entryNative.config.history.IsPrefix
      control.execution.application.current.native.config.history)
    (saved : entryNative.config.cut.IsPrefix low)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (earlier.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (selected : Fin (eventCount (earlier.prepend suffix))) (atEnd : selected.val = earlier.length)
    (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout (embedding.event selected) =
      .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, embedding.event selected⟩)
    (inside : low ≤ (embedding.event selected).val ∧
      (embedding.event selected).val < low + block.length)
    (address : control.execution.application.attempt = ⟨low, generation⟩)
    (consistent : (phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed assessment
      block low generation slotWeight slotNonnegative slotBounded who word).Consistent
        (control.execution.recall who)) :
    (fillCommitPrefix setup.program earlier suffix embedding
      control.execution.application.current.native.config.store entry).history who =
      entry.history who ++ phaseCommitRecallWord setup.program mode runtime leaks low
        (low + earlier.length) generation (control.execution.recall who) := by
  classical
  let graph := serviceGraph setup mode
  let native := control.execution.application.current.native
  let raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  obtain ⟨_draw, invariant⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler raw
  have reachable := invariant.active.reachable
  have valid := (phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw).active
  let ordered := serviceGraph_revealRelaxedOrdered setup mode
  have high : (embedding.event selected).val = low + earlier.length := by rw [rank, atEnd]
  have own (event : graph.EventId) (actor : graph.actor? event = some who) :
      event ∈ native.config.cut.completed ↔ event.val < low + earlier.length := by
    have ready := ordered.ready_visible_iff native.config.cut request.2.2.1 request.2.2.2.1
      (EventCode.output_visible_of_actor (graph.nodes event) who actor)
      (IndependentReveals.not_of_actor_eq (by rw [actor, request.2.2.2.1]))
      (IndependentReveals.not_of_actor_eq (by rw [actor, request.2.2.2.1]))
    rwa [high] at ready
  have completedOwn : ∀ index : Fin (eventCount (earlier.prepend suffix)),
      index.val < earlier.length → graph.actor? (embedding.event index) = some who →
        embedding.event index ∈ native.config.cut.completed := by
    intro index before actor
    apply (own _ actor).mpr
    rw [rank]
    omega
  have boundedOwn : ∀ event ∈ native.config.cut.completed, graph.actor? event = some who →
      event.val < low + earlier.length := by
    intro event done actor
    exact (own event actor).mp done
  have original := fillCommitPrefix_history setup.program mode earlier suffix embedding native
    entry valid who completedOwn actions
  have ownWord := commitAttemptCompletions_ownRecall setup.program mode earlier suffix embedding low
    rank entryNative native valid reachable retained saved who completedOwn boundedOwn
  let records : List graph.Completion :=
    (commitAttemptCompletions setup.program mode earlier suffix embedding native).map
    ((toEventGraph setup.program).toModeCompletion mode)
  let interval := fun completion : graph.Completion =>
    decide (low ≤ completion.event.val ∧ completion.event.val < low + earlier.length)
  have oldGone : (graph.ownCompletions who entryNative.config.history).filter interval = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro completion member
    have recorded := (List.mem_filter.mp member).1
    have done := (entryNative.config.history_exact completion.event).mp
      (List.mem_map.mpr ⟨completion, recorded, rfl⟩)
    have below := (saved.2 completion.event).mp done
    intro included
    have bounds : low ≤ completion.event.val ∧
        completion.event.val < low + earlier.length := of_decide_eq_true included
    exact (Nat.not_lt_of_ge bounds.1) below
  have newKept : (graph.ownCompletions who records).filter interval =
      graph.ownCompletions who records := by
    apply List.filter_eq_self.mpr
    intro completion member
    have recorded := (List.mem_filter.mp member).1
    obtain ⟨source, present, rfl⟩ := List.mem_map.mp recorded
    obtain ⟨index, before, named⟩ :=
      (commitAttemptCompletions_event_mem setup.program mode earlier suffix embedding native
        source.event).mp (List.mem_map.mpr ⟨source, present, rfl⟩)
    have position := rank index
    rw [named] at position
    simp only [interval, toModeCompletion, decide_eq_true_eq]
    omega
  have filtered : (graph.ownCompletions who native.config.history).filter interval =
      graph.ownCompletions who records := by
    change graph.ownCompletions who native.config.history =
      graph.ownCompletions who (entryNative.config.history ++ records) at ownWord
    have split : graph.ownCompletions who (entryNative.config.history ++ records) =
        graph.ownCompletions who entryNative.config.history ++
          graph.ownCompletions who records := List.filter_append _ _
    rw [ownWord, split, List.filter_append, oldGone, List.nil_append, newKept]
  have actual := phaseCommitRecallWord_eq_completed mode setup runtime leaks bounds wellFormed
    assessment block low generation slotWeight slotNonnegative slotBounded who word plan maximal
      inputs horizon scheduler trace clear (embedding.event selected) payload binding request inside
        address consistent
  rw [high] at actual
  change phaseCommitRecallWord setup.program mode runtime leaks low (low + earlier.length)
    generation (control.execution.recall who) = decodeCompletions setup.program
      (((graph.ownCompletions who native.config.history).filter interval).map
        ((toEventGraph setup.program).fromModeCompletion mode)) at actual
  rw [filtered] at actual
  have canonical : (graph.ownCompletions who records).map
      ((toEventGraph setup.program).fromModeCompletion mode) =
      (toEventGraph setup.program).ownCompletions who
        (commitAttemptCompletions setup.program mode earlier suffix embedding native) := by
    simp only [records, ownCompletions, List.filter_map, List.map_map,
      Function.comp_def, toModeCompletion, fromModeCompletion]
    exact List.map_id _
  rw [canonical] at actual
  exact original.trans (congrArg (entry.history who ++ ·) actual.symm)

end Vegas
