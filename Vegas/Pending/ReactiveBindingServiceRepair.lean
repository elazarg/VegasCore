/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingRestoration
import Vegas.Pending.ReactiveRevealBlock

/-! # Reconstructing private input across protected binding service

The source of each distribution is the existing service evaluator. Reserved
inclusion followed by clock padding and harmless expiry retains the repaired
player's original whole input. No player is activated during that padding.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private def clockInput (ticks : Nat) (view : (runtime.reactiveApplication leaks).PlayerView) :
    (runtime.reactiveApplication leaks).PlayerView :=
  { view with application := { view.application with publicView :=
    { view.application.publicView with clock := view.application.publicView.clock + ticks } } }

private theorem completed_clock_tail_input
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : runtime.NetworkPolicy leaks)
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (event : graph.EventId) (completed : event ∈ execution.application.config.cut.completed)
    (ticks : Nat) :
    (runtime.runInteractionPlan leaks players scheduler
      (List.replicate ticks .tick ++ [.expire event]) execution).map
        (fun next => (next.recall who, next.observe (runtime.reactiveApplication leaks) who)) =
      PMF.pure (execution.recall who,
        clockInput runtime leaks ticks
          (execution.observe (runtime.reactiveApplication leaks) who)) := by
  let app := runtime.reactiveApplication leaks
  obtain ⟨ticked, tickLaw, application, network, receipts, recall⟩ :=
    runtime.interaction_ticks_pure leaks players scheduler ticks execution
  have notReady : ¬ ticked.application.config.cut.Ready event := by
    rw [application]
    intro ready
    exact ready.1 completed
  have expiry : app.environment ticked.application (.expire event) =
      PMF.pure ticked.application :=
    runtime.environmentStep_expire_of_not_ready ticked.application event notReady
  rw [runtime.runInteractionPlan_append, tickLaw, PMF.pure_bind]
  simp only [runInteractionPlan, interactionStep, interactionInstruction, PMF.pure_bind,
    ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
  change (((ticked.environmentStep app (.application (.expire event))).bind PMF.pure).bind
    PMF.pure).map _ = _
  rw [PMF.bind_pure, PMF.bind_pure]
  change (((app.environment ticked.application (.expire event)).map
    (fun state => { ticked with application := state })).map (fun next : app.Execution =>
      { next with environmentRecall := ticked.environmentRecall ++
        [(⟨ticked.observeEnvironment app, .application (.expire event)⟩ :
          app.EnvironmentEntry)] })).map _ = _
  rw [expiry, PMF.pure_map, PMF.pure_map, PMF.pure_map]
  apply congrArg PMF.pure
  change (ticked.recall who, ticked.observe app who) = _
  rw [recall]
  apply congrArg (fun view : (runtime.reactiveApplication leaks).PlayerView =>
    (execution.recall who, view))
  change ReactiveApplication.PlayerView.mk (app := app) _ _ _ = _
  rw [application, network, receipts]
  rfl

/-- Once the paired binding has been included, the entire service padding
preserves reconstruction of the original private recall and current input. -/
theorem BindingMemory.completed_clock_tail
    (memory : BindingMemory runtime leaks) (who : Player)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : runtime.NetworkPolicy leaks)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (past : memory.restoreRecall runtime leaks (right.recall who) = left.recall who)
    (observed : memory.shadow.inputView runtime leaks
      (right.observe (runtime.reactiveApplication leaks) who) =
        left.observe (runtime.reactiveApplication leaks) who)
    (event : graph.EventId)
    (leftDone : event ∈ left.application.config.cut.completed)
    (rightDone : event ∈ right.application.config.cut.completed) (ticks : Nat) :
    (runtime.runInteractionPlan leaks players scheduler
      (List.replicate ticks .tick ++ [.expire event]) left).map
        (fun next => (next.recall who, next.observe (runtime.reactiveApplication leaks) who)) =
      (runtime.runInteractionPlan leaks players scheduler
        (List.replicate ticks .tick ++ [.expire event]) right).map
          (fun next => (memory.restoreRecall runtime leaks (next.recall who),
            memory.shadow.inputView runtime leaks
              (next.observe (runtime.reactiveApplication leaks) who))) := by
  have leftLaw := completed_clock_tail_input runtime leaks players scheduler left who event
    leftDone ticks
  have rightLaw := completed_clock_tail_input runtime leaks players scheduler right who event
    rightDone ticks
  let restore := fun pair : List (runtime.reactiveApplication leaks).PlayerEntry ×
      (runtime.reactiveApplication leaks).PlayerView =>
    (memory.restoreRecall runtime leaks pair.1, memory.shadow.inputView runtime leaks pair.2)
  have mapped := congrArg (fun law => law.map restore) rightLaw
  simp only [PMF.map_comp, PMF.pure_map] at mapped
  rw [leftLaw, show (runtime.runInteractionPlan leaks players scheduler
      (List.replicate ticks .tick ++ [.expire event]) right).map
        (fun next => (memory.restoreRecall runtime leaks (next.recall who),
          memory.shadow.inputView runtime leaks
            (next.observe (runtime.reactiveApplication leaks) who))) = _ from mapped]
  apply congrArg PMF.pure
  apply Prod.ext past.symm
  exact (congrArg (clockInput runtime leaks ticks) observed).symm

/-- The whole protected binding suffix, including its actual reserved selector
and clock padding, preserves the reconstructed owner input after replacing
missing or mistyped private material by a valid value under the same handle. -/
theorem BindingMemory.repairResponse_protected_input
    (memory : BindingMemory runtime leaks) (who : Player)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : runtime.NetworkPolicy leaks)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (lengths : (right.recall who).length = memory.responses.length)
    (past : memory.restoreRecall runtime leaks (right.recall who) = left.recall who)
    (observed : memory.shadow.inputView runtime leaks
      (right.observe (runtime.reactiveApplication leaks) who) =
        left.observe (runtime.reactiveApplication leaks) who)
    (network : left.network = right.network)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L))
    (originalFresh : left.application.candidates.lookup (who, .prepared serial) = .fresh)
    (actualFresh : right.application.candidates.lookup (who, .prepared serial) = .fresh)
    (unusable : opening.bind (fun raw => raw.as? payload) = none)
    (ready : left.application.config.cut.Ready event)
    (timely : left.application.WithinDeadline runtime event)
    (vacant : left.application.accepted (.inr event) = none)
    (unused : left.application.HandleUnused (who, .prepared serial))
    (serials : left.network.SerialsBeforeNext) (ticks : Nat) :
    let app := runtime.reactiveApplication leaks
    let view := right.observe app who
    let original : app.Action :=
      ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩
    let repaired := memory.repairResponse runtime leaks who view original
    let remembered : BindingMemory runtime leaks :=
      ⟨repaired.2, memory.responses ++ [(memory.shadow.inputView runtime leaks view, original)]⟩
    (runtime.runInteractionPlan leaks players scheduler
      (.includeLatest event who :: List.replicate ticks .tick ++ [.expire event])
        (left.respond app who original)).map (fun next => (next.recall who, next.observe app who)) =
      (runtime.runInteractionPlan leaks players scheduler
        (.includeLatest event who :: List.replicate ticks .tick ++ [.expire event])
          (right.respond app who repaired.1)).map
            (fun next => (remembered.restoreRecall runtime leaks (next.recall who),
              remembered.shadow.inputView runtime leaks (next.observe app who))) := by
  let app := runtime.reactiveApplication leaks
  let view := right.observe app who
  let material : WitnessedSubmission graph :=
    ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩
  let original : app.Action := ⟨some material⟩
  let repaired := memory.repairResponse runtime leaks who view original
  let remembered : BindingMemory runtime leaks :=
    ⟨repaired.2, memory.responses ++ [(memory.shadow.inputView runtime leaks view, original)]⟩
  let before := left.respond app who original
  let after := right.respond app who repaired.1
  let id := (who, left.network.nextSerial who)
  let beforeIncluded : app.Execution := { before.includePending app id with
    environmentRecall := before.environmentRecall ++
      [⟨before.observeEnvironment app, .include id⟩] }
  let afterIncluded : app.Execution := { after.includePending app id with
    environmentRecall := after.environmentRecall ++ [⟨after.observeEnvironment app, .include id⟩] }
  have leftSelect : runtime.interactionStep leaks players scheduler (.includeLatest event who)
      before = PMF.pure beforeIncluded := by
    have chosen := runtime.reactiveLatest_after_submit leaks who event left serials material rfl
    unfold interactionStep
    rw [interactionInstruction, chosen, PMF.pure_bind]
    simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
      ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
    rfl
  have ownFresh : (memory.shadow.inputView runtime leaks view).application.candidates
      (.prepared serial) = .fresh := by
    rw [observed]
    exact originalFresh
  have repairedAction : repaired.1 =
      runtime.reactiveBinding leaks who event payload (.success (L.someValue payload)) serial :=
    memory.repairResponse_unusable runtime leaks who view event payload outputEq codeEq node
      serial opening ownFresh actualFresh unusable
  have rightSelect : runtime.interactionStep leaks players scheduler (.includeLatest event who)
      after = PMF.pure afterIncluded := by
    dsimp only [after, afterIncluded]
    rw [repairedAction, runtime.reactiveBinding_reserved_selection leaks right who event payload
      (.success (L.someValue payload)) serial (network ▸ serials) players scheduler,
      show right.network.nextSerial who = left.network.nextSerial who from
        congrArg (fun net => net.nextSerial who) network.symm]
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
    rfl
  have restored := memory.repairResponse_include_input runtime leaks who left right lengths past
    observed network event payload outputEq codeEq node serial opening originalFresh actualFresh
      ready timely vacant unused serials
  change remembered.restoreRecall runtime leaks (afterIncluded.recall who) =
      beforeIncluded.recall who ∧
    remembered.shadow.inputView runtime leaks (afterIncluded.observe app who) =
      beforeIncluded.observe app who ∧
    (afterIncluded.recall who).length = remembered.responses.length at restored
  have configLaw := runtime.rawBinding_reserved_config leaks left who event payload outputEq
    codeEq node serial opening ready timely originalFresh vacant unused serials players scheduler
  have configSupported : (beforeIncluded.application.config, beforeIncluded.receipts) ∈
      ((runtime.interactionStep leaks players scheduler (.includeLatest event who) before).map
        fun next => (next.application.config, next.receipts)).support := by
    rw [leftSelect, PMF.pure_map, PMF.mem_support_pure_iff _ _]
  rw [configLaw, PMF.mem_support_pure_iff _ _] at configSupported
  have sameConfig := congrArg Prod.fst configSupported
  dsimp only [Prod.fst] at sameConfig
  have leftDone : event ∈ beforeIncluded.application.config.cut.completed := by
    rw [sameConfig, Config.complete_cut, EventOrder.Cut.mem_complete]
    exact Or.inl rfl
  have publicEq : afterIncluded.application.publicView = beforeIncluded.application.publicView :=
    congrArg (fun input : app.PlayerView => input.application.publicView) restored.2.1
  have sameCut := EventGraph.cut_eq_of_completionOrder_eq afterIncluded.application.config
    beforeIncluded.application.config
      (congrArg (fun observed : PublicView graph => observed.observation.completionOrder) publicEq)
  have rightDone : event ∈ afterIncluded.application.config.cut.completed := by
    rw [sameCut]
    exact leftDone
  dsimp only
  rw [List.cons_append, runInteractionPlan, leftSelect, PMF.pure_bind,
    runInteractionPlan, rightSelect, PMF.pure_bind]
  exact remembered.completed_clock_tail runtime leaks who players scheduler beforeIncluded
    afterIncluded restored.1 restored.2.1 event leftDone rightDone ticks

end Vegas.EventGraphRuntime
