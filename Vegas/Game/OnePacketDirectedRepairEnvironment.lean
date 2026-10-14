/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketDirectedRepairInclusion
import Vegas.Game.OnePacketDirectedRepairPassive
import Vegas.Game.OnePacketDirectedRepairChance
import Vegas.Pending.ReactiveBindingExpiryAccepted
import Vegas.Pending.ReactiveBindingExpiry

/-! # Complete actual environment dispatcher for directed binding repair -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

namespace DirectedBindingFrame

variable {memory : BindingMemory (runtime setup) leaks} {owner : Player}
  {original repaired : (application setup leaks).Execution}

private theorem application_stutter (frame : DirectedBindingFrame memory owner original repaired)
    (command : EnvironmentCommand (graph setup))
    (firstLaw : EventGraphRuntime.environmentStep (runtime setup) original.application command =
      PMF.pure original.application)
    (secondLaw : EventGraphRuntime.environmentStep (runtime setup) repaired.application command =
      PMF.pure repaired.application)
    (nextOriginal : (application setup leaks).Execution)
    (left : nextOriginal ∈ (original.environmentStep (application setup leaks)
      (.application command)).support) :
    ∃ nextRepaired : (application setup leaks).Execution,
      nextRepaired ∈ (repaired.environmentStep (application setup leaks)
        (.application command)).support ∧
      DirectedBindingFrame memory owner nextOriginal nextRepaired := by
  let app := application setup leaks
  have firstActual : (application setup leaks).environment original.application command =
      PMF.pure original.application :=
    firstLaw
  have secondActual : (application setup leaks).environment repaired.application command =
      PMF.pure repaired.application :=
    secondLaw
  simp only [ReactiveApplication.Execution.environmentStep, firstActual, PMF.pure_map,
    PMF.mem_support_pure_iff] at left
  subst nextOriginal
  refine ⟨{ repaired with environmentRecall := repaired.environmentRecall ++
    [⟨repaired.observeEnvironment app, .application command⟩] }, ?_, ?_⟩
  · simp only [ReactiveApplication.Execution.environmentStep, secondActual, PMF.pure_map,
      PMF.mem_support_pure_iff]
    rfl
  · exact ⟨frame.toFrame.recordEnvironment (.application command), frame.recalled⟩

private theorem sample_stutter (frame : DirectedBindingFrame memory owner original repaired)
    (event : (graph setup).EventId) (ready : original.application.config.cut.Ready event)
    (nonsample : ∀ payload law outputEq codeEq,
      nodeView (graph setup) event ≠ .sample payload law outputEq codeEq)
    (nextOriginal : (application setup leaks).Execution)
    (left : nextOriginal ∈ (original.environmentStep (application setup leaks)
      (.application (.executeSample event))).support) :
    ∃ nextRepaired : (application setup leaks).Execution,
      nextRepaired ∈ (repaired.environmentStep (application setup leaks)
        (.application (.executeSample event))).support ∧
      DirectedBindingFrame memory owner nextOriginal nextRepaired := by
  have rightReady : repaired.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← frame.toFrame.publicView, State.publicView_eventReady]
    exact ready
  exact frame.application_stutter (.executeSample event)
    (environmentStep_executeSample_of_nonsample (runtime setup) original.application event ready
      nonsample)
    (environmentStep_executeSample_of_nonsample (runtime setup) repaired.application event
      rightReady nonsample) nextOriginal left

/-- Every supported actual scheduler command has a supported repaired successor.
The hypotheses concern the original history's ready bindings and public
omission detector; no repaired successor or command-specific frame is assumed. -/
theorem environment_step (frame : DirectedBindingFrame memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (recorded : memory.RecordsSubmittedBindings (runtime setup) leaks owner original repaired)
    (clean : (runtime setup).CountClean leaks original)
    (signed : (runtime setup).SignedCommitments leaks original)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (successfulReady : ∀ (event : (graph setup).EventId) (actor : Player) (payload : L.Ty)
      (binding : EventGraph.FieldRef (graph setup).layout (.binding actor payload))
      (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
      (outputEq : (graph setup).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .resolve actor payload binding checks),
      nodeView (graph setup) event = .resolve actor payload binding checks outputEq codeEq →
      original.application.config.cut.Ready event →
      ∃ value, binding.get? original.application.config.store = some (.success value))
    (command : (application setup leaks).Command)
    (nextOriginal : (application setup leaks).Execution)
    (left : nextOriginal ∈ (original.environmentStep (application setup leaks) command).support)
    (accepted : ∀ event actor payload,
      (graph setup).outputLayout event = .binding actor payload →
      event ∈ nextOriginal.application.config.cut.completed →
      nextOriginal.application.accepted (.inr event) ≠ none) :
    ∃ nextRepaired : (application setup leaks).Execution,
      nextRepaired ∈ (repaired.environmentStep (application setup leaks) command).support ∧
      DirectedBindingFrame memory owner nextOriginal nextRepaired := by
  cases command with
  | wait => exact frame.wait_step nextOriginal left
  | activate actor => exact frame.activate_step actor nextOriginal left
  | «include» id =>
      have first : nextOriginal =
          { original.includePending (application setup leaks) id with
            environmentRecall := original.environmentRecall ++
              [⟨original.observeEnvironment (application setup leaks), .include id⟩] } := by
        simpa only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
          PMF.mem_support_pure_iff] using left
      subst nextOriginal
      let nextRepaired : (application setup leaks).Execution :=
        { repaired.includePending (application setup leaks) id with
          environmentRecall := repaired.environmentRecall ++
            [⟨repaired.observeEnvironment (application setup leaks), .include id⟩] }
      have right : nextRepaired ∈ (repaired.environmentStep (application setup leaks)
          (.include id)).support := by
        simp only [nextRepaired, ReactiveApplication.Execution.environmentStep, PMF.pure_map,
          PMF.mem_support_pure_iff]
      exact ⟨nextRepaired, right, frame.environmentStep (.include id) _ _ left right
        (frame.toFrame.pending_inclusion onlyBindings recorded clean signed leftBinding rightBinding
          successfulReady id)⟩
  | application operation =>
      cases operation with
      | advanceClock => exact frame.advanceClock_step nextOriginal left
      | executeSample event =>
          by_cases ready : original.application.config.cut.Ready event
          · cases node : nodeView (graph setup) event with
            | sample payload law outputEq codeEq =>
                exact frame.sample_step onlyBindings event ready payload law outputEq codeEq node
                  nextOriginal left
            | bind actor payload outputEq codeEq =>
                exact frame.sample_stutter event ready
                  (by intro _ _ _ _ same; rw [node] at same; cases same) nextOriginal left
            | resolve actor payload binding checks outputEq codeEq =>
                exact frame.sample_stutter event ready
                  (by intro _ _ _ _ same; rw [node] at same; cases same) nextOriginal left
          · have rightNotReady : ¬ repaired.application.config.cut.Ready event := by
              rw [← State.publicView_eventReady, ← frame.toFrame.publicView,
                State.publicView_eventReady]
              exact ready
            exact frame.application_stutter (.executeSample event)
              (environmentStep_executeSample_of_not_ready (runtime setup) original.application event
                ready)
              (environmentStep_executeSample_of_not_ready (runtime setup) repaired.application event
                rightNotReady) nextOriginal left
      | expire event =>
          obtain ⟨nextRepaired, right⟩ := (repaired.environmentStep (application setup leaks)
            (.application (.expire event))).support_nonempty
          refine ⟨nextRepaired, right, frame.environmentStep (.application (.expire event))
            _ _ left right ?_⟩
          cases node : nodeView (graph setup) event with
          | sample payload law outputEq codeEq =>
              exact frame.toFrame.expiry_public onlyBindings event (by rw [outputEq]; trivial)
                nextOriginal nextRepaired left right
          | resolve actor payload binding checks outputEq codeEq =>
              exact frame.toFrame.expiry_public onlyBindings event (by rw [outputEq]; trivial)
                nextOriginal nextRepaired left right
          | bind actor payload outputEq codeEq =>
              have notMissed : nextOriginal.application.publicView.missedBinding event = false := by
                apply Bool.eq_false_iff.mpr
                intro missed
                obtain ⟨completed, absent⟩ := (State.publicView_missedBinding _ event actor payload
                  outputEq).mp missed
                exact accepted event actor payload outputEq completed absent
              exact frame.toFrame.binding_expiry leftBinding event actor payload outputEq codeEq
                node nextOriginal nextRepaired left right notMissed

end DirectedBindingFrame

end Vegas
