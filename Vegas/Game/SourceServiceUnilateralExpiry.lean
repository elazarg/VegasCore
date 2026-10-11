/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceExpiry
import Vegas.Pending.ReactiveUnilateralExpiry
import Vegas.Pending.ReactiveUnilateralSilentExpiry

/-! # Actual source-service expiry with one arbitrary raw player -/

noncomputable section
namespace Vegas
open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Protected service derives foreign silent settlement, while actual focal
expiry admits the genuinely coupled source step without prescribing its policy. -/
theorem source_unilateral_expiry_frontier
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (opportunity : (serviceRuntime setup mode deadline).Opportunity leaks
      (serviceInitialLaw setup mode) horizon scheduler delay)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (inclusion : ProtectedInclusion (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler bound)
    (ordered : (serviceGraph setup mode).RevealRelaxedOrdered)
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
      horizon scheduler).Trace (some control)) (idle : control.actor = none)
    (valid : control.execution.application.BindingInvariant) (focal : Player)
    (conformance : ∀ owner, owner ≠ focal → (serviceRuntime setup mode deadline).RecordedTimelyCalls
      leaks owner
      control.execution)
    (profile : (serviceGraph setup mode).BehavioralProfile)
    (memories : Player → List (Option (serviceGraph setup mode).Completion))
    (consistent : ∀ owner, owner ≠ focal →
      ((serviceRuntime setup mode deadline).prescribedReactivePolicy leaks
      owner (profile owner)).Consistent (control.execution.recall owner))
    (quiet : ∀ owner entry, entry ∈ control.execution.recall owner →
      entry.action.transmission = none → entry.emitted = none)
    (sent : ∀ owner entry, entry ∈ control.execution.recall owner → ∀ material,
      entry.action.transmission = some material → ∃ message,
        entry.emitted = some message ∧ message.payload.call = material.call.packet)
    (supported : ∀ owner, owner ≠ focal → memories owner ∈
      (((serviceRuntime setup mode deadline).prescribedReactiveImplementation leaks owner
        (profile owner)).posterior (control.execution.recall owner)).support)
    (frontier : (serviceGraph setup mode).Config)
    (related : (serviceRuntime setup mode deadline).ReactiveUnilateralFrontier
      leaks focal control.execution
      memories frontier)
    (event : (serviceGraph setup mode).EventId)
    (after : (serviceApplication setup mode deadline leaks).Execution)
    (moved : after ∈ (control.execution.environmentStep
      (serviceApplication setup mode deadline leaks) (.application (.expire event))).support) :
    ∃ final, (serviceRuntime setup mode deadline).ReactiveUnilateralFrontier leaks focal
      after memories final := by
  let runtime := serviceRuntime setup mode deadline
  let app := serviceApplication setup mode deadline leaks
  by_cases focalEvent : (serviceGraph setup mode).actor? event = some focal
  · exact related.expire_focal runtime leaks profile control.execution after focal memories frontier
      consistent supported event focalEvent moved
  have movedOriginal := moved
  obtain ⟨updated, selected, rfl⟩ := PMF.support_map .. ▸ moved
  obtain ⟨next, changed, rfl⟩ := PMF.support_map .. ▸ selected
  change next ∈ (environmentStep runtime control.execution.application (.expire event)).support
    at changed
  have stutter (same : next = control.execution.application) :
      runtime.ReactiveUnilateralFrontier leaks focal
        { control.execution with
          application := next
          environmentRecall := control.execution.environmentRecall ++
            [⟨control.execution.observeEnvironment app, .application (.expire event)⟩] }
        memories frontier := by
    subst next
    exact ReactiveUnilateralFrontier.congr_execution runtime leaks _ _ focal
      memories frontier related rfl rfl rfl
  by_cases ready : control.execution.application.config.cut.Ready event
  · cases activated : control.execution.application.activatedAt event with
    | none =>
        rw [environmentStep_expire_of_not_activated runtime _ event ready activated,
          PMF.mem_support_pure_iff] at changed
        exact ⟨frontier, stutter changed⟩
    | some entered =>
        by_cases due : deadline event ≤ control.execution.application.clock - entered
        · cases node : nodeView (serviceGraph setup mode) event with
          | sample payload law outputEq codeEq =>
              rw [environmentStep_expire_sample_eq runtime _ event ready entered activated due
                payload law outputEq codeEq node, PMF.mem_support_pure_iff] at changed
              exact ⟨frontier, stutter changed⟩
          | bind owner payload outputEq codeEq =>
              have different : owner ≠ focal := by
                intro same
                exact focalEvent (same ▸ nodeView_bind_actor outputEq codeEq)
              exact (source_prescribed_due_binding_impossible setup leaks horizon scheduler delay
                bound opportunity timely inclusion ordered control trace idle owner event payload
                outputEq codeEq node ready entered activated due (profile owner)
                  (consistent owner different)
                (conformance owner different) (memories owner) (supported owner different)).elim
          | resolve owner payload binding checks outputEq codeEq =>
              have actor := nodeView_resolve_actor outputEq codeEq
              have different : owner ≠ focal := by
                intro same
                exact focalEvent (same ▸ actor)
              obtain ⟨entry, remembered, paired, named, matching⟩ :=
                due_prescribed_intention_silent setup leaks horizon scheduler delay bound
                  opportunity timely inclusion ordered control trace idle owner event actor ready
                  entered activated due (profile owner) (consistent owner different)
                  (quiet owner) (sent owner) (conformance owner different)
                  (memories owner) (supported owner different)
              subst event
              refine ⟨frontier, ?_⟩
              exact ReactiveUnilateralFrontier.expire_foreign_silent_resolution
                runtime leaks ordered
                (serviceInitialLaw setup mode) horizon scheduler control trace valid
                focal memories frontier related profile consistent supported owner different
                (quiet owner) (sent owner)
                entry remembered paired matching ready entered activated due
                payload binding checks outputEq codeEq node _
                movedOriginal
        · rw [environmentStep_expire_of_not_due runtime _ event ready entered activated due,
            PMF.mem_support_pure_iff] at changed
          exact ⟨frontier, stutter changed⟩
  · rw [environmentStep_expire_of_not_ready runtime _ event ready, PMF.mem_support_pure_iff]
      at changed
    exact ⟨frontier, stutter changed⟩


end Vegas
