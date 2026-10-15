/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativeEnvironment
import Vegas.Pending.PhaseNativeScheduler
import Vegas.Pending.PhaseNativeFailureRecord

/-! # Full adaptive physical environment transitions share native draws -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

omit [Fintype Player] in
private theorem remembered_projection (current next : (P).Execution) (chosen : (P).Command) :
    execution runtime leaks plan
        { next with environmentRecall := current.environmentRecall ++
          [⟨current.observeEnvironment P, chosen⟩] } =
      { execution runtime leaks plan next with
        environmentRecall := (execution runtime leaks plan current).environmentRecall ++
          [⟨(execution runtime leaks plan current).observeEnvironment N,
            command runtime leaks plan chosen⟩] } := by
  rw [observeEnvironment runtime leaks plan current]
  simp only [execution, List.map_append, List.map_cons, List.map_nil, environmentEntry]

/-- At genuine clear counted histories the native passive observation law uses
exactly the original pending packet list, including every reconstructed tag. -/
theorem observePending_of_clear (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (P).Scheduler) {current}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅) (who : Player) :
    (N).observePending who (execution runtime leaks plan current.execution).network.pending =
      (P).observePending who current.execution.network.pending := by
  change leaks who
    (((current.execution.network.mapPayload CommitAttemptPacket.packet).mapPayload
      plan.stampPacket).pending) = _
  rw [network_retag_of_clear runtime leaks plan bounds inputs horizon scheduler trace clear]
  rfl

/-- A common native sample couples the complete environment transitions. Clear
physical outcomes retain the exact projected network, receipts and full recalls. -/
theorem exists_paired_environmentStep (bounds : MessageBounds graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler) {control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) (chosen : (P).Command) :
    ∃ joint : PMF ((N).Execution × (P).Execution),
      joint.map Prod.fst = (execution runtime leaks plan control.execution).environmentStep N
        (command runtime leaks plan chosen) ∧
      joint.map Prod.snd = control.execution.environmentStep P chosen ∧
      (∀ pair ∈ joint.support, pair.2.application.current.excluded = ∅ →
        pair.1 = execution runtime leaks plan pair.2) ∧
      ∀ pair ∈ joint.support,
        PublicExclusionRecord
          (⟨pair.1.application, pair.2.application.current.excluded⟩ : RecoveryState graph) := by
  classical
  let current := control.execution
  have valid := clear_publicRecord runtime leaks plan bounds inputs horizon scheduler trace clear
  let firstRemember : (N).Execution → (N).Execution := fun next =>
    { next with environmentRecall := (execution runtime leaks plan current).environmentRecall ++
      [⟨(execution runtime leaks plan current).observeEnvironment N,
        command runtime leaks plan chosen⟩] }
  let secondRemember : (P).Execution → (P).Execution := fun next =>
    { next with environmentRecall := current.environmentRecall ++
      [⟨current.observeEnvironment P, chosen⟩] }
  have remembered (next : (P).Execution) :
      execution runtime leaks plan (secondRemember next) =
        firstRemember (execution runtime leaks plan next) :=
    remembered_projection runtime leaks plan current next chosen
  cases chosen with
  | activate who =>
      let firstNext := fun selected => firstRemember
        { execution runtime leaks plan current with network :=
          (execution runtime leaks plan current).network.learn who selected }
      let secondNext := fun selected => secondRemember
        { current with network := current.network.learn who selected }
      refine ⟨(leaks who current.network.pending).map
        (fun selected => (firstNext selected, secondNext selected)), ?_, ?_, ?_, ?_⟩
      · simp only [PMF.map_comp, Function.comp_def, firstNext, firstRemember,
          ReactiveApplication.Execution.environmentStep, command]
        rw [observePending_of_clear runtime leaks plan bounds inputs horizon scheduler trace clear]
        rfl
      · simp only [PMF.map_comp, Function.comp_def, secondNext, secondRemember,
          ReactiveApplication.Execution.environmentStep]
        rfl
      · intro pair member _afterClear
        obtain ⟨selected, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
        have same : execution runtime leaks plan
            { current with network := current.network.learn who selected } =
            { execution runtime leaks plan current with network :=
              (execution runtime leaks plan current).network.learn who selected } := by
          simp only [execution, MessageNetwork.mapPayload_learn]
        exact (congrArg firstRemember same).symm.trans (remembered _).symm
      · intro pair member
        obtain ⟨selected, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
        exact valid
  | wait =>
      refine ⟨PMF.pure (firstRemember (execution runtime leaks plan current),
        secondRemember current), ?_, ?_, ?_, ?_⟩
      · simp only [PMF.pure_map, ReactiveApplication.Execution.environmentStep, command,
          firstRemember]
        rfl
      · simp only [PMF.pure_map, ReactiveApplication.Execution.environmentStep, secondRemember]
        rfl
      · intro pair member _afterClear
        cases (PMF.mem_support_pure_iff _ _).mp member
        exact (remembered current).symm
      · intro pair member
        cases (PMF.mem_support_pure_iff _ _).mp member
        exact valid
  | «include» id =>
      let firstNext := (execution runtime leaks plan current).includePending N id
      let secondNext := current.includePending P id
      refine ⟨PMF.pure (firstRemember firstNext, secondRemember secondNext), ?_, ?_, ?_, ?_⟩
      · simp only [PMF.pure_map, ReactiveApplication.Execution.environmentStep, command,
          firstNext, firstRemember]
        rfl
      · simp only [PMF.pure_map, ReactiveApplication.Execution.environmentStep,
          secondNext, secondRemember]
        rfl
      · intro pair member afterClear
        cases (PMF.mem_support_pure_iff _ _).mp member
        have same := includePending_of_clear_result runtime leaks plan bounds ordered maximal
          inputs horizon scheduler trace clear id afterClear
        exact (congrArg firstRemember same).symm.trans (remembered secondNext).symm
      · intro pair member
        cases (PMF.mem_support_pure_iff _ _).mp member
        exact includePending_exclusionRecord runtime leaks plan bounds ordered maximal inputs
          horizon scheduler trace clear id
  | application selected =>
      have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon
        scheduler trace
      have frontier := (phaseApplication_live runtime leaks).history _ horizon scheduler
        (fun initial supported => by
          obtain ⟨input, _support, rfl⟩ := PMF.support_map .. ▸ supported
          exact ⟨PhaseRuntimeState.initial_frontier plan input,
            PhaseRuntimeState.initial_live plan input⟩) rawTrace
      have geometry := phasePlanGeometry_history runtime leaks plan maximal inputs horizon scheduler
        rawTrace
      have spec := pairedApplication_spec runtime current.application ordered frontier.1 frontier.2
        geometry.2.2 selected
      let firstNext : State graph → (N).Execution := fun native => firstRemember
        { execution runtime leaks plan current with application := native }
      let secondNext : PhaseRuntimeState graph → (P).Execution := fun state => secondRemember
        { current with application := state }
      refine ⟨(pairedApplication runtime current.application selected).map
        (fun pair => (firstNext pair.1, secondNext pair.2)), ?_, ?_, ?_, ?_⟩
      · calc
          _ = ((pairedApplication runtime current.application selected).map Prod.fst).map
              firstNext := by rw [PMF.map_comp, PMF.map_comp]; rfl
          _ = (environmentStep runtime current.application.current.native selected).map
              firstNext := by rw [spec.1]
          _ = _ := by
            simp only [firstNext, firstRemember, ReactiveApplication.Execution.environmentStep,
              command, PMF.map_comp]
            rfl
      · calc
          _ = ((pairedApplication runtime current.application selected).map Prod.snd).map
              secondNext := by rw [PMF.map_comp, PMF.map_comp]; rfl
          _ = (current.application.environment runtime selected).map secondNext := by
            rw [spec.2.1]
          _ = _ := by
            simp only [secondNext, secondRemember, ReactiveApplication.Execution.environmentStep,
              PMF.map_comp]
            rfl
      · intro pair member afterClear
        obtain ⟨raw, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
        have same := spec.2.2.1 raw supported afterClear
        have equal : execution runtime leaks plan
            { current with application := raw.2 } =
            { execution runtime leaks plan current with application := raw.1 } := by
          simp only [execution, same]
        exact (congrArg firstRemember equal).symm.trans (remembered _).symm
      · intro pair member
        obtain ⟨raw, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
        exact spec.2.2.2 raw supported valid

end Vegas.EventGraphRuntime.PhaseNativeProjection
