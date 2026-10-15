/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingRepairTrace

/-! # Actual passive observations and waiting retain both repair checkpoints -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}

private theorem reobserve {nativeLeaks :
    MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
    {memory : BindingMemory runtime nativeLeaks} {owner : Player}
    {original repaired : (runtime.reactiveApplication nativeLeaks).Execution}
    (frame : BindingMemory.Frame runtime nativeLeaks memory owner original repaired)
    (leftPool rightPool : MessageNetwork Player (WitnessedPacket graph))
    (poolEq : leftPool = rightPool)
    (leftService rightService :
      List (runtime.reactiveApplication nativeLeaks).EnvironmentEntry)
    (serviceEq : leftService = rightService) :
    BindingMemory.Frame runtime nativeLeaks memory owner
      { original with network := leftPool, environmentRecall := leftService }
      { repaired with network := rightPool, environmentRecall := rightService } := by
  refine ⟨frame.past, ?_, frame.lengths, poolEq, serviceEq, frame.views, frame.recall,
    frame.slots, frame.successful, frame.submissions⟩
  have own : memory.shadow.view (repaired.application.playerView owner) =
      original.application.playerView owner :=
    congrArg ReactiveApplication.PlayerView.application frame.observed
  change (⟨rightPool.observe owner, memory.shadow.view (repaired.application.playerView owner),
    repaired.receipts⟩ : (runtime.reactiveApplication nativeLeaks).PlayerView) =
      ⟨leftPool.observe owner, original.application.playerView owner, original.receipts⟩
  rw [← poolEq, frame.receipts, own]

namespace Frame

variable {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- The same actual private leak sample can be made at either paired prefix.
Neither the source packet contents nor a saved observation are erased. -/
theorem activate (frame : Frame runtime leaks memory owner original repaired)
    (actor : Player) (selected : Finset (MessageId Player)) :
    Frame runtime leaks memory owner
      { original with
        network := original.network.learn actor selected
        environmentRecall := original.environmentRecall ++
          [⟨original.observeEnvironment (phaseApplication runtime leaks), .activate actor⟩] }
      { repaired with
        network := repaired.network.learn actor selected
        environmentRecall := repaired.environmentRecall ++
          [⟨repaired.observeEnvironment (phaseApplication runtime leaks), .activate actor⟩] } := by
  have pools : original.network.learn actor selected = repaired.network.learn actor selected :=
    congrArg (fun pool => pool.learn actor selected) frame.network
  have service : original.environmentRecall ++
      [⟨original.observeEnvironment (phaseApplication runtime leaks), .activate actor⟩] =
      repaired.environmentRecall ++
        [⟨repaired.observeEnvironment (phaseApplication runtime leaks), .activate actor⟩] := by
    rw [frame.service, frame.environment_input]
  refine ⟨?_, ?_, frame.phases, frame.generation, frame.clearOriginal, frame.clearRepaired,
    frame.archiveOriginal, frame.archiveRepaired, pools, service, frame.foreignRecall⟩
  · exact reobserve frame.live _ _ (congrArg PhaseBindingRepair.network pools) _ _
      (congrArg (List.map (environmentEntry runtime leaks)) service)
  · exact reobserve frame.saved _ _ (congrArg PhaseBindingRepair.network pools) _ _
      (congrArg (List.map (environmentEntry runtime leaks)) service)

/-- Waiting appends the actual scheduler command and changes no private input. -/
theorem wait (frame : Frame runtime leaks memory owner original repaired) :
    Frame runtime leaks memory owner
      { original with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment (phaseApplication runtime leaks), .wait⟩] }
      { repaired with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment (phaseApplication runtime leaks), .wait⟩] } := by
  have service : original.environmentRecall ++
      [⟨original.observeEnvironment (phaseApplication runtime leaks), .wait⟩] =
      repaired.environmentRecall ++
        [⟨repaired.observeEnvironment (phaseApplication runtime leaks), .wait⟩] := by
    rw [frame.service, frame.environment_input]
  refine ⟨?_, ?_, frame.phases, frame.generation, frame.clearOriginal, frame.clearRepaired,
    frame.archiveOriginal, frame.archiveRepaired, frame.network, service, frame.foreignRecall⟩
  · exact reobserve frame.live _ _ (congrArg PhaseBindingRepair.network frame.network) _ _
      (congrArg (List.map (environmentEntry runtime leaks)) service)
  · exact reobserve frame.saved _ _ (congrArg PhaseBindingRepair.network frame.network) _ _
      (congrArg (List.map (environmentEntry runtime leaks)) service)

/-- The actual passive observation law supplies the paired activation prefix;
its sample is shared because the complete physical pending network is equal. -/
theorem activate_trace (frame : Frame runtime leaks memory owner original repaired)
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (PhaseRuntimeState graph)) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat)
    (prior : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + 1, none, repaired⟩)) (actor : Player)
    (selected : (ReactiveApplication.Command.activate actor) ∈
      (scheduler original.environmentRecall
        (original.observeEnvironment (phaseApplication runtime leaks))).support)
    (sample : Finset (MessageId Player))
    (observed : sample ∈ (leaks actor original.network.pending).support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, some actor,
        { repaired with
          network := repaired.network.learn actor sample
          environmentRecall := repaired.environmentRecall ++
            [⟨repaired.observeEnvironment (phaseApplication runtime leaks),
              .activate actor⟩] }⟩)) := by
  have chosen : (ReactiveApplication.Command.activate actor) ∈
      (scheduler repaired.environmentRecall
        (repaired.observeEnvironment (phaseApplication runtime leaks))).support := by
    rw [← frame.scheduler_law scheduler]
    exact selected
  apply menu.trace_environment initial horizon scheduler remaining repaired _ (.activate actor)
    prior chosen
  unfold ReactiveApplication.Execution.environmentStep
  rw [PMF.support_map]
  refine ⟨{ repaired with network := repaired.network.learn actor sample }, ?_, rfl⟩
  rw [PMF.support_map]
  refine ⟨sample, ?_, rfl⟩
  change sample ∈ (leaks actor repaired.network.pending).support
  rw [← frame.network]
  exact observed

/-- The original scheduler's waiting atom extends the repaired legal prefix. -/
theorem wait_trace (frame : Frame runtime leaks memory owner original repaired)
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (PhaseRuntimeState graph)) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat)
    (prior : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining + 1, none, repaired⟩))
    (selected : (ReactiveApplication.Command.wait) ∈
      (scheduler original.environmentRecall
        (original.observeEnvironment (phaseApplication runtime leaks))).support) :
    Nonempty ((menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none,
        { repaired with environmentRecall := repaired.environmentRecall ++
          [⟨repaired.observeEnvironment (phaseApplication runtime leaks), .wait⟩] }⟩)) := by
  have chosen : (ReactiveApplication.Command.wait) ∈
      (scheduler repaired.environmentRecall
        (repaired.observeEnvironment (phaseApplication runtime leaks))).support := by
    rw [← frame.scheduler_law scheduler]
    exact selected
  apply menu.trace_environment initial horizon scheduler remaining repaired _ .wait prior chosen
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
    PMF.mem_support_pure_iff]

end Frame
end Vegas.EventGraphRuntime.PhaseBindingRepair
