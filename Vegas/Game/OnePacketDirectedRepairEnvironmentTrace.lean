/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketDirectedRepairResponse

/-! # Actual scheduler traces through directed binding repair

The repair frame preserves the scheduler's actual view and private command
recall. Therefore the same scheduler command remains supported. A paired actual
environment operation extends the repaired one-packet history, with the same
complete operational record when its delivered-value guard holds.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

private theorem environment_step_supported {Principal : Type} [DecidableEq Principal]
    (app : ReactiveApplication Principal) (menu : app.ResponseMenu) (initial : PMF app.State)
    (horizon : Nat) (scheduler : app.Scheduler) (remaining : Nat)
    (execution next : app.Execution) (command : app.Command)
    (joint : Principal → Option app.Action)
    (legal : (menu.protocol initial horizon scheduler).Legal
      (some ⟨remaining + 1, none, execution⟩) joint)
    (chosen : command ∈ (scheduler execution.environmentRecall
      (execution.observeEnvironment app)).support)
    (reached : next ∈ (execution.environmentStep app command).support) :
    some ⟨remaining, command.actor? app, next⟩ ∈
      ((menu.protocol initial horizon scheduler).step
        (some ⟨remaining + 1, none, execution⟩) ⟨joint, legal⟩).support := by
  change _ ∈ ((scheduler execution.environmentRecall
    (execution.observeEnvironment app)).bind _).support
  rw [PMF.support_bind]
  refine Set.mem_iUnion₂.mpr ⟨command, chosen, ?_⟩
  rw [PMF.support_map]
  exact ⟨next, reached, rfl⟩

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

namespace DirectedBindingFrame

variable {memory : BindingMemory (runtime setup) leaks} {owner : Player}
  {original repaired nextOriginal nextRepaired : (application setup leaks).Execution}

/-- Supported scheduler commands transport through actual repaired environment
operations. Both executions retain the same command, remaining horizon, and
activation target, rather than an independently selected delivery schedule. -/
theorem environment_trace (frame : DirectedBindingFrame memory owner original repaired)
    (remaining : Nat)
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (some ⟨remaining + 1, none, original⟩))
    (imagePrior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (some ⟨remaining + 1, none, repaired⟩))
    (records : operationalRecord setup leaks bounds horizon scheduler prior =
      operationalRecord setup leaks bounds horizon scheduler imagePrior)
    (command : (application setup leaks).Command)
    (chosen : command ∈ (scheduler original.environmentRecall
      (original.observeEnvironment (application setup leaks))).support)
    (left : nextOriginal ∈ (original.environmentStep (application setup leaks) command).support)
    (right : nextRepaired ∈ (repaired.environmentStep (application setup leaks) command).support)
    (after : BindingMemory.Frame (runtime setup) leaks memory owner nextOriginal nextRepaired)
    (delivered : deliveredValue setup leaks owner
        (nextOriginal.observe (application setup leaks) owner) =
      deliveredValue setup leaks owner (nextRepaired.observe (application setup leaks) owner)) :
    DirectedBindingFrame memory owner nextOriginal nextRepaired ∧
      ∃ trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
          (some ⟨remaining, command.actor? (application setup leaks), nextRepaired⟩),
        operationalRecord setup leaks bounds horizon scheduler trace =
          operationalState setup leaks
              (some ⟨remaining, command.actor? (application setup leaks), nextOriginal⟩) ::
            operationalRecord setup leaks bounds horizon scheduler prior := by
  have repairedFrame := frame.environmentStep command nextOriginal nextRepaired left right after
  refine ⟨repairedFrame, ?_⟩
  let joint : Player → Option (application setup leaks).Action := fun _ => none
  have legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal
      (some ⟨remaining + 1, none, repaired⟩) joint := by
    constructor
    · simp [onePacketProtocol, ReactiveApplication.ResponseMenu.protocol,
        ReactiveApplication.terminal]
    · intro actor
      simp [joint, onePacketProtocol, ReactiveApplication.ResponseMenu.protocol,
        ReactiveApplication.actor]
  have chosenRepair : command ∈ (scheduler repaired.environmentRecall
      (repaired.observeEnvironment (application setup leaks))).support := by
    rw [← frame.service, ← frame.toFrame.environment]
    exact chosen
  have realized : some ⟨remaining, command.actor? (application setup leaks), nextRepaired⟩ ∈
      ((onePacketProtocol setup leaks bounds horizon scheduler).step
        (some ⟨remaining + 1, none, repaired⟩) ⟨joint, legal⟩).support := by
    exact environment_step_supported (application setup leaks)
      (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon scheduler remaining
      repaired nextRepaired command joint legal chosenRepair right
  refine ⟨imagePrior.extend joint legal realized, ?_⟩
  change operationalState setup leaks
      (some ⟨remaining, command.actor? (application setup leaks), nextRepaired⟩) ::
        operationalRecord setup leaks bounds horizon scheduler imagePrior = _
  rw [← records, ← after.operationalState repairedFrame.recalled delivered]

end DirectedBindingFrame

end Vegas
