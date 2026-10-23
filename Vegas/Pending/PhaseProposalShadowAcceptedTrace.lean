/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalShadowOpeningAcceptance
import Interaction.ReactiveRoundTrace

/-! # Lifting actual paired accepting handlers to counted executions -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Constructor-specific factual handler proofs feed the literal inclusion
operation. The same supported scheduler command then produces the genuine
target trace, TRUE receipts and complete nonrepairing input histories. -/
theorem include_accepted_repair_trace
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat)
    (left right : (app).Execution)
    (rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining + 1, none, right⟩))
    (memory nextMemory : BindingShadow graph) (owner : Player)
    (frame : PhaseStateFrame memory owner left.application right.application)
    (owned : memory.OwnBindings owner) (nextOwned : nextMemory.OwnBindings owner)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : left.network.lookup id = some message)
    (firstState secondState : PhaseRuntimeState graph)
    (firstHandled : left.application.handle runtime message = some firstState)
    (secondHandled : right.application.handle runtime message = some secondState)
    (paired : PhaseStateFrame nextMemory owner firstState secondState)
    (selected : ReactiveApplication.Command.include id ∈
      (scheduler left.environmentRecall (left.observeEnvironment app)).support) :
    let first := { left.includePending app id with
      environmentRecall := left.environmentRecall ++ [⟨left.observeEnvironment app, .include id⟩] }
    let second := { right.includePending app id with
      environmentRecall := right.environmentRecall ++
        [⟨right.observeEnvironment app, .include id⟩] }
    Nonempty (((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, none, second⟩)) ∧
      first.application = firstState ∧ second.application = secondState ∧
      first.network = second.network ∧
      phaseExternalObservation runtime leaks owner first =
        phaseExternalObservation runtime leaks owner second := by
  classical
  intro first second
  have rightFound : right.network.lookup id = some message := by rw [← network]; exact found
  have before : left.observeEnvironment app = right.observeEnvironment app := by
    change (⟨left.network.publicView, left.application.publicView, left.receipts⟩ :
      (app).EnvironmentView) = ⟨_, _, _⟩
    rw [network, receipts, frame.publicView owned]
    rfl
  have chosen : ReactiveApplication.Command.include id ∈
      (scheduler right.environmentRecall (right.observeEnvironment app)).support := by
    rw [← service, ← before]
    exact selected
  have moved : second ∈ (right.environmentStep app (.include id)).support := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.mem_support_pure_iff]
    rfl
  have target := (PhaseCount.onePacketMenu runtime leaks bounds).trace_environment
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler remaining right second
      (.include id) rightTrace chosen moved
  have firstApplication : first.application = firstState := by
    simp only [first, ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, show (app).handle left.application message = some firstState from firstHandled,
      Option.getD_some]
  have secondApplication : second.application = secondState := by
    simp only [second, ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      rightFound, show (app).handle right.application message = some secondState from secondHandled,
      Option.getD_some]
  have nextNetwork : first.network = second.network := by
    simp only [first, second, ReactiveApplication.Execution.includePending,
      MessageNetwork.includePending, found, rightFound]
    rw [network]
  have nextReceipts : first.receipts = second.receipts := by
    simp only [first, second, ReactiveApplication.Execution.includePending,
      MessageNetwork.includePending, found, rightFound,
      show (app).handle left.application message = some firstState from firstHandled,
      show (app).handle right.application message = some secondState from secondHandled,
      Option.isSome_some]
    rw [receipts]
  have nextService : first.environmentRecall = second.environmentRecall := by
    change left.environmentRecall ++ [_] = right.environmentRecall ++ [_]
    rw [service, before]
  have nextFrame : PhaseStateFrame nextMemory owner first.application second.application := by
    rw [firstApplication, secondApplication]
    exact paired
  refine ⟨target, firstApplication, secondApplication, nextNetwork, ?_⟩
  apply phaseExternalObservation_congr runtime leaks first second owner nextNetwork nextReceipts
    nextService (nextFrame.publicView nextOwned) (nextFrame.playerView_other nextOwned)
  intro who different
  change (left.includePending app id).recall who = (right.includePending app id).recall who
  simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    found, rightFound] using recalled who different

end Vegas.EventGraphRuntime.BindingShadow
