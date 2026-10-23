/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalShadowRejection
import Interaction.ReactiveRoundTrace

/-! # Actual repaired trace extensions at rejected counted inclusions -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The original rejected packet constructs a genuine repaired execution
step under the same selected scheduler atom. Its FALSE receipt, stale packet
identity, complete network and every other player's literal input persist. -/
theorem include_rejected_repair_trace
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat)
    (left right : (app).Execution)
    (leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining + 1, none, left⟩))
    (rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining + 1, none, right⟩))
    (memory : BindingShadow graph) (owner : Player)
    (frame : PhaseStateFrame memory owner left.application right.application)
    (owned : memory.OwnBindings owner)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : left.network.lookup id = some message) (member : message ∈ left.network.inputs)
    (rejected : left.application.handle runtime message = none)
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
      first.application = left.application ∧ second.application = right.application ∧
      first.network = second.network ∧
      phaseExternalObservation runtime leaks owner first =
        phaseExternalObservation runtime leaks owner second := by
  classical
  intro first second
  have rightRejected := frame.rejection_of_counted runtime leaks bounds plan inputs horizon
    scheduler ⟨remaining + 1, none, left⟩ leftTrace owned message member rejected
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
  have leftApplication : first.application = left.application := by
    simp only [first, ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, show (app).handle left.application message = none from rejected, Option.getD_none]
  have rightApplication : second.application = right.application := by
    simp only [second, ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      rightFound, show (app).handle right.application message = none from rightRejected,
      Option.getD_none]
  have nextNetwork : first.network = second.network := by
    simp only [first, second, ReactiveApplication.Execution.includePending,
      MessageNetwork.includePending, found, rightFound]
    rw [network]
  have nextReceipts : first.receipts = second.receipts := by
    simp only [first, second, ReactiveApplication.Execution.includePending,
      MessageNetwork.includePending, found, rightFound,
      show (app).handle left.application message = none from rejected,
      show (app).handle right.application message = none from rightRejected, Option.isSome_none]
    rw [receipts]
  have nextService : first.environmentRecall = second.environmentRecall := by
    change left.environmentRecall ++ [_] = right.environmentRecall ++ [_]
    rw [service, before]
  have nextFrame : PhaseStateFrame memory owner first.application second.application := by
    rw [leftApplication, rightApplication]
    exact frame
  refine ⟨target, leftApplication, rightApplication, nextNetwork, ?_⟩
  apply phaseExternalObservation_congr runtime leaks first second owner nextNetwork nextReceipts
    nextService (nextFrame.publicView owned) (nextFrame.playerView_other owned)
  intro who different
  change (left.includePending app id).recall who = (right.includePending app id).recall who
  simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    found, rightFound] using recalled who different

end Vegas.EventGraphRuntime.BindingShadow
