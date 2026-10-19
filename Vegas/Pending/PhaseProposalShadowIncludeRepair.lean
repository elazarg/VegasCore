/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalShadowHandlerRepair
import Vegas.Pending.PhaseProposalShadowRejectedTrace
import Vegas.Pending.PhaseProposalShadowAcceptedTrace

/-! # Every actual pending inclusion extends a general counted repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Missing, rejected and accepting packets all use their actual native
branch. The repaired counted trace is constructed under the original selected
scheduler atom, through arbitrary exclusions, old traffic and phase resets. -/
theorem include_repair
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
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (supported : memory.CompletedAt right.application.current.native.config)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (prepared : PreparedBindings runtime leaks owner left right)
    (entryRef : left.application.entry.native.config.store.BindingRefines
      right.application.entry.native.config.store)
    (currentRef : left.application.current.native.config.store.BindingRefines
      right.application.current.native.config.store)
    (id : MessageId Player)
    (selected : ReactiveApplication.Command.include id ∈
      (scheduler left.environmentRecall (left.observeEnvironment app)).support) :
    let first := { left.includePending app id with
      environmentRecall := left.environmentRecall ++ [⟨left.observeEnvironment app, .include id⟩] }
    let second := { right.includePending app id with
      environmentRecall := right.environmentRecall ++
        [⟨right.observeEnvironment app, .include id⟩] }
    ∃ nextMemory : BindingShadow graph,
      Nonempty (((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
          (some ⟨remaining, none, second⟩)) ∧
      nextMemory.OwnBindings owner ∧
      (∀ slot, nextMemory.candidates slot ≠ some .fresh) ∧
      PhaseStateFrame nextMemory owner first.application second.application ∧
      nextMemory.CompletedAt second.application.current.native.config ∧
      first.network = second.network ∧
      phaseExternalObservation runtime leaks owner first =
        phaseExternalObservation runtime leaks owner second ∧
      PreparedBindings runtime leaks owner first second ∧
      first.application.entry.native.config.store.BindingRefines
          second.application.entry.native.config.store ∧
      first.application.current.native.config.store.BindingRefines
          second.application.current.native.config.store := by
  classical
  intro first second
  have firstMoved : first ∈ (left.environmentStep app (.include id)).support := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.mem_support_pure_iff]
    rfl
  have secondMoved : second ∈ (right.environmentStep app (.include id)).support := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.mem_support_pure_iff]
    rfl
  have nextPrepared := PreparedBindings.environment runtime leaks prepared (.include id)
    firstMoved secondMoved
  cases found : left.network.lookup id with
  | none =>
      have rightFound : right.network.lookup id = none := by rw [← network]; exact found
      have firstApplication : first.application = left.application := by
        simp only [first, ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, found]
      have secondApplication : second.application = right.application := by
        simp only [second, ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, rightFound]
      have nextFrame : PhaseStateFrame memory owner first.application second.application := by
        rw [firstApplication, secondApplication]
        exact frame
      have nextNetwork : first.network = second.network := by
        simp only [first, second, ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, found, rightFound]
        exact network
      have nextReceipts : first.receipts = second.receipts := by
        simp only [first, second, ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, found, rightFound]
        exact receipts
      have before : left.observeEnvironment app = right.observeEnvironment app := by
        change (⟨left.network.publicView, left.application.publicView, left.receipts⟩ :
          (app).EnvironmentView) = ⟨_, _, _⟩
        rw [network, receipts, frame.publicView owned]
        rfl
      have nextService : first.environmentRecall = second.environmentRecall := by
        change left.environmentRecall ++ [_] = right.environmentRecall ++ [_]
        rw [service, before]
      have chosen : ReactiveApplication.Command.include id ∈
          (scheduler right.environmentRecall (right.observeEnvironment app)).support := by
        rw [← service, ← before]
        exact selected
      have target := (PhaseCount.onePacketMenu runtime leaks bounds).trace_environment
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler remaining right second
          (.include id) rightTrace chosen secondMoved
      refine ⟨memory, target, owned, valid, nextFrame, ?_, nextNetwork, ?_, nextPrepared, ?_, ?_⟩
      · rw [secondApplication]
        exact supported
      · apply phaseExternalObservation_congr runtime leaks first second owner nextNetwork
          nextReceipts nextService (nextFrame.publicView owned) (nextFrame.playerView_other owned)
        intro who different
        change (left.includePending app id).recall who = (right.includePending app id).recall who
        simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          found, rightFound] using recalled who different
      · rw [firstApplication, secondApplication]
        exact entryRef
      · rw [firstApplication, secondApplication]
        exact currentRef
  | some message =>
      have physical := PhaseCount.physicalBindings_history runtime leaks bounds plan inputs horizon
        scheduler leftTrace
      obtain ⟨entry, entryMember, _material, _, emitted, _⟩ :=
        physical.origins.lookup id message found
      have output : message ∈ (app).outputs (left.recall message.sender) :=
        List.mem_filterMap.mpr ⟨entry, entryMember, emitted⟩
      rw [← physical.clean.1.1 message.sender] at output
      have member : message ∈ left.network.inputs := (List.mem_filter.mp output).1
      cases handled : left.application.handle runtime message with
      | none =>
          obtain ⟨target, firstApplication, secondApplication, nextNetwork, external⟩ :=
            include_rejected_repair_trace runtime leaks bounds plan inputs horizon scheduler
              remaining left right leftTrace rightTrace memory owner frame owned network receipts
                service recalled id message found member handled selected
          refine ⟨memory, target, owned, valid, ?_, ?_, nextNetwork, external, nextPrepared, ?_, ?_⟩
          · rw [firstApplication, secondApplication]
            exact frame
          · rw [secondApplication]
            exact supported
          · rw [firstApplication, secondApplication]
            exact entryRef
          · rw [firstApplication, secondApplication]
            exact currentRef
      | some next =>
          obtain ⟨nextMemory, image, imageHandled, nextOwned, nextValid, paired, nextSupport,
              nextEntryRef, nextCurrentRef⟩ :=
            frame.handler_repair runtime leaks bounds plan inputs horizon scheduler
              ⟨remaining + 1, none, left⟩ ⟨remaining + 1, none, right⟩ leftTrace rightTrace owned
                valid supported prepared entryRef currentRef message member next handled
          obtain ⟨target, firstApplication, secondApplication, nextNetwork, external⟩ :=
            include_accepted_repair_trace runtime leaks bounds plan inputs horizon scheduler
              remaining left right rightTrace memory nextMemory owner frame owned nextOwned network
                receipts service recalled id message found next image handled imageHandled paired
                  selected
          refine ⟨nextMemory, target, nextOwned, nextValid, ?_, ?_, nextNetwork, external,
            nextPrepared, ?_, ?_⟩
          · rw [firstApplication, secondApplication]
            exact paired
          · rw [secondApplication]
            exact nextSupport
          · rw [firstApplication, secondApplication]
            exact nextEntryRef
          · rw [firstApplication, secondApplication]
            exact nextCurrentRef

end Vegas.EventGraphRuntime.BindingShadow
