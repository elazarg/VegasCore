/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalShadowSourceAcceptance
import Vegas.Pending.PhaseProposalShadowInclude
import Interaction.ReactiveRoundTrace

/-! # Genuine repaired trace extensions at accepted binding inclusions

The selected original scheduler atom and original accepted handler construct
the repaired trace extension. Neither target acceptance nor target transition
support is assumed. Saved and live semantic shadows may be masked by a retry.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The actual original accepting inclusion extends the already initialized
repaired prefix under the same scheduler, retaining the full focal input word. -/
theorem include_owned_binding_repair_trace
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
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : left.network.lookup id = some message) (member : message ∈ left.network.inputs)
    (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (next : PhaseRuntimeState graph)
    (accepted : left.application.handle runtime message = some next)
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
      nextMemory.OwnBindings owner ∧ nextMemory.candidates = memory.candidates ∧
      (∀ slot, nextMemory.candidates slot ≠ some .fresh) ∧
      PhaseStateFrame nextMemory owner first.application second.application ∧
      nextMemory.CompletedAt second.application.current.native.config ∧
      phaseExternalObservation runtime leaks owner first =
        phaseExternalObservation runtime leaks owner second := by
  classical
  intro first second
  obtain ⟨intermediate, image, imageHandled, _, _, _, _, _⟩ :=
    frame.repair_owned_binding_of_history runtime leaks bounds plan inputs horizon scheduler
      ⟨remaining + 1, none, left⟩ ⟨remaining + 1, none, right⟩ leftTrace rightTrace owned
        valid supported message member event payload binding candidate call next accepted
  have rightFound : right.network.lookup id = some message := by rw [← network]; exact found
  have rightMember : message ∈ right.network.inputs := by rw [← network]; exact member
  obtain ⟨nextMemory, nextOwned, candidates, nextValid, paired, nextSupport,
      nextNetwork, external⟩ := include_owned_binding_external_of_history runtime leaks bounds
        plan inputs horizon scheduler ⟨remaining + 1, none, right⟩ rightTrace memory owner left
          frame owned valid supported network receipts service recalled id message rightFound
            rightMember event payload binding candidate call image imageHandled
  have before : left.observeEnvironment app = right.observeEnvironment app := by
    change (⟨left.network.publicView, left.application.publicView, left.receipts⟩ :
      (app).EnvironmentView) = ⟨_, _, _⟩
    rw [network, frame.publicView owned, receipts]
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
  have nextReceipts : first.receipts = second.receipts :=
    congrArg (fun observation => observation.2.1) external
  have nextService : first.environmentRecall = second.environmentRecall := by
    change left.environmentRecall ++ [_] = right.environmentRecall ++ [_]
    rw [service, before]
  have nextRecall (who : Player) (different : who ≠ owner) :
      first.recall who = second.recall who := by
    change (left.includePending app id).recall who = (right.includePending app id).recall who
    simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, rightFound] using recalled who different
  refine ⟨nextMemory, target, nextOwned, candidates, nextValid, paired, nextSupport, ?_⟩
  exact phaseExternalObservation_congr runtime leaks first second owner nextNetwork nextReceipts
    nextService (paired.publicView nextOwned) (paired.playerView_other nextOwned) nextRecall

end Vegas.EventGraphRuntime.BindingShadow
