/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalCountedShadowAcceptance
import Vegas.Pending.PhaseBindingOpaqueStep

/-! # Entire external input preservation at an actual accepted inclusion

The paired handler is derived from counted provenance. The actual execution
update retains receipts, submitted traffic, the service word and every other
owner's full recall and current input, including across recovery normalization.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A real accepting pending inclusion preserves the complete external
execution observation after actual general normalization. The target handler,
its receipt and its logical output mask are constructed by the proof. -/
theorem include_owned_binding_external_of_history
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (memory : BindingShadow graph) (owner : Player) (left : (app).Execution)
    (frame : PhaseStateFrame memory owner left.application control.execution.application)
    (owned : memory.OwnBindings owner)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (supported : memory.CompletedAt control.execution.application.current.native.config)
    (network : left.network = control.execution.network)
    (receipts : left.receipts = control.execution.receipts)
    (service : left.environmentRecall = control.execution.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = control.execution.recall who)
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : control.execution.network.lookup id = some message)
    (member : message ∈ control.execution.network.inputs)
    (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (next : PhaseRuntimeState graph)
    (accepted : control.execution.application.handle runtime message = some next) :
    ∃ nextMemory : BindingShadow graph, nextMemory.OwnBindings owner ∧
      nextMemory.candidates = memory.candidates ∧
      (∀ slot, nextMemory.candidates slot ≠ some .fresh) ∧
      PhaseStateFrame nextMemory owner (left.includePending app id).application
        (control.execution.includePending app id).application ∧
      nextMemory.CompletedAt
        (control.execution.includePending app id).application.current.native.config ∧
      (left.includePending app id).network =
        (control.execution.includePending app id).network ∧
      phaseExternalObservation runtime leaks owner (left.includePending app id) =
        phaseExternalObservation runtime leaks owner (control.execution.includePending app id) := by
  classical
  have leftFound : left.network.lookup id = some message := by rw [network]; exact found
  obtain ⟨nextMemory, image, firstHandled, nextOwned, candidates, nextValid, nextFrame,
      nextSupport⟩ := frame.handle_owned_binding_of_history runtime leaks bounds plan inputs horizon
        scheduler control trace owned valid supported message member event payload binding
          candidate call next accepted
  have paired : PhaseStateFrame nextMemory owner (left.includePending app id).application
      (control.execution.includePending app id).application := by
    simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      leftFound, found, show (app).handle left.application message = some image from firstHandled,
      show (app).handle control.execution.application message = some next from accepted,
      Option.getD_some] using nextFrame
  have stillSupported : nextMemory.CompletedAt
      (control.execution.includePending app id).application.current.native.config := by
    simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, show (app).handle control.execution.application message = some next from accepted,
      Option.getD_some] using nextSupport
  have nextNetwork : (left.includePending app id).network =
      (control.execution.includePending app id).network := by
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      leftFound, found]
    rw [network]
  have nextReceipts : (left.includePending app id).receipts =
      (control.execution.includePending app id).receipts := by
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      leftFound, found, show (app).handle left.application message = some image from firstHandled,
      show (app).handle control.execution.application message = some next from accepted,
      Option.isSome_some]
    rw [receipts]
  have nextService : (left.includePending app id).environmentRecall =
      (control.execution.includePending app id).environmentRecall := by
    simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      leftFound, found] using service
  have nextRecall (who : Player) (different : who ≠ owner) :
      (left.includePending app id).recall who =
        (control.execution.includePending app id).recall who := by
    simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      leftFound, found] using recalled who different
  refine ⟨nextMemory, nextOwned, candidates, nextValid, paired, stillSupported, nextNetwork, ?_⟩
  exact phaseExternalObservation_congr runtime leaks _ _ owner nextNetwork nextReceipts nextService
    (paired.publicView nextOwned) (paired.playerView_other nextOwned) nextRecall

end Vegas.EventGraphRuntime.BindingShadow
