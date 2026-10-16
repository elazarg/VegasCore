/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingPreparationMemory

/-! # Actual accepted inclusion with updated sender-private reconstruction -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The actual same-packet include operation reconstructs both complete phase
states after the private memory update. Neither the target handler nor a target
normalization equation is assumed. Accepted failure is retained exactly. -/
theorem include_binding_memory (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner) (left right : (app).Execution)
    (application : left.application = memory.phased owner right.application)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (clear : right.application.current.excluded = ∅) (archive : right.application.retired = [])
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : right.network.lookup id = some message) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (admitted : (message.payload.tokenValid right.application.attempt &&
      right.application.allows message.payload.packet.call &&
      !right.application.current.excludedCall message.payload.packet.call) = true)
    (sender : message.id.1 = owner) (candidateOwner : candidate.1 = owner)
    (ready : right.application.current.native.config.cut.Ready event)
    (timely : right.application.current.native.WithinDeadline runtime event)
    (vacant : right.application.current.native.accepted (.inr event) = none)
    (unused : right.application.current.native.HandleUnused candidate)
    (fixed : right.application.current.native.candidates.lookup candidate ≠ .fresh)
    (originalFixed : left.application.current.native.candidates.lookup candidate ≠ .fresh)
    (savedMissing : event ∉ right.application.entry.native.config.cut.completed) :
    let result := left.application.current.native.bindingResult candidate payload
    let remembered := memory.rememberCompletion event
      (cast (congrArg EventField.Action outputEq.symm) result)
      (cast (congrArg EventField.Value outputEq.symm) result)
    let first := left.includePending app id
    let second := right.includePending app id
    remembered.OwnBindings owner ∧
      first.application = remembered.phased owner second.application ∧
      first.network = second.network ∧ first.receipts = second.receipts ∧
      first.environmentRecall = second.environmentRecall ∧
      (∀ who, who ≠ owner → first.recall who = second.recall who) := by
  classical
  intro result remembered first second
  have originalFixed' : (memory.native owner right.application.current.native).candidates.lookup
      candidate ≠ .fresh := by simpa only [application, phased, recovery] using originalFixed
  obtain ⟨firstState, secondState, firstHandled, secondHandled, nextOwned, reconstructed⟩ :=
    phase_handle_binding_memory runtime memory owner owned right.application clear archive event
      payload outputEq codeEq node message candidate call admitted sender candidateOwner ready
        timely vacant unused fixed originalFixed' savedMissing
  have firstFound : left.network.lookup id = some message := by rw [network]; exact found
  have firstHandled' : (app).handle left.application message = some firstState := by
    rw [application]
    exact firstHandled
  change (app).handle right.application message = some secondState at secondHandled
  have memoryEq : remembered = memory.rememberCompletion event
      (cast (congrArg EventField.Action outputEq.symm)
        ((memory.native owner right.application.current.native).bindingResult candidate payload))
      (cast (congrArg EventField.Value outputEq.symm)
        ((memory.native owner right.application.current.native).bindingResult candidate payload)) :=
      by
    dsimp only [remembered, result]
    rw [application]
    rfl
  rw [← memoryEq] at nextOwned reconstructed
  refine ⟨nextOwned, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [first, second, ReactiveApplication.Execution.includePending,
      MessageNetwork.includePending, firstFound, found, firstHandled', secondHandled,
      Option.isSome_some, Option.getD_some] using reconstructed.symm
  · simp only [first, second, ReactiveApplication.Execution.includePending,
      MessageNetwork.includePending, firstFound, found]
    rw [network]
  · simp only [first, second, ReactiveApplication.Execution.includePending,
      MessageNetwork.includePending, firstFound, found, firstHandled', secondHandled,
      Option.isSome_some]
    rw [receipts]
  · simpa only [first, second, ReactiveApplication.Execution.includePending,
      MessageNetwork.includePending, firstFound, found] using service
  · simpa only [first, second, ReactiveApplication.Execution.includePending,
      MessageNetwork.includePending, firstFound, found] using recalled

end Vegas.EventGraphRuntime.BindingShadow
