/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingCountedMemory

/-! # Every physical packet inclusion in an opaque all-value binding block -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
/-- A physically accepted call inside a commitment descriptor is a binding
packet. Opening, malformed and stale calls cannot create a hidden successor. -/
theorem accepted_call_in_commitment (state next : PhaseRuntimeState graph)
    (opaquePhase : ∀ phase ∈ state.phases.head?, phase.kind = .commitment)
    (message : Message Player (CommitAttemptPacket graph))
    (accepted : state.handle runtime message = some next) :
    ∃ event candidate, message.payload.packet.call = .commitment event candidate := by
  classical
  unfold PhaseRuntimeState.handle at accepted
  split at accepted
  · rename_i admitted
    obtain ⟨native, handled, _⟩ := Option.map_eq_some_iff.mp accepted
    have allowed := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp admitted).1).2
    cases call : message.payload.packet.call with
    | commitment event candidate => exact ⟨event, candidate, rfl⟩
    | malformed raw =>
        simp only [call, handle] at handled
        cases handled
    | opening event candidate raw =>
        rw [call] at handled
        obtain ⟨_ready, _timely, actor, payload, binding, checks, outputEq, _codeEq, _value,
            _result, _facts⟩ := handle_opening_conditions runtime state.current.native native
              message.id event candidate raw handled
        obtain ⟨phase, installed, named, namedEq, inside⟩ :=
          state.allows_event message.payload.packet.call allowed
        have same : named = event := by
          rw [call] at namedEq
          exact Option.some.inj namedEq.symm
        subst named
        obtain ⟨lower, upper⟩ := (phase.mem_events event).mp inside
        have fields := phase.fields event lower upper
        rw [opaquePhase phase installed] at fields
        obtain ⟨owner, ty, bindingEq⟩ := fields
        cases outputEq.symm.trans bindingEq
  · cases accepted

/-- Every actual counted include chooses its own accepting or rejecting branch.
Both actual successors retain complete all-value reconstruction, physical
receipts and foreign recall; no image handler or successor memory is supplied. -/
theorem include_counted_binding_memory (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (memory : BindingShadow graph) (owner : Player) (owned : memory.OwnBindings owner)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (left : (app).Execution)
    (application : left.application = memory.phased owner control.execution.application)
    (network : left.network = control.execution.network)
    (receipts : left.receipts = control.execution.receipts)
    (service : left.environmentRecall = control.execution.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = control.execution.recall who)
    (clear : control.execution.application.current.excluded = ∅)
    (opaquePhase : ∀ phase ∈ control.execution.application.phases.head?,
      phase.kind = .commitment)
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : control.execution.network.lookup id = some message)
    (member : message ∈ control.execution.network.inputs) :
    ∃ nextMemory : BindingShadow graph,
      nextMemory.OwnBindings owner ∧
      (∀ slot, nextMemory.candidates slot ≠ some .fresh) ∧
      (left.includePending app id).application =
        nextMemory.phased owner (control.execution.includePending app id).application ∧
      (left.includePending app id).network = (control.execution.includePending app id).network ∧
      (left.includePending app id).receipts = (control.execution.includePending app id).receipts ∧
      (left.includePending app id).environmentRecall =
        (control.execution.includePending app id).environmentRecall ∧
      (∀ who, who ≠ owner → (left.includePending app id).recall who =
        (control.execution.includePending app id).recall who) ∧
      (left.includePending app id).recall = left.recall ∧
      (control.execution.includePending app id).recall = control.execution.recall := by
  classical
  have firstFound : left.network.lookup id = some message := by rw [network]; exact found
  cases handled : control.execution.application.handle runtime message with
  | some next =>
      obtain ⟨event, candidate, call⟩ := accepted_call_in_commitment runtime
        control.execution.application next opaquePhase message handled
      obtain ⟨remembered, image, nextOwned, nextValid, firstHandled, reconstructed⟩ :=
        phase_handle_binding_memory_of_history runtime leaks bounds plan inputs horizon scheduler
          control trace memory owner owned valid clear message member event candidate call next
            handled
      have firstHandled' : (app).handle left.application message = some image := by
        rw [application]
        exact firstHandled
      change (app).handle control.execution.application message = some next at handled
      refine ⟨remembered, nextOwned, nextValid, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          firstFound, found, firstHandled', handled, Option.getD_some] using reconstructed.symm
      · simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          firstFound, found]
        rw [network]
      · simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          firstFound, found, firstHandled', handled, Option.isSome_some]
        rw [receipts]
      · simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          firstFound, found] using service
      · simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          firstFound, found] using recalled
      · simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          firstFound]
      · simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          found]
  | none =>
      have publicEq : left.application.publicView = control.execution.application.publicView := by
        rw [application]
        exact phased_publicView owned _
      have comparison := PhaseRuntimeState.handle_opaque_external_congr runtime left.application
        control.execution.application owner (by rw [application]; rfl)
        (by rw [application]; rfl) (congrArg PhasePublicView.retired publicEq)
        (by rw [application]; exact native_publicView owned _)
        (by intro who different; rw [application];
            exact native_playerView_other owned _ who different)
        (by rw [application]; exact clear) clear (by simpa only [application, phased] using
          opaquePhase) message
      rw [handled, Option.map_none] at comparison
      have firstNone : (app).handle left.application message = none := by
        cases first : (app).handle left.application message with
        | none => rfl
        | some image =>
            have rawFirst : left.application.handle runtime message = some image := first
            rw [rawFirst] at comparison
            cases comparison
      change (app).handle control.execution.application message = none at handled
      refine ⟨memory, owned, valid, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          firstFound, found, firstNone, handled, Option.getD_none] using application
      · simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          firstFound, found]
        rw [network]
      · simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          firstFound, found, firstNone, handled, Option.isSome_none]
        rw [receipts]
      · simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          firstFound, found] using service
      · simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          firstFound, found] using recalled
      · simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          firstFound]
      · simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          found]

end Vegas.EventGraphRuntime.BindingShadow
