/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingCountedIncludeMemory

/-! # Actual same-scheduler inclusion prefixes with evolving all-value memory -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L} {Obs : Type}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A selected original scheduler include builds both genuine chronological
successor traces and derives the updated hidden memory. Complete operational
own recall and all other owners' full recall are retained for the next step. -/
theorem phase_binding_memory_include_trace (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (remaining : Nat) (left right : (app).Execution)
    (leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining + 1, none, left⟩))
    (rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining + 1, none, right⟩))
    (memory : BindingShadow graph) (owner : Player) (owned : memory.OwnBindings owner)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (application : left.application = memory.phased owner right.application)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (observe : (app).PlayerView → Obs)
    (past : (left.recall owner).map (fun entry => (observe entry.beforeView, entry.emitted)) =
      (right.recall owner).map (fun entry => (observe entry.beforeView, entry.emitted)))
    (clear : right.application.current.excluded = ∅)
    (opaquePhase : ∀ phase ∈ right.application.phases.head?, phase.kind = .commitment)
    (id : MessageId Player)
    (selected : ReactiveApplication.Command.include id ∈
      (scheduler left.environmentRecall (left.observeEnvironment app)).support) :
    let firstNext := {left.includePending app id with environmentRecall :=
      left.environmentRecall ++ [⟨left.observeEnvironment app, .include id⟩]}
    let secondNext := {right.includePending app id with environmentRecall :=
      right.environmentRecall ++ [⟨right.observeEnvironment app, .include id⟩]}
    Nonempty (((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, none, firstNext⟩)) ∧
    Nonempty (((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, none, secondNext⟩)) ∧
    ∃ nextMemory : BindingShadow graph,
      nextMemory.OwnBindings owner ∧
      (∀ slot, nextMemory.candidates slot ≠ some .fresh) ∧
      firstNext.application = nextMemory.phased owner secondNext.application ∧
      firstNext.network = secondNext.network ∧ firstNext.receipts = secondNext.receipts ∧
      firstNext.environmentRecall = secondNext.environmentRecall ∧
      (∀ who, who ≠ owner → firstNext.recall who = secondNext.recall who) ∧
      (firstNext.recall owner).map (fun entry => (observe entry.beforeView, entry.emitted)) =
        (secondNext.recall owner).map (fun entry => (observe entry.beforeView, entry.emitted)) := by
  classical
  intro firstNext secondNext
  have supports := phase_opaque_include_trace runtime leaks memory owner owned left right
    application network receipts service recalled clear opaquePhase
      (PhaseCount.onePacketMenu runtime leaks bounds) (inputs.map (PhaseRuntimeState.initial plan))
        horizon scheduler remaining leftTrace rightTrace id selected
  refine ⟨supports.1, supports.2.1, ?_⟩
  have before : left.observeEnvironment app = right.observeEnvironment app := by
    change (⟨left.network.publicView, left.application.publicView, left.receipts⟩ :
      (app).EnvironmentView) = ⟨_, _, _⟩
    rw [network, receipts, application, phased_publicView owned]
    rfl
  have logs : left.environmentRecall ++ [⟨left.observeEnvironment app,
      (ReactiveApplication.Command.include id)⟩] =
      right.environmentRecall ++ [⟨right.observeEnvironment app, .include id⟩] := by
    rw [service, before]
  cases found : right.network.lookup id with
  | none =>
      have firstFound : left.network.lookup id = none := by rw [network]; exact found
      refine ⟨memory, owned, valid, ?_, ?_, ?_, logs, ?_, ?_⟩
      · simpa only [firstNext, secondNext, ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, firstFound, found] using application
      · simpa only [firstNext, secondNext, ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, firstFound, found] using network
      · simpa only [firstNext, secondNext, ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, firstFound, found] using receipts
      · simpa only [firstNext, secondNext, ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, firstFound, found] using recalled
      · simpa only [firstNext, secondNext, ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, firstFound, found] using past
  | some message =>
      have physical := PhaseCount.physicalBindings_history runtime leaks bounds plan inputs horizon
        scheduler rightTrace
      obtain ⟨entry, entryMember, material, _action, emitted, _packet⟩ :=
        physical.origins.lookup id message found
      have output : message ∈ (app).outputs (right.recall message.sender) :=
        List.mem_filterMap.mpr ⟨entry, entryMember, emitted⟩
      rw [← physical.clean.1.1 message.sender] at output
      have member : message ∈ right.network.inputs := (List.mem_filter.mp output).1
      obtain ⟨remembered, nextOwned, nextValid, appEq, netEq, receiptsEq, _serviceEq, recallEq,
          firstRecall, secondRecall⟩ :=
        include_counted_binding_memory runtime leaks bounds plan inputs horizon scheduler
          ⟨remaining + 1, none, right⟩ rightTrace memory owner owned valid left application network
            receipts service recalled clear opaquePhase id message found member
      refine ⟨remembered, nextOwned, nextValid, appEq, netEq, receiptsEq, logs, recallEq, ?_⟩
      change ((left.includePending app id).recall owner).map _ =
        ((right.includePending app id).recall owner).map _
      rw [firstRecall, secondRecall]
      exact past

end Vegas.EventGraphRuntime.BindingShadow
