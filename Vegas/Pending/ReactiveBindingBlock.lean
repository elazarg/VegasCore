/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBinding
import Vegas.Pending.ReactiveServiceSelection
import Vegas.Pending.EventSequentialTiming

/-! # Atomic binding and its reserved inclusion

This is the actual response and service instruction. It retains the selected
binding value, including failure, and uses no private preparation activation.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The reserved selector chooses a newly emitted binding even in the presence
of earlier pending traffic. -/
theorem reactiveBinding_reserved_selection (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat)
    (serials : execution.network.SerialsBeforeNext)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) :
    let app := runtime.reactiveApplication leaks
    let submitted := execution.respond app owner
      (runtime.reactiveBinding leaks owner event payload result serial)
    runtime.interactionStep leaks players network (.includeLatest event owner) submitted =
      submitted.environmentStep app (.include (owner, execution.network.nextSerial owner)) := by
  let app := runtime.reactiveApplication leaks
  let submitted := execution.respond app owner
    (runtime.reactiveBinding leaks owner event payload result serial)
  have selected : runtime.reactiveLatest leaks event owner (submitted.observeEnvironment app) =
      .include (owner, execution.network.nextSerial owner) := by
    cases result <;> exact runtime.reactiveLatest_after_submit leaks owner event execution serials
      _ rfl
  change runtime.interactionStep leaks players network (.includeLatest event owner) submitted = _
  unfold interactionStep
  rw [interactionInstruction, selected, FinDist.pure_bind]
  simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
  exact FinDist.bind_pure _

/-- A single compiled binding response followed by actual reserved inclusion
has exactly the graph commit kernel and a successful receipt. All freshness,
readiness and timing premises concern the entry checkpoint. -/
theorem reactiveBinding_reserved_config (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (result : PublicationResult (L.Val payload)) (serial : Nat)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (fresh : execution.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (vacant : execution.application.accepted (.inr event) = none)
    (unused : execution.application.HandleUnused (owner, .prepared serial))
    (serials : execution.network.SerialsBeforeNext)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) :
    let app := runtime.reactiveApplication leaks
    let submitted := execution.respond app owner
      (runtime.reactiveBinding leaks owner event payload result serial)
    (runtime.interactionStep leaks players network (.includeLatest event owner) submitted).map
      (fun next => (next.application.config, next.receipts)) =
      FinDist.pure (execution.application.config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) result)
        (cast (congrArg EventField.Value outputEq.symm) result),
        execution.receipts ++ [((owner, execution.network.nextSerial owner), true)]) := by
  let app := runtime.reactiveApplication leaks
  let submitted := execution.respond app owner
    (runtime.reactiveBinding leaks owner event payload result serial)
  have configEq : submitted.application.config = execution.application.config := by
    change (submitStep (Submission.register _ execution.application owner) owner _).config = _
    rw [submitStep_config]
    exact (Submission.register_facts _ owner execution.application).1
  have publicEq : submitted.application.publicView = execution.application.publicView := by
    change (submitStep (Submission.register _ execution.application owner) owner _).publicView = _
    rw [submitStep_publicView]
    exact (Submission.register_facts _ owner execution.application).2.2
  have acceptedEq : submitted.application.accepted = execution.application.accepted :=
    congrArg PublicView.accepted publicEq
  have clockEq : submitted.application.clock = execution.application.clock :=
    congrArg PublicView.clock publicEq
  have activatedEq : submitted.application.activatedAt = execution.application.activatedAt :=
    congrArg PublicView.activatedAt publicEq
  have submittedReady : submitted.application.config.cut.Ready event := by
    rwa [configEq]
  have submittedTimely : submitted.application.WithinDeadline runtime event := by
    unfold State.WithinDeadline
    rwa [clockEq, activatedEq]
  have submittedVacant : submitted.application.accepted (.inr event) = none := by
    rwa [acceptedEq]
  have submittedUnused : submitted.application.HandleUnused (owner, .prepared serial) := by
    simpa only [State.HandleUnused, acceptedEq] using unused
  have pending : submitted.network.lookup (owner, execution.network.nextSerial owner) =
      some ⟨(owner, execution.network.nextSerial owner),
        ⟨.commitment event (owner, .prepared serial), none⟩⟩ := by
    cases result <;> exact serials.lookup_submit owner
      ⟨.commitment event (owner, .prepared serial), none⟩
  let scheduler : app.Scheduler := fun _ _ => FinDist.pure .wait
  have reached : submitted ∈ (app.runRounds scheduler players 0 submitted).support := by
    simp only [ReactiveApplication.runRounds, FinDist.mem_support_pure]
  obtain ⟨completed, receipt⟩ := runtime.reactiveBinding_continuation_include leaks owner event
    payload outputEq codeEq node result serial (execution.network.nextSerial owner) execution
    submitted fresh scheduler players 0 reached pending submittedReady submittedTimely
    submittedVacant submittedUnused
  simp only [configEq] at completed
  have priorReceipts : submitted.receipts = execution.receipts := rfl
  rw [priorReceipts] at receipt
  dsimp only
  rw [runtime.reactiveBinding_reserved_selection leaks execution owner event payload result serial
    serials players network]
  simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
  exact congrArg FinDist.pure (Prod.ext completed receipt)

/-- At initialization, a first binding node needs only its positive declared
deadline. Candidate freshness, handle availability and transport freshness all
follow from the real initialized state. -/
theorem reactiveBinding_initialized_config (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) (owner : Player) (event : graph.EventId) (first : event.val = 0)
    (payload : L.Ty) (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (positive : 0 < runtime.deadline event)
    (result : PublicationResult (L.Val payload)) (serial : Nat)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) :
    let app := runtime.reactiveApplication leaks
    let execution := ReactiveApplication.Execution.initial app (State.initial inputs)
    ∃ ready : execution.application.config.cut.Ready event,
      (runtime.interactionStep leaks players network (.includeLatest event owner)
        (execution.respond app owner
          (runtime.reactiveBinding leaks owner event payload result serial))).map
          (fun next => (next.application.config, next.receipts)) =
        FinDist.pure (execution.application.config.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) result)
          (cast (congrArg EventField.Value outputEq.symm) result), [((owner, 0), true)]) := by
  let app := runtime.reactiveApplication leaks
  let execution := ReactiveApplication.Execution.initial app (State.initial inputs)
  have ready : execution.application.config.cut.Ready event := by
    constructor
    · exact Finset.notMem_empty event
    · intro predecessor member
      have before := graph.order.predecessor_lt member
      omega
  have actor : graph.actor? event = some owner := by
    change (graph.nodes event).actor = some owner
    rw [← EventCode.actor_cast outputEq (graph.nodes event), codeEq]
    rfl
  have timely : execution.application.WithinDeadline runtime event :=
    State.initial_withinDeadline inputs runtime event ready (by rw [actor]; rfl) positive
  have unused : execution.application.HandleUnused (owner, .prepared serial) := by
    intro field associated
    obtain ⟨input, initialOwner, payload, _, _, same⟩ :=
      State.initial_accepted_eq_some inputs field (owner, .prepared serial) associated
    cases congrArg Prod.snd same
  refine ⟨ready, ?_⟩
  exact runtime.reactiveBinding_reserved_config leaks execution owner event payload outputEq codeEq
    node result serial ready timely (State.initial_candidate inputs owner (.prepared serial)) rfl
    unused MessageNetwork.SerialsBeforeNext.empty players network

end Vegas.EventGraphRuntime
