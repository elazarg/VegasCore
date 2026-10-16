/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingForeignCompletionMemory
import Vegas.Pending.PhaseBindingMemoryFreshness
import Vegas.Pending.PhaseStoredCheckpoint
import Vegas.Pending.PhaseLatestBindingHistory
import Vegas.Pending.PhaseOwnCommitments

/-! # All-value remembered acceptance derived from actual counted histories -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Actual accepted counted commitments determine their own readiness, sender,
frozen physical handle and absence from the saved checkpoint. The complete
next all-value reconstruction is derived; no image outcome is supplied. -/
theorem phase_handle_binding_memory_of_history (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (memory : BindingShadow graph) (owner : Player) (owned : memory.OwnBindings owner)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (clear : control.execution.application.current.excluded = ∅)
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ control.execution.network.inputs)
    (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (next : PhaseRuntimeState graph)
    (accepted : control.execution.application.handle runtime message = some next) :
    ∃ nextMemory : BindingShadow graph, ∃ image : PhaseRuntimeState graph,
      nextMemory.OwnBindings owner ∧
      (∀ slot, nextMemory.candidates slot ≠ some .fresh) ∧
      (memory.phased owner control.execution.application).handle runtime message = some image ∧
      nextMemory.phased owner next = image := by
  classical
  have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  have archive := (phase_clear_history runtime leaks plan inputs horizon scheduler control rawTrace
    clear).2
  have admitted : (message.payload.tokenValid control.execution.application.attempt &&
      control.execution.application.allows message.payload.packet.call &&
      !control.execution.application.current.excludedCall message.payload.packet.call) = true := by
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · assumption
    · cases accepted
  have nativeAccepted : ∃ native,
      handle runtime control.execution.application.current.native
        ⟨message.id, .commitment event candidate⟩ = some native := by
    unfold PhaseRuntimeState.handle at accepted
    rw [admitted] at accepted
    simp only [↓reduceIte, call, Option.map_eq_some_iff] at accepted
    obtain ⟨native, handled, _⟩ := accepted
    exact ⟨native, handled⟩
  obtain ⟨native, handled⟩ := nativeAccepted
  obtain ⟨ready, timely, actor, payload, outputEq, codeEq, node, sender, candidateOwner,
      vacant, unused⟩ := handle_commitment_conditions runtime _ native message.id event candidate
        handled
  have count := PhaseCount.countRecall_history runtime leaks rawTrace
  have output : message ∈ (app).outputs (control.execution.recall actor) := by
    rw [← count.1 actor]
    exact List.mem_filter.mpr ⟨member, by simp only [Message.sender, sender, decide_true]⟩
  have signed := phaseOwnCommitmentsFixed_history runtime leaks
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler rawTrace
  change PhaseOwnCommitmentsFixed runtime leaks control.execution at signed
  have fixed : control.execution.application.current.native.candidates.lookup candidate ≠
      .fresh := by
    have handleEq : candidate = (actor, candidate.2) := Prod.ext candidateOwner rfl
    rw [handleEq]
    exact signed actor message output event candidate.2 (by rwa [← handleEq])
  by_cases same : actor = owner
  · subst owner
    have originalFixed : (memory.native actor
        control.execution.application.current.native).candidates.lookup candidate ≠ .fresh := by
      intro fresh
      have candidateEq : candidate = (actor, candidate.2) := Prod.ext candidateOwner rfl
      rw [candidateEq] at fresh fixed
      simp only [BindingShadow.native, CommitmentCandidates.lookup, ite_true] at fresh
      exact fixed ((candidate_fresh_iff memory valid candidate.2 _).mp fresh)
    have savedMissing :
        event ∉ control.execution.application.entry.native.config.cut.completed := by
      intro completed
      have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler
        rawTrace
      have available :=
        (control.execution.application.entry.native.config.output_available event).mpr completed
      cases old : control.execution.application.entry.native.config.outputs event with
      | none => simp only [old, Option.isSome_none, Bool.false_eq_true] at available
      | some value =>
          have retained := stored (.inr event) value old
          apply ready.1
          apply (control.execution.application.current.native.config.output_available event).mp
          change control.execution.application.current.native.config.outputs event = some value
            at retained
          rw [retained]
          rfl
    obtain ⟨image, second, firstHandled, secondHandled, nextOwned, reconstructed⟩ :=
      phase_handle_binding_memory runtime memory actor owned control.execution.application clear
        archive event payload outputEq codeEq node message candidate call admitted sender
          candidateOwner ready timely vacant unused fixed originalFixed savedMissing
    have equalNext : second = next := Option.some.inj (secondHandled.symm.trans accepted)
    subst second
    refine ⟨_, image, nextOwned, ?_, firstHandled, reconstructed⟩
    exact rememberCompletion_candidates_not_fresh memory valid event _ _
  · obtain ⟨image, second, firstHandled, secondHandled, reconstructed⟩ :=
      phase_handle_foreign_binding_memory runtime memory owner owned control.execution.application
        clear actor same event payload outputEq codeEq node message candidate call admitted sender
          candidateOwner ready timely vacant unused fixed
    have equalNext : second = next := Option.some.inj (secondHandled.symm.trans accepted)
    subst second
    exact ⟨memory, image, owned, valid, firstHandled, reconstructed⟩

end Vegas.EventGraphRuntime.BindingShadow
