/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingBindingPersistence
import Vegas.Pending.PhaseBindingReceiptResolution
import Vegas.Pending.PhaseClearHistory

/-! # The original second binding installs the genuine publication-only suffix -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- A true original Bob receipt at a still-original query is current native
completion, not just completion of an unrelated archived attempt. -/
theorem original_bob_receipt_completed (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt)
    (accepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob
      current.execution) :
    bobBinding ∈ current.execution.application.current.native.config.cut.completed := by
  have resolved := PhaseService.bindingAccepted_resolved runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon selected trace (originalCoordinate bob) bob
      accepted
  change (⟨originalAttempt, bobBinding⟩ : CommitAttemptEvent graph).Resolved
    current.execution.application at resolved
  rcases resolved with generation | phase | ⟨_same, completed⟩
  · rw [original] at generation
    exact (Nat.lt_irrefl _ generation).elim
  · rw [original] at phase
    exact (Nat.lt_irrefl _ phase).elim
  · exact completed

/-- The actual accepting Alice inclusion after Bob's original true receipt
preserves its literal native result through clear settlement and leaves only
the publication suffix. The source prefix and inclusion are arbitrary raw
histories; no prescribed original own word is required. -/
theorem original_second_binding_publication_prefix (selected : app.Scheduler)
    (remaining : Nat) (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon selected).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (original : execution.application.attempt = originalAttempt)
    (clear : execution.application.current.excluded = ∅)
    (bobAccepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob
      execution)
    (message : Message Player (CommitAttemptPacket graph))
    (lookup : execution.network.lookup message.id = some message) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment aliceBinding candidate)
    (native : EventGraphRuntime.State graph)
    (nativeHandled : handle runtime execution.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = some native)
    (nextState : PhaseRuntimeState graph)
    (normalized : nextState =
      ({ execution.application with current := (execution.application.current.inclusionResult
        message.payload.packet.call native) } : PhaseRuntimeState graph).normalize)
    (accepted : app.handle execution.application message = some nextState)
    (chosen : (.«include» message.id : app.Command) ∈
      (selected execution.environmentRecall (execution.observeEnvironment app)).support)
    (next : app.Execution)
    (included : next ∈ (execution.environmentStep app (.«include» message.id)).support) :
    next.application.phases <:+ [publicationPhase] ∧
      next.application.current.native = native ∧
      next.application.current.excluded = ∅ := by
  have raw := rawMenu.toRawTrace initial horizon selected trace
  have bobDone := original_bob_receipt_completed selected ⟨remaining + 1, none, execution⟩ raw
    original bobAccepted
  have bobNext : bobBinding ∈ native.config.cut.completed :=
    handle_completed_subset runtime execution.application.current.native native
      ⟨message.id, message.payload.packet.call⟩ nativeHandled bobDone
  obtain ⟨event, named, _ready, aliceDone⟩ := handle_completes runtime
    execution.application.current.native native ⟨message.id, message.payload.packet.call⟩
      nativeHandled
  have sameEvent : event = aliceBinding := by
    apply Option.some.inj
    exact named.symm.trans (by rw [call]; rfl)
  subst event
  have rawClear : (execution.application.current.inclusionResult
      message.payload.packet.call native).excluded = ∅ := by
    rw [call]
    exact clear
  have nextClear : nextState.current.excluded = ∅ := by
    rw [normalized]
    exact ((PhaseRuntimeState.settle_physical _ _ _ _ _).1).trans rawClear
  have nativeEq : nextState.current.native = native := by
    rw [normalized]
    exact congrArg RecoveryState.native (PhaseRuntimeState.normalize_of_clear
      ({ execution.application with current := (execution.application.current.inclusionResult
        message.payload.packet.call native) } : PhaseRuntimeState graph)
      (normalized ▸ nextClear)).1
  have includedApplication : next.application = nextState := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at included
    cases (PMF.mem_support_pure_iff _ _).mp included
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      lookup, accepted, Option.getD_some]
  obtain ⟨nextTrace⟩ := rawMenu.trace_environment initial horizon selected remaining execution next
    (.«include» message.id) trace chosen included
  have nextRaw := rawMenu.toRawTrace initial horizon selected nextTrace
  have finalNative : next.application.current.native = native :=
    (congrArg (fun state : PhaseRuntimeState graph => state.current.native)
      includedApplication).trans nativeEq
  have aliceFinal : aliceBinding ∈ next.application.current.native.config.cut.completed := by
    rw [finalNative]
    exact aliceDone
  have bobFinal : bobBinding ∈ next.application.current.native.config.cut.completed := by
    rw [finalNative]
    exact bobNext
  refine ⟨completed_bindings_publication_tail selected ⟨remaining, none, next⟩ nextRaw
    aliceFinal bobFinal, finalNative, ?_⟩
  rw [includedApplication]
  exact nextClear

end Vegas.Examples.CommitSeedSignalling
