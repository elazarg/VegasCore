/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNamespace
import Vegas.Pending.ReactiveCountAudit

/-! # Authentic packet namespaces follow physical emission order

Attempt identifiers are attached by the actual application. Monotone runtime
namespaces therefore bound every signed input and order each principal's inputs
by their permanent serials, independently of count cleanliness or scheduling.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The complete authenticated input list retains its actual namespace order. -/
structure InputNamespaces (execution : (app).Execution) : Prop where
  ordered : execution.application.Ordered
  serials : execution.InputSerialsInOrder (app)
  bounded : ∀ message ∈ execution.network.inputs,
    message.payload.attempt.generation ≤ execution.application.attempt.generation ∧
      message.payload.attempt.phase ≤ execution.application.attempt.phase
  monotone : ∀ first ∈ execution.network.inputs, ∀ second ∈ execution.network.inputs,
    first.sender = second.sender → first.id.2 < second.id.2 →
      first.payload.attempt.generation ≤ second.payload.attempt.generation ∧
        first.payload.attempt.phase ≤ second.payload.attempt.phase

namespace InputNamespaces

variable {runtime leaks}

theorem initial (state : PhaseRuntimeState graph) (ordered : state.Ordered) :
    InputNamespaces runtime leaks (ReactiveApplication.Execution.initial (app) state) :=
  ⟨ordered, fun _ => rfl, fun _ impossible => (List.not_mem_nil impossible).elim,
    fun _ impossible => (List.not_mem_nil impossible).elim⟩

theorem respond {execution : (app).Execution} (valid : InputNamespaces runtime leaks execution)
    (who : Player) (action : (app).Action) :
    InputNamespaces runtime leaks (execution.respond (app) who action) := by
  cases action with
  | mk transmission =>
      cases transmission with
      | none => exact ⟨valid.ordered, valid.serials, valid.bounded, valid.monotone⟩
      | some material =>
          let message : Message Player (CommitAttemptPacket graph) :=
            ⟨(who, execution.network.nextSerial who), (app).packet
              ((app).submit execution.application who material) who
              (execution.network.known who) material⟩
          have packetNamespace : message.payload.attempt = execution.application.attempt := rfl
          have inputs : (execution.respond (app) who ⟨some material⟩).network.inputs =
              List.append execution.network.inputs [message] := rfl
          refine ⟨valid.ordered,
            ((app).inputSerialsInOrderInvariant (fun _ _ => PMF.pure .wait)).respond
              execution who ⟨some material⟩ valid.serials, ?_, ?_⟩
          · intro packet present
            rw [inputs] at present
            rcases List.mem_append.mp present with old | new
            · exact valid.bounded packet old
            · rw [List.mem_singleton.mp new, packetNamespace]
              exact ⟨le_rfl, le_rfl⟩
          · intro first firstMem second secondMem same lower
            rw [inputs] at firstMem secondMem
            rcases List.mem_append.mp firstMem with firstOld | firstNew
            · rcases List.mem_append.mp secondMem with secondOld | secondNew
              · exact valid.monotone first firstOld second secondOld same lower
              · rw [List.mem_singleton.mp secondNew, packetNamespace]
                exact valid.bounded first firstOld
            · rw [List.mem_singleton.mp firstNew] at same lower ⊢
              rcases List.mem_append.mp secondMem with secondOld | secondNew
              · have previous := valid.serials.serial_lt secondOld
                change who = second.sender at same
                change execution.network.nextSerial who < second.id.2 at lower
                rw [← same] at previous
                omega
              · rw [List.mem_singleton.mp secondNew] at lower
                exact (Nat.lt_irrefl _ lower).elim

theorem environment {execution next : (app).Execution}
    (valid : InputNamespaces runtime leaks execution) (command : (app).Command)
    (reached : next ∈ (execution.environmentStep (app) command).support) :
    InputNamespaces runtime leaks next := by
  have progress := (phaseApplication_namespace_progress runtime leaks).environmentStep
    execution next command reached valid.ordered
  have inputs := (app).environmentStep_inputs execution next command reached
  refine ⟨(phaseApplication_seedOrder runtime leaks).environmentStep execution next command
    valid.ordered reached, ?_, ?_, ?_⟩
  · intro who
    rw [inputs, (app).environmentStep_nextSerial execution next command reached]
    exact valid.serials who
  · intro message present
    rw [inputs] at present
    obtain ⟨generation, phase⟩ := valid.bounded message present
    exact ⟨generation.trans progress.1, phase.trans progress.2⟩
  · intro first firstMem second secondMem same lower
    rw [inputs] at firstMem secondMem
    exact valid.monotone first firstMem second secondMem same lower

end InputNamespaces

/-- Actual raw execution histories supply namespace monotonicity for every
signed input; no posterior, probability, service or packet-correctness premise. -/
theorem inputNamespaces_history (initial : PMF (app).State)
    (initialized : ∀ state ∈ initial.support, state.Ordered)
    (horizon : Nat) (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((app).protocol initial horizon scheduler).Trace (some control)) :
    InputNamespaces runtime leaks control.execution := by
  have invariant : (app).ServiceInvariant scheduler (InputNamespaces runtime leaks) := {
    respond := fun _ who action valid => InputNamespaces.respond valid who action
    environment := fun _ _ command valid _ reached =>
      InputNamespaces.environment valid command reached }
  exact invariant.history initial horizon
    (fun state supported => InputNamespaces.initial state (initialized state supported)) trace

end Vegas.EventGraphRuntime
