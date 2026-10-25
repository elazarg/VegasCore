/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseRecoveryInformation
import Vegas.Game.SequentialPhaseObservation
import Vegas.Game.PhaseClearPacketInformation
import Interaction.ReactiveRecordedEnvironment
import Interaction.ReactiveInvariantPrefix

/-! # Scheduler reconstruction before a public exclusion

The decoder reads only the original scheduler's environment view and its own
recorded environment entries. Exact reconstruction is proved on all actual clear
counted histories; retired failure snapshots are not reconstructed after exclusion.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.SequentialPhaseSchedulerInformation

open SourceProgram EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] in
private theorem restamp_messages {graph : Vegas.EventGraph Player L}
    (plan : RuntimePhasePlan graph) (messages : List (Message Player (CommitAttemptPacket graph)))
    (fixed : ∀ message ∈ messages,
      plan.stampPacket message.payload.packet = message.payload) :
    (messages.map (Message.mapPayload CommitAttemptPacket.packet)).map
      (Message.mapPayload plan.stampPacket) = messages := by
  rw [List.map_map]
  calc
    _ = messages.map id := List.map_congr_left fun message present => by
      cases message with
      | mk identity packet => exact congrArg (Message.mk identity) (fixed _ present)
    _ = messages := List.map_id messages

variable {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)
  (runtime : EventGraphRuntime (EventGraph.withMode (toEventGraph program) .sequential))
  (leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket (EventGraph.withMode (toEventGraph program) .sequential)))
  (recoveryLeaks : MessageNetwork.ObservationRule Player
    (WitnessedPacket (EventGraph.withMode (toEventGraph program) .sequential)))

local notation "P" => phaseApplication runtime leaks
local notation "R" => runtime.recoveryApplication recoveryLeaks

/-- Restore the same physical command in the phase application. -/
def command : (R).Command → (P).Command
  | .activate who => .activate who
  | .include identity => .include identity
  | .application operation => .application operation
  | .wait => .wait

@[simp] theorem command_project (operation : (P).Command) :
    command program runtime leaks recoveryLeaks
      (PhaseRecoveryProjection.command runtime leaks recoveryLeaks operation) = operation := by
  cases operation <;> rfl

/-- Reconstruct static packet tags and clear phase metadata from the recovery public input. -/
def environmentView (view : (R).EnvironmentView) : (P).EnvironmentView where
  network := view.network.mapPayload (sequentialRuntimePhasePlan program).stampPacket
  application := SequentialPhaseObservation.publicView program
    view.application.1 view.application.2
  receipts := view.receipts

/-- Decode one entry using only its own original observation and command. -/
def environmentEntry (entry : (R).EnvironmentEntry) : (P).EnvironmentEntry where
  beforeView := environmentView program runtime leaks recoveryLeaks entry.beforeView
  command := command program runtime leaks recoveryLeaks entry.command

/-- An recovery scheduler can run the phase scheduler on its decoded own input. -/
def scheduler (original : (P).Scheduler) : (R).Scheduler := fun past view =>
  (original (past.map (environmentEntry program runtime leaks recoveryLeaks))
    (environmentView program runtime leaks recoveryLeaks view)).map
      (PhaseRecoveryProjection.command runtime leaks recoveryLeaks)

variable [Fintype Player]
  (bounds : MessageBounds (EventGraph.withMode (toEventGraph program) .sequential))

/-- The entire actual scheduler view reconstructs, including pending and earlier inputs. -/
theorem environmentView_history
    (inputs : PMF ((EventGraph.withMode (toEventGraph program) .sequential)).Inputs)
    (horizon : Nat) (original : (P).Scheduler) {control : (P).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial (sequentialRuntimePhasePlan program)))
        horizon original).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) :
    environmentView program runtime leaks recoveryLeaks
      (PhaseRecoveryProjection.environmentView runtime leaks recoveryLeaks
        (control.execution.observeEnvironment (P))) =
      control.execution.observeEnvironment (P) := by
  let plan := sequentialRuntimePhasePlan program
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon
    original trace
  have packets := PhaseCount.clear_network_packets_history runtime leaks plan bounds inputs
    horizon original trace clear
  have pending := restamp_messages plan control.execution.network.pending packets.pending
  have ledger := restamp_messages plan control.execution.network.ledger packets.ledger
  have submitted := restamp_messages plan control.execution.network.inputs packets.inputs
  have publicEq := SequentialPhaseObservation.publicView_history program runtime leaks inputs
    horizon original rawTrace clear
  have recover : SequentialPhaseObservation.publicView program
        control.execution.application.current.native.publicView
        control.execution.application.current.excluded =
      control.execution.application.publicView := by
    rw [clear]
    exact publicEq.symm
  dsimp only [environmentView, PhaseRecoveryProjection.environmentView,
    ReactiveApplication.Execution.observeEnvironment, MessageNetwork.publicView,
    MessageNetwork.PublicView.mapPayload]
  rw [pending, ledger, submitted]
  change ReactiveApplication.EnvironmentView.mk (app := (P)) _
    (SequentialPhaseObservation.publicView program
      control.execution.application.current.native.publicView
      control.execution.application.current.excluded) _ = _
  rw [recover]
  rfl

/-- Each recalled scheduler view is reconstructed at its genuine earlier counted
prefix. Public exclusion monotonicity ensures that prefix is also clear. -/
theorem recall_history
    (inputs : PMF ((EventGraph.withMode (toEventGraph program) .sequential)).Inputs)
    (horizon : Nat) (original : (P).Scheduler) {control : (P).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial (sequentialRuntimePhasePlan program)))
        horizon original).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) :
    (control.execution.environmentRecall.map
      (PhaseRecoveryProjection.environmentEntry runtime leaks recoveryLeaks)).map
        (environmentEntry program runtime leaks recoveryLeaks) =
      control.execution.environmentRecall := by
  let plan := sequentialRuntimePhasePlan program
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have monotone := phaseApplication_exclusion_monotone runtime leaks
  have lowerInvariant (lower : Finset Player) :
      (P).Invariant (fun state => lower ⊆ state.current.excluded) := {
    submit := fun state actor material holds =>
      holds.trans (monotone.submit state actor material)
    handle := fun state message next holds accepted =>
      holds.trans (monotone.handle state message next accepted)
    environment := fun state operation next holds reached =>
      holds.trans (monotone.environment state operation next reached) }
  have each (entry : (P).EnvironmentEntry)
      (member : entry ∈ control.execution.environmentRecall) :
      environmentEntry program runtime leaks recoveryLeaks
        (PhaseRecoveryProjection.environmentEntry runtime leaks recoveryLeaks entry) = entry := by
    obtain ⟨before, prior, kept, _inactive, _positive, viewed, _selected, _later⟩ :=
      menu.recorded_environment_prefix initial horizon original control trace entry member
    have earlierClear : before.execution.application.current.excluded = ∅ := by
      have retained := (lowerInvariant before.execution.application.current.excluded).tracePrefix
        menu initial horizon original before control prior trace kept (Finset.Subset.refl _)
      exact Finset.subset_empty.mp (by simpa only [clear] using retained)
    have viewedBack := environmentView_history program runtime leaks recoveryLeaks bounds inputs
      horizon original prior earlierClear
    rw [← viewed] at viewedBack
    change (⟨environmentView program runtime leaks recoveryLeaks
        (PhaseRecoveryProjection.environmentView runtime leaks recoveryLeaks entry.beforeView),
      command program runtime leaks recoveryLeaks
        (PhaseRecoveryProjection.command runtime leaks recoveryLeaks entry.command)⟩ :
          (P).EnvironmentEntry) = entry
    rw [viewedBack, command_project]
  rw [List.map_map]
  calc
    _ = control.execution.environmentRecall.map id := List.map_congr_left each
    _ = control.execution.environmentRecall := List.map_id _

/-- At every actual clear counted history the derived scheduler has exactly the
projected original command law, with no scheduler-memory or kernel-equality premise. -/
theorem scheduler_history
    (inputs : PMF ((EventGraph.withMode (toEventGraph program) .sequential)).Inputs)
    (horizon : Nat) (original : (P).Scheduler) {control : (P).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial (sequentialRuntimePhasePlan program)))
        horizon original).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) :
    scheduler program runtime leaks recoveryLeaks original
      (PhaseRecoveryProjection.execution runtime leaks recoveryLeaks
        control.execution).environmentRecall
      ((PhaseRecoveryProjection.execution runtime leaks recoveryLeaks
        control.execution).observeEnvironment (R)) =
    (original control.execution.environmentRecall
      (control.execution.observeEnvironment (P))).map
        (PhaseRecoveryProjection.command runtime leaks recoveryLeaks) := by
  unfold scheduler
  rw [PhaseRecoveryProjection.observeEnvironment]
  change (original ((control.execution.environmentRecall.map
      (PhaseRecoveryProjection.environmentEntry runtime leaks recoveryLeaks)).map
        (environmentEntry program runtime leaks recoveryLeaks))
      (environmentView program runtime leaks recoveryLeaks
        (PhaseRecoveryProjection.environmentView runtime leaks recoveryLeaks
          (control.execution.observeEnvironment (P))))).map
      (PhaseRecoveryProjection.command runtime leaks recoveryLeaks) = _
  rw [
    recall_history program runtime leaks recoveryLeaks bounds inputs horizon original trace clear,
    environmentView_history program runtime leaks recoveryLeaks bounds inputs horizon original
      trace clear]

end Vegas.EventGraphRuntime.SequentialPhaseSchedulerInformation
