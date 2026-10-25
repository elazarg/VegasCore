/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseRecoveryInformation
import Vegas.Game.SequentialPhaseObservation
import Vegas.Game.PhaseClearPacketInformation
import Interaction.ReactiveRecordedResponse
import Interaction.ReactiveRecallInvariant

/-! # Reconstructing clear phase player observations from recovery inputs

Only the supplied player's original current view and own recall are decoded.
Actual phase geometry and authored-packet facts justify the reconstruction;
neither builder recall nor an omniscient history is an argument of the decoder.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.SequentialPhasePlayerInformation

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



variable (runtime : EventGraphRuntime (EventGraph.withMode (toEventGraph program) .sequential))
  (leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket (EventGraph.withMode (toEventGraph program) .sequential)))
  (recoveryLeaks : MessageNetwork.ObservationRule Player
    (WitnessedPacket (EventGraph.withMode (toEventGraph program) .sequential)))

local notation "P" => phaseApplication runtime leaks
local notation "R" => runtime.recoveryApplication recoveryLeaks

/-- Decode the static phase metadata and packet tags from the recovery current player input. -/
def playerView (view : (R).PlayerView) : (P).PlayerView where
  messages := view.messages.mapPayload (sequentialRuntimePhasePlan program).stampPacket
  application := (view.application.1,
    SequentialPhaseObservation.publicView program view.application.1.publicView view.application.2)
  receipts := view.receipts

/-- Decode an original own response entry without adding hidden strategy memory. -/
def playerEntry (entry : (R).PlayerEntry) : (P).PlayerEntry where
  beforeView := playerView program runtime leaks recoveryLeaks entry.beforeView
  action := PhaseRecoveryProjection.phaseAction runtime leaks recoveryLeaks entry.action
  emitted := entry.emitted.map
    (Message.mapPayload (sequentialRuntimePhasePlan program).stampPacket)

/-- The full input decoder uses only own recall and the current observed player view. -/
def information (input : (R).Info) : (P).Info :=
  input.map fun pair =>
    (pair.1.map (playerEntry program runtime leaks recoveryLeaks),
      playerView program runtime leaks recoveryLeaks pair.2)

variable [Fintype Player]
  (bounds : MessageBounds (EventGraph.withMode (toEventGraph program) .sequential))

/-- Every actual clear counted callback recovers its exact current player observation. -/
theorem playerView_history
    (inputs : PMF ((EventGraph.withMode (toEventGraph program) .sequential)).Inputs)
    (horizon : Nat)
    (scheduler : (P).Scheduler) {control : (P).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial (sequentialRuntimePhasePlan program)))
        horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) (who : Player) :
    playerView program runtime leaks recoveryLeaks
        (PhaseRecoveryProjection.playerView runtime leaks recoveryLeaks
          (control.execution.observe (P) who)) = control.execution.observe (P) who := by
  let plan := sequentialRuntimePhasePlan program
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon
    scheduler trace
  have packets := PhaseCount.clear_network_packets_history runtime leaks plan bounds inputs
    horizon scheduler trace clear
  have leaked := restamp_messages plan (control.execution.network.leaked who)
    (packets.leaked who)
  have ledger := restamp_messages plan control.execution.network.ledger packets.ledger
  have publicEq := SequentialPhaseObservation.publicView_history program runtime leaks inputs
    horizon scheduler rawTrace clear
  have recover : SequentialPhaseObservation.publicView program
        control.execution.application.current.native.publicView
        control.execution.application.current.excluded =
      control.execution.application.publicView := by
    rw [clear]
    exact publicEq.symm
  dsimp only [playerView, PhaseRecoveryProjection.playerView,
    ReactiveApplication.Execution.observe, MessageNetwork.observe,
    MessageNetwork.PlayerView.mapPayload]
  rw [leaked, ledger]
  change ReactiveApplication.PlayerView.mk (app := (P)) _
      (control.execution.application.current.native.playerView who,
        SequentialPhaseObservation.publicView program
          control.execution.application.current.native.publicView
          control.execution.application.current.excluded) _ = _
  rw [recover]
  rfl

/-- The complete own past also reconstructs exactly; each remembered view is justified
at its actual earlier legal callback, not by a chosen representative history. -/
theorem recall_history (inputs :
    PMF ((EventGraph.withMode (toEventGraph program) .sequential)).Inputs)
    (horizon : Nat)
    (scheduler : (P).Scheduler) {control : (P).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial (sequentialRuntimePhasePlan program)))
        horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) (who : Player) :
    ((control.execution.recall who).map
      (PhaseRecoveryProjection.playerEntry runtime leaks recoveryLeaks)).map
        (playerEntry program runtime leaks recoveryLeaks) = control.execution.recall who := by
  let plan := sequentialRuntimePhasePlan program
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let rawTrace := menu.toRawTrace initial horizon scheduler trace
  have monotone := phaseApplication_exclusion_monotone runtime leaks
  have lowerInvariant (lower : Finset Player) :
      (P).Invariant (fun state => lower ⊆ state.current.excluded) := {
    submit := fun state actor material holds =>
      holds.trans (monotone.submit state actor material)
    handle := fun state message next holds accepted =>
      holds.trans (monotone.handle state message next accepted)
    environment := fun state command next holds reached =>
      holds.trans (monotone.environment state command next reached) }
  have ownBound := (P).recallBound_history (fun observation => observation.2.excluded)
    (fun state => state.current.excluded) (fun _ _ => rfl) lowerInvariant
    initial horizon scheduler control rawTrace
  have inputRecall := (P).history_inputRecall initial horizon scheduler rawTrace
  have each (entry : (P).PlayerEntry) (member : entry ∈ control.execution.recall who) :
      playerEntry program runtime leaks recoveryLeaks
        (PhaseRecoveryProjection.playerEntry runtime leaks recoveryLeaks entry) = entry := by
    obtain ⟨before, prior, _earlier, _active, viewed, _allowed, _later⟩ :=
      menu.recorded_response_prefix initial horizon scheduler control trace who entry member
    have flag : entry.beforeView.application.2.excluded = ∅ :=
      Finset.subset_empty.mp (by simpa only [clear] using ownBound who entry member)
    have priorClear : before.execution.application.current.excluded = ∅ := by
      have flags := congrArg (fun view : (P).PlayerView => view.application.2.excluded) viewed
      change entry.beforeView.application.2.excluded =
        before.execution.application.current.excluded at flags
      exact flags.symm.trans flag
    have viewedBack := playerView_history program runtime leaks recoveryLeaks bounds inputs
      horizon scheduler prior priorClear who
    rw [← viewed] at viewedBack
    have emittedBack : (entry.emitted.map (Message.mapPayload CommitAttemptPacket.packet)).map
        (Message.mapPayload plan.stampPacket) = entry.emitted := by
      cases emitted : entry.emitted with
      | none => simp only [Option.map_none]
      | some message =>
          have present : message ∈ (P).outputs (control.execution.recall who) :=
            List.mem_filterMap.mpr ⟨entry, member, emitted⟩
          rw [← inputRecall who] at present
          have fixed := PhaseCount.clear_input_restamp_history runtime leaks plan bounds inputs
            horizon scheduler trace clear message (List.mem_filter.mp present).1
          have envelope : Message.mapPayload plan.stampPacket
              (Message.mapPayload CommitAttemptPacket.packet message) = message := by
            cases message with
            | mk identity packet => exact congrArg (Message.mk identity) fixed
          simpa only [emitted, Option.map_some] using congrArg some envelope
    change (⟨playerView program runtime leaks recoveryLeaks
        (PhaseRecoveryProjection.playerView runtime leaks recoveryLeaks entry.beforeView),
      PhaseRecoveryProjection.phaseAction runtime leaks recoveryLeaks
        (PhaseRecoveryProjection.action runtime leaks recoveryLeaks entry.action),
      (entry.emitted.map (Message.mapPayload CommitAttemptPacket.packet)).map
        (Message.mapPayload plan.stampPacket)⟩ : (P).PlayerEntry) = entry
    rw [viewedBack, PhaseRecoveryProjection.phaseAction_action, emittedBack]
  rw [List.map_map]
  calc
    _ = (control.execution.recall who).map id := List.map_congr_left each
    _ = control.execution.recall who := List.map_id (control.execution.recall who)

/-- Actual clear counted information fibers have an inverse using recovery player
information alone. No restriction to honest histories or equilibrium support is made. -/
theorem information_history (inputs :
    PMF ((EventGraph.withMode (toEventGraph program) .sequential)).Inputs)
    (horizon : Nat)
    (scheduler : (P).Scheduler) {control : (P).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial (sequentialRuntimePhasePlan program)))
        horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) (who : Player) :
    information program runtime leaks recoveryLeaks
        (PhaseRecoveryProjection.information runtime leaks recoveryLeaks
          ((P).observe who (some control))) = (P).observe who (some control) := by
  by_cases active : control.actor = some who
  · simp only [ReactiveApplication.observe, active, ↓reduceIte, information,
      PhaseRecoveryProjection.information, Option.map_some]
    rw [recall_history program runtime leaks recoveryLeaks bounds inputs horizon scheduler
      trace clear who,
      playerView_history program runtime leaks recoveryLeaks bounds inputs horizon scheduler
        trace clear who]
  · simp only [ReactiveApplication.observe, active, ↓reduceIte, information,
      PhaseRecoveryProjection.information, Option.map_none]

end Vegas.EventGraphRuntime.SequentialPhasePlayerInformation
