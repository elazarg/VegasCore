/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryPendingCompletion

/-! # The current-event phase stopped before public exclusion -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat}
  {recoveryScheduler : (recoveryApplication (runtime setup) leaks).Scheduler}
  (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon recoveryScheduler)

local notation "scheduler" => RecoveryProjection.nativeScheduler (runtime setup) leaks
  recoveryScheduler
local notation "menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

include initialized nativeLaw completes in
/-- The first public failure cannot precede completion of the pending source
event. Adding that stopping condition therefore preserves its entire phase law. -/
theorem recovery_pending_until_eq_clearUntil
    (certificate : (E).WellFoundedHistories) (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅))
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event) :
    (N).runBehavioralUntil certificate players
        (LateStopped setup leaks bounds horizon scheduler rank) start =
      (N).runBehavioralUntil certificate players
        (fun final => LateStopped setup leaks bounds horizon scheduler rank final ∨
          ¬ Clear final.state) start := by
  classical
  let late := LateStopped setup leaks bounds horizon scheduler rank
  let early := fun final : (E).History => late final ∨ ¬ Clear final.state
  have splitting : ∀ history,
      (N).runBehavioralUntil certificate players late history =
        ((N).runBehavioralUntil certificate players early history).bind
          ((N).runBehavioralUntil certificate players late) := by
    intro history
    induction history using certificate.induction with
    | _ history ih =>
    by_cases halted : early history
    · rw [(N).runBehavioralUntil_of_stopped certificate players halted, PMF.pure_bind]
    have going : ¬ late history := fun stopped => halted (Or.inl stopped)
    by_cases terminal : (E).terminal history.state
    · rw [(N).runBehavioralUntil_of_terminal certificate players terminal,
        (N).runBehavioralUntil_of_terminal certificate players terminal, PMF.pure_bind,
        (N).runBehavioralUntil_of_terminal certificate players terminal]
    rw [(N).runBehavioralUntil_of_running certificate players going terminal,
      (N).runBehavioralUntil_of_running certificate players halted terminal, PMF.bind_bind]
    apply bind_congr_on_support
    intro next member
    exact ih next ((N).mem_support_runBehavioralFrom_one players terminal member).1
  rw [splitting start]
  calc
    _ = ((N).runBehavioralUntil certificate players early start).bind PMF.pure := by
      apply bind_congr_on_support
      intro final member
      obtain ⟨anchor, state, _completed, nextPrefix, _seen⟩ := recovery_pending_stop_completed
        initialized nativeLaw completes true certificate players start current ordered clear
          event ready
        final member
      exact (N).runBehavioralUntil_of_stopped certificate players ⟨_, state, nextPrefix⟩
    _ = _ := PMF.bind_pure _

end Vegas
