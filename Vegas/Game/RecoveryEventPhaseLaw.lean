/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryPendingCompletion

/-! # The current-event phase stopped before public exclusion -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

section CountedCompletion

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
local notation "onePacketN" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
  scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler
local notation "ClearState" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk
    native ∅))

/-- A first public failure cannot precede completion of the current
pending event under counted clear terminal completeness. -/
theorem pending_until_eq_clearUntil
    (terminalCompletes : ∀ (final : (application setup runtime leaks).Control),
      ((menu).protocol (initialLaw setup) horizon scheduler).Trace (some final) →
      ExclusionEvidence 0 ∅ (⟨final.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      (application setup runtime leaks).terminal (some final) →
      final.execution.application.config.cut.Terminal)
    (certificate : (E).WellFoundedHistories) (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅))
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event) :
    (N).runBehavioralUntil certificate players
        (LateStopped setup runtime leaks bounds horizon scheduler rank) start =
      (N).runBehavioralUntil certificate players
        (fun final => LateStopped setup runtime leaks bounds horizon scheduler rank final ∨
          ¬ ClearState final.state) start := by
  classical
  let late := LateStopped setup runtime leaks bounds horizon scheduler rank
  let early := fun final : (E).History => late final ∨ ¬ ClearState final.state
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
      obtain ⟨anchor, state, _completed, nextPrefix, _seen⟩ := pending_stop_completed (runtime :=
        runtime)
        terminalCompletes true certificate players start current ordered clear event ready
        final member
      exact (N).runBehavioralUntil_of_stopped certificate players ⟨_, state, nextPrefix⟩
    _ = _ := PMF.bind_pure _

end CountedCompletion

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat}
  {recoveryScheduler : (recoveryApplication runtime leaks).Scheduler}
  (completes : Recovery.CompletesPlay runtime leaks initial horizon recoveryScheduler)

local notation "scheduler" => RecoveryProjection.nativeScheduler runtime leaks
  recoveryScheduler
local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk
    native ∅))

include initialized nativeLaw completes in
/-- The first public failure cannot precede completion of the pending source
event. Adding that stopping condition therefore preserves its entire phase law. -/
theorem recovery_pending_until_eq_clearUntil
    (certificate : (E).WellFoundedHistories) (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅))
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event) :
    (N).runBehavioralUntil certificate players
        (LateStopped setup runtime leaks bounds horizon scheduler rank) start =
      (N).runBehavioralUntil certificate players
        (fun final => LateStopped setup runtime leaks bounds horizon scheduler rank final ∨
          ¬ Clear final.state) start := by
  apply pending_until_eq_clearUntil (runtime := runtime) ?_ certificate players start current
    ordered clear event ready
  exact Recovery.CompletesPlay.clear_counted_native (runtime := runtime) bounds initialized
    nativeLaw completes


end Vegas
