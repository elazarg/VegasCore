/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketBoundaryWaiting

/-! # Waiting for the first owner callback under actual recovery service -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable [Fintype Player]
  {bounds : MessageBounds (graph setup)}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat} {scheduler : (recoveryApplication runtime leaks).Scheduler}
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : Recovery.Opportunity runtime leaks initial horizon scheduler delay)
  (timely : runtime.AsyncTimely delay bound)

local notation "NativeScheduler" =>
  RecoveryProjection.nativeScheduler runtime leaks scheduler
local notation "Menu" => bounds.onePacketMenu runtime leaks

include initialized nativeLaw opportunity in
private theorem counted_opportunity (control : (application setup runtime leaks).Control)
    (trace : ((Menu).protocol (initialLaw setup) horizon (NativeScheduler)).Trace (some control))
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅)) :
    OpportunityAt runtime leaks control.execution delay := by
  have raw := (Menu).toRawTrace (initialLaw setup) horizon (NativeScheduler) trace
  rw [← nativeLaw] at raw
  exact opportunity.clear_native runtime leaks initialized control raw clear

include initialized nativeLaw in
private theorem counted_complete
    (completes : Recovery.CompletesPlay runtime leaks initial horizon scheduler)
    (control : (application setup runtime leaks).Control)
    (trace : ((Menu).protocol (initialLaw setup) horizon (NativeScheduler)).Trace (some control))
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅))
    (terminal : (application setup runtime leaks).terminal (some control)) :
    control.execution.application.config.cut.Terminal := by
  have raw := (Menu).toRawTrace (initialLaw setup) horizon (NativeScheduler) trace
  rw [← nativeLaw] at raw
  exact Recovery.CompletesPlay.clear_native runtime leaks initialized completes control
    raw clear terminal

include initialized nativeLaw opportunity timely in
theorem recovery_waiting_environment
    {remaining : Nat} {execution : (application setup runtime leaks).Execution}
    (trace : ((Menu).protocol (initialLaw setup) horizon (NativeScheduler)).Trace
      (some ⟨remaining + 1, none, execution⟩))
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk execution.application ∅))
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (never : ∀ entry ∈ execution.recall owner, ¬ ActivatedAt setup runtime leaks owner event entry)
    (command : (application setup runtime leaks).Command) (next : (application setup runtime
      leaks).Execution)
    (reached : next ∈ (execution.environmentStep (application setup runtime leaks)
      command).support) :
    next.application.config = execution.application.config ∧
      ExclusionEvidence 0 ∅ (RecoveryState.mk next.application ∅) := by
  exact counted_waiting_environment (runtime := runtime) (counted_opportunity (runtime := runtime)
    initialized nativeLaw opportunity)
    timely trace clear ordered decoded intendedPoint owner event owned ready never command next
    reached

include initialized nativeLaw opportunity timely in
theorem recovery_waiting_until_firstActivation
    (completes : Recovery.CompletesPlay runtime leaks initial horizon scheduler)
    (certificate : ((Menu).protocol (initialLaw setup) horizon
      (NativeScheduler)).WellFoundedHistories)
    (players : ∀ player, ((Menu).information (initialLaw setup) horizon
      (NativeScheduler)).BehavioralPolicy player)
    (start : ((Menu).protocol (initialLaw setup) horizon (NativeScheduler)).History)
    {remaining : Nat} {execution : (application setup runtime leaks).Execution}
    (current : start.state = some ⟨remaining, none, execution⟩)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk execution.application ∅))
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (never : ∀ entry ∈ execution.recall owner, ¬ ActivatedAt setup runtime leaks owner event
      entry) :
    ∀ stopped ∈ (((Menu).information (initialLaw setup) horizon
      (NativeScheduler)).runBehavioralUntil certificate players
        (fun history => (application setup runtime leaks).actor history.state = some owner)
          start).support,
      ∃ control, stopped.state = some control ∧ control.actor = some owner ∧
        control.execution.application.config = execution.application.config ∧
        ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) ∧
        control.execution.recall owner = execution.recall owner := by
  exact counted_waiting_until_firstActivation (runtime := runtime)
    (counted_opportunity (runtime := runtime) initialized nativeLaw opportunity) timely
    (counted_complete (runtime := runtime) initialized nativeLaw completes) certificate players
      start current clear
    ordered decoded intendedPoint owner event owned ready never

include initialized nativeLaw opportunity timely in
theorem recovery_boundary_firstActivation
    (completes : Recovery.CompletesPlay runtime leaks initial horizon scheduler)
    (certificate : ((Menu).protocol (initialLaw setup) horizon
      (NativeScheduler)).WellFoundedHistories)
    (players : ∀ player, ((Menu).information (initialLaw setup) horizon
      (NativeScheduler)).BehavioralPolicy player)
    (start : ((Menu).protocol (initialLaw setup) horizon (NativeScheduler)).History)
    {rank : Nat} {execution : (application setup runtime leaks).Execution}
    (current : start.state =
      some ⟨horizon - execution.environmentRecall.length, none, execution⟩)
    (boundary : ReachedBoundary setup runtime leaks horizon (NativeScheduler) rank execution)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk execution.application ∅))
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (owner : Player) (event : (graph setup).EventId) (atRank : event.val = rank)
    (owned : (graph setup).actor? event = some owner) :
    ∀ stopped ∈ (((Menu).information (initialLaw setup) horizon
      (NativeScheduler)).runBehavioralUntil certificate players
        (fun history => (application setup runtime leaks).actor history.state = some owner)
          start).support,
      ∃ (remaining : Nat) (anchor : (application setup runtime leaks).Execution),
        stopped.state = some ⟨remaining, some owner, anchor⟩ ∧
        anchor.application.config = execution.application.config ∧
        ExclusionEvidence 0 ∅ (RecoveryState.mk anchor.application ∅) ∧
        anchor.recall owner = execution.recall owner ∧
        pendingEvent setup runtime leaks owner
          (some (anchor.recall owner,
            anchor.observe (application setup runtime leaks) owner)) = some event ∧
        ∀ entry ∈ anchor.recall owner, ¬ ActivatedAt setup runtime leaks owner event entry := by
  exact counted_boundary_firstActivation (runtime := runtime)
    (counted_opportunity (runtime := runtime) initialized nativeLaw opportunity) timely
    (counted_complete (runtime := runtime) initialized nativeLaw completes) certificate players
      start current boundary
    clear decoded intendedPoint owner event atRank owned

end Vegas
