/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAsyncTimeliness
import Vegas.Pending.ExclusionService

/-! # Protected calls before and at the first recovery exclusion -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol Interaction EventGraphRuntime
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
  {initial : PMF (RecoveryState (serviceGraph setup mode))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (⟨State.initial inputs, ∅⟩ : RecoveryState (serviceGraph setup mode)))
  (nativeLaw : initial.map RecoveryState.native = serviceInitialLaw setup mode)
  {horizon : Nat}
  {scheduler : ((serviceRuntime setup mode deadline).recoveryApplication leaks).Scheduler}
  {bound : (serviceGraph setup mode).EventId → Nat}
  (inclusion : Recovery.ProtectedInclusion (serviceRuntime setup mode deadline) leaks initial
    horizon scheduler bound)

include initialized nativeLaw inclusion in
/-- Every fresh call is settled along a clear native history of the actual recovery
service. The service premise is used only at genuine clear predecessor histories. -/
theorem recovery_settlesFreshCalls_history
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner) :
    ∀ {state}
      (_trace : ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon
        (RecoveryProjection.nativeScheduler (serviceRuntime setup mode deadline) leaks
          scheduler)).Trace state),
      (∀ current, state = some current → PublicExclusionRecord
        (⟨current.execution.application, ∅⟩ : RecoveryState (serviceGraph setup mode))) →
      ReactiveApplication.serviceInvariant (SettlesFreshCalls setup leaks owner event bound) state
  | _, .start, _ => trivial
  | _, .extend (source := before) prior joint _ reached, clear => by
      have beforeClear := native_clear_before_transition (serviceRuntime setup mode deadline)
        leaks (serviceInitialLaw setup mode) (by
          intro native supported
          obtain ⟨source, _, rfl⟩ := PMF.support_map .. ▸ supported
          exact ⟨_, rfl⟩) horizon
        (RecoveryProjection.nativeScheduler (serviceRuntime setup mode deadline) leaks scheduler)
        prior joint reached clear
      have valid := recovery_settlesFreshCalls_history owner event owned prior beforeClear
      cases before with
      | none =>
          obtain ⟨inputs, _, rfl⟩ := PMF.support_map .. ▸ reached
          intro earlier entry later message split
          simp [ReactiveApplication.Execution.initial] at split
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact settlesFreshCalls_respond setup leaks owner event bound execution
                (legalFacts setup leaks horizon _ _ prior) who _ valid
          | none =>
              cases remaining with
              | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact valid
              | succ remaining =>
                  obtain ⟨command, _, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  have actualTrace := prior
                  rw [← nativeLaw] at actualTrace
                  have atPrefix := Recovery.ProtectedInclusion.clear_native
                    (serviceRuntime setup mode deadline) leaks initialized inclusion
                    ⟨remaining + 1, none, execution⟩ actualTrace (beforeClear _ rfl)
                  exact settlesFreshCalls_environment setup leaks owner event owned remaining
                    execution atPrefix prior valid command next supported

include initialized nativeLaw inclusion in
/-- A scheduler move from a clear prefix preserves settlement even if that very
move produces the first public exclusion. No service contract is asserted after it. -/
theorem recovery_settlesFreshCalls_environment
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (remaining : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution)
    (prior : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon
      (RecoveryProjection.nativeScheduler (serviceRuntime setup mode deadline) leaks
        scheduler)).Trace (some ⟨remaining + 1, none, execution⟩))
    (clear : PublicExclusionRecord
      (⟨execution.application, ∅⟩ : RecoveryState (serviceGraph setup mode)))
    (command : (serviceApplication setup mode deadline leaks).Command)
    (next : (serviceApplication setup mode deadline leaks).Execution)
    (reached : next ∈ (execution.environmentStep
      (serviceApplication setup mode deadline leaks) command).support) :
    SettlesFreshCalls setup leaks owner event bound next := by
  have valid := recovery_settlesFreshCalls_history setup leaks initialized nativeLaw inclusion
    owner event owned prior (by intro current same; cases Option.some.inj same; exact clear)
  have actualTrace := prior
  rw [← nativeLaw] at actualTrace
  have atPrefix := Recovery.ProtectedInclusion.clear_native (serviceRuntime setup mode deadline)
    leaks initialized inclusion ⟨remaining + 1, none, execution⟩ actualTrace clear
  exact settlesFreshCalls_environment setup leaks owner event owned remaining execution atPrefix
    prior valid command next reached

include initialized nativeLaw inclusion in
/-- At a clear history, an acceptable fresh call is accepted once its protected
window has passed, and any completion already carries its accepting receipt. -/
theorem recovery_prescribed_packet_settles
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon
      (RecoveryProjection.nativeScheduler (serviceRuntime setup mode deadline) leaks
        scheduler)).Trace (some control))
    (clear : PublicExclusionRecord
      (⟨control.execution.application, ∅⟩ : RecoveryState (serviceGraph setup mode)))
    (event : (serviceGraph setup mode).EventId) (owner : Player)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (earlier later : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (entry : (serviceApplication setup mode deadline leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (split : control.execution.recall owner = earlier ++ entry :: later)
    (call : FreshCall setup leaks owner event bound entry message)
    (sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor (serviceRuntime setup mode deadline) leaks other event message.id) :
    (entry.beforeView.application.publicView.clock + bound event <
        control.execution.application.clock →
      (message.id, true) ∈ control.execution.receipts) ∧
      (event ∈ control.execution.application.config.cut.completed →
        (message.id, true) ∈ control.execution.receipts) := by
  have settled := recovery_settlesFreshCalls_history setup leaks initialized nativeLaw inclusion
    owner event owned trace (by intro current same; cases Option.some.inj same; exact clear)
    earlier entry later message split call sole
  refine ⟨fun late => ?_, settled.1⟩
  by_cases completed : event ∈ control.execution.application.config.cut.completed
  · exact settled.1 completed
  · have actualTrace := trace
    rw [← nativeLaw] at actualTrace
    have atPrefix := Recovery.ProtectedInclusion.clear_native (serviceRuntime setup mode deadline)
      leaks initialized inclusion control actualTrace clear
    obtain ⟨accepted, receipt⟩ := atPrefix event owner owned earlier later entry message split
      call.emitted call.authored call.addressed call.ready sole completed late
    exact settled.2.1 accepted receipt

end Vegas
