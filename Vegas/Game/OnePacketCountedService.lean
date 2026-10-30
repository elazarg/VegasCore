/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveDecisionPredecessor
import Vegas.Game.OnePacketFirstActivation
import Vegas.Game.SourceServiceSequentialTimeliness
import Vegas.Pending.ReactiveFirstOpportunity
import Vegas.Pending.ExclusionNativeFailure

/-! # Native clock and settlement facts on actual clear counted histories

The service inputs are pointwise conditions at genuine clear one-packet
prefixes. No native raw or recovery-wide contract is required.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol Interaction EventGraphRuntime
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup))

local notation "N" => application setup runtime leaks
local notation "nativeMenu" => MessageBounds.onePacketMenu runtime leaks bounds

/-- Every fresh call settles at every actual clear native counted history under
pointwise counted inclusion. Service is instantiated only at genuine counted prefixes. -/
theorem settlesFreshCalls_counted_clear_history
    (horizon : Nat) (scheduler : (N).Scheduler) (bound : (graph setup).EventId → Nat)
    (inclusion : ∀ control : (N).Control,
      ((nativeMenu).protocol (initialLaw setup) horizon scheduler).Trace (some control) →
      control.execution.application.config.defaulted = ∅ →
      ProtectedInclusionAt runtime leaks control.execution bound)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner) :
    ∀ {state}
      (_trace : ((nativeMenu).protocol (initialLaw setup) horizon scheduler).Trace state),
      (∀ current, state = some current → current.execution.application.config.defaulted = ∅) →
      ReactiveApplication.serviceInvariant
        (SettlesFreshCalls setup leaks owner event bound) state
  | _, .start, _ => trivial
  | _, .extend (source := before) prior joint _ reached, clear => by
      have rawPrior := (nativeMenu).toRawTrace (initialLaw setup) horizon
        scheduler prior
      have beforeClear := native_clear_before_transition runtime leaks
        (initialLaw setup) horizon
        scheduler joint reached clear
      have valid := settlesFreshCalls_counted_clear_history horizon scheduler
        bound inclusion
        owner event
        owned prior beforeClear
      cases before with
      | none =>
          obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ reached
          intro earlier entry later message split
          simp [ReactiveApplication.Execution.initial] at split
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact settlesFreshCalls_respond setup leaks owner event bound execution
                (legalFacts setup leaks horizon _ _ rawPrior) who _ valid
          | none =>
              cases remaining with
              | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact valid
              | succ remaining =>
                  obtain ⟨command, _, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  have atPrefix := inclusion ⟨remaining + 1, none, execution⟩ prior
                    (beforeClear _ rfl)
                  exact SettlesFreshCalls.environment setup leaks owner event owned
                    remaining
                    execution atPrefix rawPrior valid command next supported

/-- One command from an actual clear counted prefix preserves settlement even
when this command creates the first public failure; no service is imposed after it. -/
theorem settlesFreshCalls_counted_clear_environment
    (horizon : Nat) (scheduler : (N).Scheduler) (bound : (graph setup).EventId → Nat)
    (inclusion : ∀ control : (N).Control,
      ((nativeMenu).protocol (initialLaw setup) horizon scheduler).Trace (some control) →
      control.execution.application.config.defaulted = ∅ →
      ProtectedInclusionAt runtime leaks control.execution bound)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (remaining : Nat) (execution : (N).Execution)
    (prior : ((nativeMenu).protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining + 1, none, execution⟩))
    (clear : execution.application.config.defaulted = ∅)
    (command : (N).Command) (next : (N).Execution)
    (reached : next ∈ (execution.environmentStep (N) command).support) :
    SettlesFreshCalls setup leaks owner event bound next := by
  have valid := settlesFreshCalls_counted_clear_history setup runtime leaks bounds horizon
    scheduler bound
    inclusion
    owner event owned prior (by intro current same; cases Option.some.inj same; exact clear)
  have atPrefix := inclusion ⟨remaining + 1, none, execution⟩ prior clear
  have rawPrior := (nativeMenu).toRawTrace (initialLaw setup) horizon
    scheduler prior
  exact SettlesFreshCalls.environment setup leaks owner event owned remaining execution
    atPrefix rawPrior valid command next reached

/-- Actual clear counted prefixes carry accepting receipts for every completed
protected fresh call, and once its original strict protected window has elapsed. -/
theorem prescribed_packet_counted_clear_settles
    (horizon : Nat) (scheduler : (N).Scheduler) (bound : (graph setup).EventId → Nat)
    (inclusion : ∀ control : (N).Control,
      ((nativeMenu).protocol (initialLaw setup) horizon scheduler).Trace (some control) →
      control.execution.application.config.defaulted = ∅ →
      ProtectedInclusionAt runtime leaks control.execution bound)
    (control : (N).Control)
    (trace : ((nativeMenu).protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (clear : control.execution.application.config.defaulted = ∅)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (earlier later : List (N).PlayerEntry) (entry : (N).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup)))
    (split : control.execution.recall owner = earlier ++ entry :: later)
    (call : FreshCall setup leaks owner event bound entry message)
    (sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor runtime leaks other event message.id) :
    (entry.beforeView.application.publicView.clock + bound event <
        control.execution.application.clock → (message.id, true) ∈ control.execution.receipts) ∧
      (event ∈ control.execution.application.config.cut.completed →
        (message.id, true) ∈ control.execution.receipts) := by
  have settled := settlesFreshCalls_counted_clear_history setup runtime leaks bounds horizon
    scheduler bound
    inclusion
    owner event owned trace (by intro current same; cases Option.some.inj same; exact clear)
    earlier entry later message split call sole
  refine ⟨fun late => ?_, settled.1⟩
  by_cases completed : event ∈ control.execution.application.config.cut.completed
  · exact settled.1 completed
  · have atPrefix := inclusion control trace clear
    obtain ⟨accepted, receipt⟩ := atPrefix event owner owned earlier later entry message split
      call.emitted call.authored call.addressed call.ready sole completed late
    exact settled.2.1 accepted receipt


end Vegas
