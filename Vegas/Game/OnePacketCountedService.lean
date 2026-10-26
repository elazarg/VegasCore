/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveDecisionPredecessor
import Vegas.Game.OnePacketFirstActivation
import Vegas.Game.OnePacketFactorization
import Vegas.Game.SourceServiceAsyncTimeliness
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

/-- Every first actual native counted callback fits the original inclusion deadline
under pointwise counted opportunity, including arbitrary prior source counterfactuals. -/
theorem firstActivation_inclusionFits_of_counted_opportunity
    (horizon : Nat) (scheduler : (N).Scheduler) (delay bound : (graph setup).EventId → Nat)
    (opportunity : ∀ control : (N).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      OpportunityAt runtime leaks control.execution delay)
    (timely : runtime.AsyncTimely delay bound)
    {state : (N).ProtocolState}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).Trace state)
    {remaining : Nat} {who : Player} {execution : (N).Execution}
    (current : state = some ⟨remaining, some who, execution⟩)
    (clear : ExclusionEvidence 0 ∅ (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who,
      ¬ ActivatedAt setup runtime leaks who event entry) :
    execution.application.publicView.InclusionFitsDeadline runtime bound event := by
  let service := scheduler
  obtain ⟨previous, ⟨countedTrace⟩, applicationEq, recallEq⟩ :=
    (nativeMenu).decision_predecessor (initialLaw setup) horizon service trace current
  have spec := PublicView.ownTurn?_spec _ who event turn
  have ready := (execution.application.publicView_eventReady event).mp spec.1
  have strategic : ((graph setup).actor? event).isSome = true := by rw [spec.2]; rfl
  have previousTrace := (nativeMenu).toRawTrace (initialLaw setup) horizon service countedTrace
  obtain ⟨draw, invariant⟩ :=
    (roster_trace_facts setup leaks horizon service previousTrace).1
  rw [applicationEq] at invariant
  obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor event ready strategic
  have previousClear : ExclusionEvidence 0 ∅
      (⟨previous.application, ∅⟩ : RecoveryState (graph setup)) := by
    rw [applicationEq]
    exact clear
  have actual := opportunity ⟨remaining + 1, none, previous⟩ countedTrace previousClear
  have fits := inclusionFitsDeadline_of_unrecalled_turn runtime leaks
    (initialLaw setup) horizon service (serviceGraph_revealRelaxedOrdered setup .sequential)
    ⟨remaining + 1, none, previous⟩ previousTrace rfl delay bound timely actual event who spec.2
    (by rw [applicationEq]; exact spec.1) entered (by rw [applicationEq]; exact activated)
    (fun entry remembered => never entry (recallEq ▸ remembered))
  change previous.application.publicView.InclusionFitsDeadline runtime bound event at fits
  rwa [applicationEq] at fits


/-- Every fresh call settles at every actual clear native counted history under
pointwise counted inclusion. Service is instantiated only at genuine counted prefixes. -/
theorem settlesFreshCalls_counted_clear_history
    (horizon : Nat) (scheduler : (N).Scheduler) (bound : (graph setup).EventId → Nat)
    (inclusion : ∀ control : (N).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      ProtectedInclusionAt runtime leaks control.execution bound)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner) :
    ∀ {state}
      (_trace : (onePacketProtocol setup runtime leaks bounds horizon
        scheduler).Trace state),
      (∀ current, state = some current → ExclusionEvidence 0 ∅
        (⟨current.execution.application, ∅⟩ : RecoveryState (graph setup))) →
      ReactiveApplication.serviceInvariant
        (SettlesFreshCalls setup leaks owner event bound) state
  | _, .start, _ => trivial
  | _, .extend (source := before) prior joint _ reached, clear => by
      have rawPrior := (nativeMenu).toRawTrace (initialLaw setup) horizon
        scheduler prior
      have beforeClear := native_clear_before_transition runtime leaks
        (initialLaw setup) (by
          intro native supported
          change native ∈ (setup.initialLaw.map
            (fun draw => State.initial (graph := graph setup) (setup.eventInputs draw))).support
              at supported
          obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
          exact ⟨setup.eventInputs draw, rfl⟩) horizon
        scheduler rawPrior joint reached clear
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
                  exact settlesFreshCalls_environment setup leaks owner event owned
                    remaining
                    execution atPrefix rawPrior valid command next supported

/-- One command from an actual clear counted prefix preserves settlement even
when this command creates the first public failure; no service is imposed after it. -/
theorem settlesFreshCalls_counted_clear_environment
    (horizon : Nat) (scheduler : (N).Scheduler) (bound : (graph setup).EventId → Nat)
    (inclusion : ∀ control : (N).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      ProtectedInclusionAt runtime leaks control.execution bound)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (remaining : Nat) (execution : (N).Execution)
    (prior : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).Trace
        (some ⟨remaining + 1, none, execution⟩))
    (clear : ExclusionEvidence 0 ∅ (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
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
  exact settlesFreshCalls_environment setup leaks owner event owned remaining execution
    atPrefix rawPrior valid command next reached

/-- Actual clear counted prefixes carry accepting receipts for every completed
protected fresh call, and once its original strict protected window has elapsed. -/
theorem prescribed_packet_counted_clear_settles
    (horizon : Nat) (scheduler : (N).Scheduler) (bound : (graph setup).EventId → Nat)
    (inclusion : ∀ control : (N).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      ProtectedInclusionAt runtime leaks control.execution bound)
    (control : (N).Control)
    (trace : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).Trace (some control))
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
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
