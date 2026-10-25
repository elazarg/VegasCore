/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveDecisionPredecessor
import Vegas.Game.SequentialPhaseNativeService
import Vegas.Game.OnePacketFirstActivation
import Vegas.Pending.ReactiveFirstOpportunity

/-! # Physical phase opportunity bounds the first actual counted source response

The idle predecessor is itself a legal counted source prefix. Pointwise native
opportunity therefore applies under the physical phase contract, without an
unrestricted raw-native or recovery opportunity assumption.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol Interaction EventGraphRuntime
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup))

local notation "inputs" => PMF.map setup.eventInputs setup.initialLaw
local notation "plan" => sequentialRuntimePhasePlan setup.program
local notation "recoveryLeaks" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "P" => phaseApplication (runtime setup) leaks
local notation "N" => application setup recoveryLeaks
local notation "phaseInitial" => PMF.map (PhaseRuntimeState.initial plan) (inputs)
local notation "nativeMenu" => MessageBounds.onePacketMenu (runtime setup) recoveryLeaks bounds
local notation "recoveryScheduler" => SequentialPhaseSchedulerInformation.scheduler setup.program
  (runtime setup) leaks recoveryLeaks
local notation "nativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup) recoveryLeaks

/-- Every first actual native counted callback fits the original inclusion deadline
under physical phase opportunity, including arbitrary prior source counterfactuals. -/
theorem phase_firstActivation_inclusionFits
    (horizon : Nat) (scheduler : (P).Scheduler) (delay bound : (graph setup).EventId → Nat)
    (opportunity : PhaseService.Opportunity (runtime setup) leaks phaseInitial horizon scheduler
      delay)
    (timely : (runtime setup).AsyncTimely delay bound)
    {state : (N).ProtocolState}
    (trace : (onePacketProtocol setup recoveryLeaks bounds horizon
      (nativeScheduler (recoveryScheduler scheduler))).Trace state)
    {remaining : Nat} {who : Player} {execution : (N).Execution}
    (current : state = some ⟨remaining, some who, execution⟩)
    (clear : ExclusionEvidence 0 ∅ (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who,
      ¬ ActivatedAt setup recoveryLeaks who event entry) :
    execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event := by
  let service := nativeScheduler (recoveryScheduler scheduler)
  obtain ⟨previous, ⟨countedTrace⟩, applicationEq, recallEq⟩ :=
    (nativeMenu).decision_predecessor (initialLaw setup) horizon service trace current
  have spec := PublicView.ownTurn?_spec _ who event turn
  have ready := (execution.application.publicView_eventReady event).mp spec.1
  have strategic : ((graph setup).actor? event).isSome = true := by rw [spec.2]; rfl
  have previousTrace := (nativeMenu).toRawTrace (initialLaw setup) horizon service countedTrace
  obtain ⟨draw, invariant⟩ :=
    (roster_trace_facts setup recoveryLeaks horizon service previousTrace).1
  rw [applicationEq] at invariant
  obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor event ready strategic
  have previousClear : ExclusionEvidence 0 ∅
      (⟨previous.application, ∅⟩ : RecoveryState (graph setup)) := by
    rw [applicationEq]
    exact clear
  have actual := PhaseService.Opportunity.clear_native_counted setup leaks bounds horizon scheduler
    delay opportunity countedTrace previousClear
  have fits := inclusionFitsDeadline_of_unrecalled_turn (runtime setup) recoveryLeaks
    (initialLaw setup) horizon service (serviceGraph_revealRelaxedOrdered setup .sequential)
    ⟨remaining + 1, none, previous⟩ previousTrace rfl delay bound timely actual event who spec.2
    (by rw [applicationEq]; exact spec.1) entered (by rw [applicationEq]; exact activated)
    (fun entry remembered => never entry (recallEq ▸ remembered))
  change previous.application.publicView.InclusionFitsDeadline (runtime setup) bound event at fits
  rwa [applicationEq] at fits

end Vegas
