/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCountedService
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
  (runtime : EventGraphRuntime (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup))

local notation "inputs" => PMF.map setup.eventInputs setup.initialLaw
local notation "plan" => sequentialRuntimePhasePlan setup.program
local notation "recoveryLeaks" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "P" => phaseApplication runtime leaks
local notation "N" => application (runtime := runtime) setup recoveryLeaks
local notation "phaseInitial" => PMF.map (PhaseRuntimeState.initial plan) (inputs)
local notation "nativeMenu" => MessageBounds.onePacketMenu runtime recoveryLeaks bounds
local notation "recoveryScheduler" => SequentialPhaseSchedulerInformation.scheduler setup.program
  runtime leaks recoveryLeaks
local notation "nativeScheduler" => RecoveryProjection.nativeScheduler runtime recoveryLeaks

/-- Every first actual native counted callback fits the original inclusion deadline
under physical phase opportunity, including arbitrary prior source counterfactuals. -/
theorem phase_firstActivation_inclusionFits
    (horizon : Nat) (scheduler : (P).Scheduler) (delay bound : (graph setup).EventId → Nat)
    (opportunity : PhaseService.Opportunity runtime leaks phaseInitial horizon scheduler
      delay)
    (timely : runtime.AsyncTimely delay bound)
    {state : (N).ProtocolState}
    (trace : (onePacketProtocol (runtime := runtime) setup recoveryLeaks bounds horizon
      (nativeScheduler (recoveryScheduler scheduler))).Trace state)
    {remaining : Nat} {who : Player} {execution : (N).Execution}
    (current : state = some ⟨remaining, some who, execution⟩)
    (clear : ExclusionEvidence 0 ∅ (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who,
      ¬ ActivatedAt (runtime := runtime) setup recoveryLeaks who event entry) :
    execution.application.publicView.InclusionFitsDeadline runtime bound event := by
  exact firstActivation_inclusionFits_of_counted_opportunity (runtime := runtime) setup
    recoveryLeaks bounds horizon
    (nativeScheduler (recoveryScheduler scheduler)) delay bound
    (fun control prior clear => PhaseService.Opportunity.clear_native_counted setup runtime leaks
      bounds
      horizon scheduler delay opportunity prior clear) timely trace current clear event turn never

end Vegas
