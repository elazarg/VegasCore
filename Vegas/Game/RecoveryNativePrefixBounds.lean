/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryNativeComparison
import Vegas.Game.OnePacketBaseAssembly
import Vegas.Game.OnePacketBindingRepairAssembly

/-! # Prefix estimates for the native comparison sequence

The same recovery completion weights give a native comparison sequence with
vanishing unforced posterior mass and operational-record decorrelation. These
are prefix estimates; no native service or continuation contract is used.
-/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication runtime leaks).Scheduler)

variable {Public : Type*} {signal : State L setup.context → Public}

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler runtime leaks scheduler
local notation "R" => model setup runtime leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) Initial horizon scheduler

def nativeBaseInputs
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [Finite setup.intendedProtocol.History]
    [∀ who, DecidableEq ((N).InfoState who)] (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (slots_pos : 0 < bounds.candidateCount) :
    OnePacketBaseInputs setup runtime leaks bounds horizon (NativeScheduler) sequence
      bounds.candidateCount := by
  refine OnePacketBaseInputs.ofCounterparts (runtime := runtime) wellFormed sequence sourceMixed
    (2 * horizon + 2)
    0 (le_refl 0) covers coversInputs capacity slots_pos ?_
  intro weights targetSequence assembled mixed _bayes who site notFree notOwing
    past view atSite event turn
  exact OnePacketCounterpartInputs.ofBindingRepairs (runtime := runtime) wellFormed independent
    observable sourceMixed
    (fun n => trembleScale_pos
      (combinedFloor_pos setup runtime leaks bounds horizon (NativeScheduler) (sequence n)))
    (fun n => trembleScale_le_one
      (combinedFloor_pos setup runtime leaks bounds horizon (NativeScheduler) (sequence n)).le
      (combinedFloor_le_one setup runtime leaks bounds horizon (NativeScheduler) (sequence n)))
    (fun _ => rfl) covers coversInputs capacity weights assembled mixed
    notFree notOwing atSite turn

end Vegas.RecoveryOnePacket
