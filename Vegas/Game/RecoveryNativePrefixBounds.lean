/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryNativeComparison
import Vegas.Game.OnePacketBaseAssembly
import Vegas.Game.OnePacketBindingRepairAssembly
import Vegas.Game.OnePacketCertificateAssembly
import Vegas.Game.OnePacketPrescribedSites
import Vegas.Game.OnePacketSilentShape

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
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler

def nativeBaseInputs
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [Finite setup.intendedProtocol.History]
    [∀ who, DecidableEq ((N).InfoState who)] (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependent)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (slots_pos : 0 < bounds.candidateCount) :
    OnePacketBaseInputs setup leaks bounds horizon (NativeScheduler) sequence
      bounds.candidateCount := by
  refine OnePacketBaseInputs.ofCounterparts wellFormed sequence sourceMixed (2 * horizon + 2)
    0 (le_refl 0) covers coversInputs capacity slots_pos ?_
  intro weights targetSequence assembled mixed _bayes who site notFree notOwing
    past view atSite event turn
  exact OnePacketCounterpartInputs.ofBindingRepairs wellFormed independent sourceMixed
    (fun n => trembleScale_pos
      (combinedFloor_pos setup leaks bounds horizon (NativeScheduler) (sequence n)))
    (fun n => trembleScale_le_one
      (combinedFloor_pos setup leaks bounds horizon (NativeScheduler) (sequence n)).le
      (combinedFloor_le_one setup leaks bounds horizon (NativeScheduler) (sequence n)))
    (fun _ => rfl) covers coversInputs capacity weights assembled mixed
    notFree notOwing atSite turn

end Vegas.RecoveryOnePacket
