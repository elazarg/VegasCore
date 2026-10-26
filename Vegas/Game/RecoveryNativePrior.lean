/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryNativeStrategy

/-! # Exact prior transport of canonical native projection

Canonical source projection is the existing bounded native projection followed
by the equality of its projected initial law with the original source prior.
-/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication runtime leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler runtime leaks scheduler
local notation "R" => model setup runtime leaks bounds Initial horizon scheduler

/-- Canonical projection is precisely the bounded native profile with its
choice carrier transported along the equality of initial priors. -/
theorem sourceNativeProfile_eq_cast (strategy : ∀ who, (R).BehavioralPolicy who)
    (who : Player) (input : (application setup runtime leaks).Info) :
    sourceNativeProfile setup runtime leaks bounds horizon scheduler strategy who input =
      (boundedNativeProfile runtime leaks bounds Initial horizon scheduler strategy
        who input).map (Equiv.cast (congrArg
          (fun law : PMF (EventGraphRuntime.State (graph setup)) =>
            ((bounds.onePacketMenu runtime leaks).information law horizon
              (NativeScheduler)).Choice who input) (initialLaw_native setup))) := by
  unfold sourceNativeProfile boundedNativeProfile sourceNativeChoiceEquiv
  exact (PMF.map_comp (p := strategy who (liftInformation runtime leaks input))
    (f := boundedChoiceEquiv runtime leaks bounds Initial horizon scheduler who input)
    (Equiv.cast (congrArg
      (fun law : PMF (EventGraphRuntime.State (graph setup)) =>
        ((bounds.onePacketMenu runtime leaks).information law horizon
          (NativeScheduler)).Choice who input) (initialLaw_native setup)))).symm

end Vegas.RecoveryOnePacket
