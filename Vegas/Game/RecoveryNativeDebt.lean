/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryDebtUniformity
import Vegas.Game.RecoveryNativeWeights

/-! # Own-debt classification at paired clear decision inputs

Own source debt depends on the projected complete observation. A native debt
witness therefore yields debt at an actual recovery decision with that input.
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
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) Initial horizon scheduler
local notation "RMenu" => Recovery.onePacketMenu runtime leaks bounds
local notation "NMenu" => bounds.onePacketMenu runtime leaks

/-- Native own debt cannot disappear at an actual recovery decision with the
same lifted complete input. -/
theorem owingAgent_of_nativeOwing_at_liftedSite [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    {who : Player} (site : (N).InformationSite who)
    (decision : (R).IsDecisionInfo who (liftInformation runtime leaks site.1))
    (owing : Vegas.OwingAgent setup runtime leaks bounds horizon (NativeScheduler) ((N).agentAt
      site)) :
    OwingAgent setup runtime leaks bounds Initial horizon scheduler
      ((R).agentAt ⟨liftInformation runtime leaks site.1, decision⟩) := by
  obtain ⟨native, point, nativeDecoded, owes⟩ := owing
  let recoverySite : (R).InformationSite who :=
    ⟨liftInformation runtime leaks site.1, decision⟩
  obtain ⟨recovery, _running, _choice, _permitted⟩ := recoverySite.2
  have nativeActive := InformationSite.active (N) site native
  have recoveryActive := InformationSite.active (R) recoverySite recovery
  obtain ⟨nativeControl, nativeCurrent, nativeActor⟩ := (application setup runtime
    leaks).control_of_active
    (initialLaw setup) horizon (NativeScheduler)
    ((NMenu).toRawHistory (initialLaw setup) horizon (NativeScheduler) native.1) who nativeActive
  obtain ⟨recoveryControl, recoveryCurrent, recoveryActor⟩ :=
    (recoveryApplication runtime leaks).control_of_active Initial horizon scheduler
      ((RMenu).toRawHistory Initial horizon scheduler recovery.1) who recoveryActive
  change native.1.state = some nativeControl at nativeCurrent
  change recovery.1.state = some recoveryControl at recoveryCurrent
  obtain ⟨recoveryPoint, recoveryDecoded⟩ := nativeDecodedState_isSome setup runtime leaks bounds
    horizon
    scheduler recovery.1 recoveryCurrent
  refine ⟨recovery, recoveryPoint, recoveryDecoded, ?_⟩
  have nativeObserved := ((NMenu).info (initialLaw setup) horizon (NativeScheduler) who
    native.1.trace).symm.trans native.2
  have recoveryObserved := ((RMenu).info Initial horizon scheduler who
    recovery.1.trace).symm.trans recovery.2
  rw [nativeCurrent] at nativeObserved
  rw [recoveryCurrent] at recoveryObserved
  have projectedObserved := observe_projection runtime leaks who (some recoveryControl)
  change (application setup runtime leaks).observe who
      (some (RecoveryProjection.control runtime leaks recoveryControl)) =
    RecoveryProjection.information runtime leaks
      ((recoveryApplication runtime leaks).observe who (some recoveryControl))
    at projectedObserved
  rw [recoveryObserved, information_liftInformation] at projectedObserved
  have projectedActor : (RecoveryProjection.control runtime leaks recoveryControl).actor =
      some who := recoveryActor
  have samePairs :
      some (nativeControl.execution.recall who,
        nativeControl.execution.observe (application setup runtime leaks) who) =
      some ((RecoveryProjection.execution runtime leaks recoveryControl.execution).recall
          who,
        (RecoveryProjection.execution runtime leaks recoveryControl.execution).observe
          (application setup runtime leaks) who) := by
    have sameObserved := nativeObserved.trans projectedObserved.symm
    change (application setup runtime leaks).observe who (some nativeControl) =
      (application setup runtime leaks).observe who
        (some (RecoveryProjection.control runtime leaks recoveryControl)) at sameObserved
    simp only [ReactiveApplication.observe, nativeActor, projectedActor, ↓reduceIte] at sameObserved
    exact sameObserved
  rw [nativeCurrent] at nativeDecoded
  rw [recoveryCurrent] at recoveryDecoded
  exact (Vegas.owesFailure_iff_of_projectView_eq (runtime := runtime) (setup := setup) (leaks :=
    leaks)
    (first := nativeControl.execution)
    (second := RecoveryProjection.execution runtime leaks recoveryControl.execution)
    (firstPast := nativeControl.execution.recall who)
    (secondPast :=
      (RecoveryProjection.execution runtime leaks recoveryControl.execution).recall who)
    who nativeDecoded recoveryDecoded (congrArg (projectView setup runtime leaks who)
      samePairs)).mp owes

end Vegas.RecoveryOnePacket
