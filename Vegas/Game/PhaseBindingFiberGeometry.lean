/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseMarkedBindingFiber
import Vegas.Pending.PhaseNativeInvariant

/-! # Actual ready-binding geometry throughout complete information fibers -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- A genuine clear owned request is shared by every history at its complete
physical information. Both actual state invariants are derived from the real
initialized traces; no all-fiber readiness premise is assumed. -/
theorem phase_binding_fiber_genuine (focal : Player) (site : (N).InformationSite focal)
    (original : (phaseApplication runtime leaks).Control)
    (originalTrace : (E).Trace (some original))
    (atSite : (N).infoOf focal originalTrace = site.1)
    (active : original.actor = some focal)
    (event : (serviceGraph setup mode).EventId)
    (clear : original.execution.application.current.excluded = ∅)
    (request : original.execution.application.SeedRequest focal
      ⟨original.execution.application.attempt, event⟩) :
    ∀ history : (N).InformationHistory focal site.1,
      ∃ control : (phaseApplication runtime leaks).Control,
        history.1.state = some control ∧ control.actor = some focal ∧
          control.execution.application.current.excluded = ∅ ∧
          control.execution.application.SeedRequest focal
            ⟨control.execution.application.attempt, event⟩ := by
  have valid (control : (phaseApplication runtime leaks).Control)
      (trace : (E).Trace (some control)) :
      ∃ draw, control.execution.application.Invariant draw := by
    let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
    have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon
      scheduler trace
    have initialEq : inputs.map (PhaseRuntimeState.initial plan) = initial :=
      PMF.map_comp _ _ _
    rw [← initialEq] at rawTrace
    exact phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler rawTrace
  obtain ⟨originalDraw, originalValid⟩ := valid original originalTrace
  rintro ⟨⟨state, trace⟩, same⟩
  have infoEq : (N).infoOf focal trace = (N).infoOf focal originalTrace := same.trans atSite.symm
  change ((PhaseCount.onePacketMenu runtime leaks bounds).signals initial horizon scheduler).infoOf
    focal trace =
    ((PhaseCount.onePacketMenu runtime leaks bounds).signals initial horizon scheduler).infoOf
      focal originalTrace at infoEq
  rw [ReactiveApplication.ResponseMenu.info, ReactiveApplication.ResponseMenu.info] at infoEq
  cases state with
  | none => simp [ReactiveApplication.observe, active] at infoEq
  | some control =>
      by_cases acting : control.actor = some focal
      · simp only [ReactiveApplication.observe, acting, active, ↓reduceIte] at infoEq
        have publicEq : control.execution.application.publicView =
            original.execution.application.publicView :=
          congrArg (fun input => input.2.application.2) (Option.some.inj infoEq)
        have targetClear : control.execution.application.current.excluded = ∅ := by
          exact (congrArg PhasePublicView.excluded publicEq).trans clear
        obtain ⟨draw, controlValid⟩ := valid control trace
        have publicRequest := (PhaseRuntimeState.requests_publicView original.execution.application
          originalValid focal ⟨original.execution.application.attempt, event⟩).mpr request
        rw [← publicEq] at publicRequest
        have targetRequest := (PhaseRuntimeState.requests_publicView control.execution.application
          controlValid focal ⟨original.execution.application.attempt, event⟩).mp publicRequest
        have attemptEq : control.execution.application.attempt =
            original.execution.application.attempt := congrArg PhasePublicView.attempt publicEq
        refine ⟨control, rfl, acting, targetClear, ?_⟩
        simpa only [attemptEq] using targetRequest
      · simp [ReactiveApplication.observe, acting, active] at infoEq

end Vegas
