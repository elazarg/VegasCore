/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseAttemptRetryCompletion
import Vegas.Game.PhaseBindingFiberGeometry

/-! # Actual local assessment retries retain the focal event's delivery -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (runtimePlan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial runtimePlan (encodeInputs draw))
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- At a genuine clear request, every surviving retry in the SAME assessment's
actual local boundary law contains an accepted old-attempt completion of the
focal event. The result holds for every installed local response law, including
silence; readiness throughout the belief fiber is derived from information. -/
theorem phaseLocalAttemptBoundary_retry_completed
    (assessment : (N).BehavioralAssessment) (owner : Player)
    (site : (N).InformationSite owner) (law : PMF ((N).Choice owner site.1))
    (original : (app).Control) (originalTrace : (E).Trace (some original))
    (atSite : (N).infoOf owner originalTrace = site.1)
    (active : original.actor = some owner)
    (clear : original.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId)
    (request : original.execution.application.SeedRequest owner
      ⟨original.execution.application.attempt, event⟩)
    (final : (E).History)
    (supported : final ∈ (phaseLocalAttemptBoundary setup mode runtime leaks (menu) initial horizon
      scheduler assessment owner site law original.execution.application.attempt).support)
    (retry : PhaseSurvivingRetry setup mode runtime leaks owner
      original.execution.application.attempt final.state) :
    ∃ next : (app).Control, final.state = some next ∧
      ∃ record ∈ next.execution.application.retired,
        record.attempt = original.execution.application.attempt ∧
          event ∈ record.state.config.cut.completed ∧ record.state.ReceiptsComplete ∧
            ¬ record.state.PublicFailure event := by
  classical
  unfold phaseLocalAttemptBoundary at supported
  rw [PMF.mem_support_bind_iff] at supported
  obtain ⟨history, _prior, stopped⟩ := supported
  obtain ⟨before, shape, beforeActive, _beforeClear, beforeRequest⟩ :=
    phase_binding_fiber_genuine setup mode runtime leaks bounds runtimePlan horizon scheduler
      owner site original originalTrace atSite active event clear request history
  rcases history with ⟨⟨state, beforeTrace⟩, atInfo⟩
  change state = some before at shape
  subst state
  have infoEq : (N).infoOf owner beforeTrace = (N).infoOf owner originalTrace :=
    atInfo.trans atSite.symm
  change ((menu).signals initial horizon scheduler).infoOf owner beforeTrace =
    ((menu).signals initial horizon scheduler).infoOf owner originalTrace at infoEq
  rw [ReactiveApplication.ResponseMenu.info, ReactiveApplication.ResponseMenu.info] at infoEq
  simp only [ReactiveApplication.observe, beforeActive, active, ↓reduceIte] at infoEq
  have sameAttempt : before.execution.application.attempt =
      original.execution.application.attempt :=
    congrArg (fun input => input.2.application.2.attempt) (Option.some.inj infoEq)
  let updated := Profile.update (sig := (N).behavioralSignature) assessment.strategy owner
    ((assessment.strategy owner).withLaw site.1 law)
  have general := phase_attempt_boundary_retry_completed setup mode runtime leaks (menu)
    runtimePlan initial (by
      intro state member
      obtain ⟨draw, _possible, rfl⟩ := PMF.support_map .. ▸ member
      exact ⟨encodeInputs draw, rfl⟩) horizon scheduler
  have member : final ∈ ((N).runBehavioralUntil
      ((menu).bounded initial horizon scheduler).wellFoundedHistories updated
      (fun history => PhaseAttemptExit setup mode runtime leaks owner
        before.execution.application.attempt history.state)
          ⟨some before, beforeTrace⟩).support := by
    simpa only [sameAttempt] using stopped
  have retryBefore : PhaseSurvivingRetry setup mode runtime leaks owner
      before.execution.application.attempt final.state := by
    simpa only [sameAttempt] using retry
  simpa only [sameAttempt] using general updated before beforeTrace owner event beforeRequest final
    member retryBefore

end Vegas
