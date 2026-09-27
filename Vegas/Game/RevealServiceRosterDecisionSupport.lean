/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterClock
import Vegas.Game.RevealServiceRosterPosition
import Vegas.Game.RevealServiceRosterPrefixSupport

/-! # Legal roster decisions start from legal source prefixes

This bridge combines actual protocol histories, the scheduler plan and the
source checkpoint induction. It applies at every retained information site,
regardless of equilibrium probability or passive pending-message observations.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem roster_decision_boundary (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (responses : (application setup leaks).ResponseMenu)
    (who : Player) (control : (application setup leaks).Control)
    (trace : (responses.protocol (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Trace (some control))
    (active : control.actor = some who) :
    ∃ event : (graph setup).EventId, ∃ slot boundary prior,
      (rosters event)[slot]? = some who ∧
      control.execution.environmentRecall.length =
        (rosterPlanPrefix setup rosters event.val).length + 1 + slot + 1 ∧
      boundary ∈ ((initialLaw setup).bind fun state =>
        (runtime setup).runInteractionPlan leaks responses.uniformResponses network
          (rosterPlanPrefix setup rosters event.val)
          (ReactiveApplication.Execution.initial (application setup leaks) state)).support ∧
      prior ∈ ((runtime setup).runInteractionPlan leaks responses.uniformResponses network
        ([.grant event] ++ ((rosters event).take slot).map ServiceInstruction.player)
        boundary).support ∧
      control.execution ∈
        (prior.environmentStep (application setup leaks) (.activate who)).support := by
  obtain ⟨count, prior, _, position, _, selected, priorSupport, activated⟩ :=
    roster_decision_supported setup leaks rosters network responses who control trace active
  obtain ⟨event, slot, owner, located, planPrefix⟩ :=
    roster_activation_prefix setup rosters count who selected
  have phaseSupport : prior ∈
      (((initialLaw setup).bind fun state =>
        (runtime setup).runInteractionPlan leaks responses.uniformResponses network
          (rosterPlanPrefix setup rosters event.val)
          (ReactiveApplication.Execution.initial (application setup leaks) state)).bind
        (fun boundary => (runtime setup).runInteractionPlan leaks responses.uniformResponses
          network ([.grant event] ++ ((rosters event).take slot).map ServiceInstruction.player)
          boundary)).support :=
      by
    simpa only [planPrefix, runInteractionPlan_append, FinDist.bind_bind] using priorSupport
  obtain ⟨boundary, boundarySupport, phase⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ phaseSupport)
  exact ⟨event, slot, boundary, prior, owner, by omega, boundarySupport, phase, activated⟩

variable [Fintype Player]

/-- Every actual retained decision has an initialized legal source state at
its phase boundary. Both the boundary and current execution retain the native
private histories; none are quotiented to obtain this support statement. -/
theorem roster_decision_source (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((rosterMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who) :
    ∃ event : (graph setup).EventId, ∃ slot boundary prior,
      (rosters event)[slot]? = some who ∧
      control.execution.environmentRecall.length =
        (rosterPlanPrefix setup rosters event.val).length + 1 + slot + 1 ∧
      prior ∈ ((runtime setup).runInteractionPlan leaks
        (rosterMenu setup leaks bounds rosters).uniformResponses network
        ([.grant event] ++ ((rosters event).take slot).map ServiceInstruction.player)
        boundary).support ∧
      control.execution ∈
        (prior.environmentStep (application setup leaks) (.activate who)).support ∧
      ∃ initial ∈ setup.initialLaw.support, ∃ state,
        PublicPrefixCheckpoint setup leaks initial setup.program
          (EventLowering.ContextRefs.initial setup.context
            (EventLowering.outputLayout setup.program))
          (Revelations.initial setup.context) (EventLowering.outputRef setup.program)
          0 event.val state boundary ∧
        sourcePrefix? setup event.val boundary.application.config = some state ∧
        state ∈ ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program
          (fun owner => RevealOnly.uniformPolicy owner setup.program reveals)))^[event.val]
            (FinDist.pure (ProtocolState.entry setup.program
              (setup.initialConfig initial)))).support ∧
        boundary.network.Satisfies (fun message =>
          message.id ∈ boundary.network.ledger.map Message.id) := by
  let menu := rosterMenu setup leaks bounds rosters
  obtain ⟨event, slot, boundary, prior, owner, position, boundarySupport, phase, activated⟩ :=
    roster_decision_boundary setup leaks rosters network menu who control trace active
  obtain ⟨initial, initialSupport, state, checkpoint, decoded, _, sourceSupport, clean⟩ :=
    initialized_roster_prefix_support setup leaks bounds rosters network reveals openable
      menu.uniformResponses
      (fun owner past view response supported =>
        (menu.uniformResponses_support owner past view response).mp supported)
      event.val event.isLt.le boundary boundarySupport
  exact ⟨event, slot, boundary, prior, owner, position, phase, activated,
    initial, initialSupport, state, checkpoint, decoded, sourceSupport, clean⟩

end Vegas.SourceProgram.RevealService
