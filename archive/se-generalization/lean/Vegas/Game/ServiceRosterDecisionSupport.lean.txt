/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRosterClock
import Vegas.Game.ServiceRosterPosition

/-! # Actual service roster decision boundaries
-/

noncomputable section

namespace Vegas

open SourceProgram

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
        (rosterPlanPrefix setup rosters event.val).length + slot + 1 ∧
      boundary ∈ ((initialLaw setup).bind fun state =>
        (runtime setup).runInteractionPlan leaks responses.uniformResponses network
          (rosterPlanPrefix setup rosters event.val)
          (ReactiveApplication.Execution.initial (application setup leaks) state)).support ∧
      prior ∈ ((runtime setup).runInteractionPlan leaks responses.uniformResponses network
        (((rosters event).take slot).map ServiceInstruction.player)
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
          network (((rosters event).take slot).map ServiceInstruction.player)
          boundary)).support :=
      by
    simpa only [planPrefix, runInteractionPlan_append, PMF.bind_bind] using priorSupport
  obtain ⟨boundary, boundarySupport, phase⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ phaseSupport)
  exact ⟨event, slot, boundary, prior, owner, by omega, boundarySupport, phase, activated⟩

end Vegas
