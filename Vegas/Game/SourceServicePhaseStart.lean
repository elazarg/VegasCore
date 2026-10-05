/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecisionSupport

/-! # Actual retained histories at a phase start

A retained history whose service position is the end of a complete prefix of
event blocks supplies the full typed boundary, including readiness and the
absence of submissions for future events. Empty response rosters require no
special case or additional service assumption.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

variable [Fintype Player]

/-- Every actual retained history at the start of an event block is itself a
complete typed source boundary. All operational resources are inherited from
the source-prefix proof. -/
theorem sourceService_phase_boundary
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (idle : control.actor = none)
    (event : (graph setup).EventId)
    (planPrefix : (rosterPlan setup rosters).take control.execution.environmentRecall.length =
      rosterPlanPrefix setup rosters event.val) :
    ∃ initial ∈ setup.initialLaw.support, ∃ (Γ : SourceCtx Player L)
      (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ),
      ServiceBoundary setup leaks rosters initial source refs event.val control.execution := by
  let menu := sourceServiceMenu setup leaks bounds rosters
  have supported := menu.roundSupported_uniform (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) trace
  have account := supported.1
  have reached := supported.2
  rw [idle] at reached
  change control.execution ∈ ((application setup leaks).roundsFrom (initialLaw setup)
    (rosterScheduler setup leaks rosters network) menu.uniformResponses
      control.execution.environmentRecall.length).support at reached
  have within : control.execution.environmentRecall.length ≤ (rosterPlan setup rosters).length :=
    by omega
  rw [roster_roundsFrom setup leaks rosters network menu.uniformResponses _ within, planPrefix]
    at reached
  obtain ⟨initial, initialSupport, _, _, _, Γ, names, remaining, remainingProfile, source,
      refs, embedding, refsBefore, _, _, _, _, _, _, _, _, checkpoint⟩ :=
    initialized_sourceService_prefix_support setup leaks bounds values capacity rosters
      opportunities menu.uniformResponses
      (fun who past view response member =>
        (menu.uniformResponses_support who past view response).mp member)
      network (failureProfile setup.program) event.val event.isLt.le control.execution reached
  exact ⟨initial, initialSupport, Γ, source, refs, checkpoint⟩

end Vegas
