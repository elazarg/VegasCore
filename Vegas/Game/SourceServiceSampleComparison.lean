/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceHarmlessContinuation
import Vegas.Game.SourceServiceContinuationBridge

/-! # Zero gain at public sampling opportunities

At a public-sampling phase every retained response is transport-only, so every
legal response leaves the same application law at the next event boundary.
The generic local comparison then gives equal prescribed and alternative
continuation laws for every local lottery and every belief over the site.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace TimedApproximant

variable {service : SourceServiceSpec Player L} (approx : TimedApproximant service)

include approx in
/-- Every legal response at a public-sampling decision is transport-only. -/
theorem sample_response_transport {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    {event : (graph service.setup).EventId} (chance : (graph service.setup).actor? event = none)
    (sole : execution.application.publicView.SoleReady event)
    (response : (application service.setup service.leaks).Action)
    (allowed : response ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who)) :
    response = ⟨none⟩ := by
  have present := service.menu.fullyMixed_response_support (initialLaw service.setup)
    service.planLength service.scheduler approx.players approx.covered approx.assessment
    approx.strategy approx.mixed who remaining execution trace response allowed
  simp only [players, sourceServiceTimedPolicy_idle _ _ _ _ _ who _
    (execution.observe (application service.setup service.leaks) who)
    (sole.idle (by rw [chance]; exact (Option.some_ne_none who).symm))] at present
  exact (application service.setup service.leaks).silentPolicy_cases _ _ response present

open Classical in
/-- At a public-sampling site, every local lottery has the prescribed
continuation law, for every belief over the site. -/
theorem sample_comparison_eq (who : Player) (site : service.model.InformationSite who)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (observed : site.1 = some (past, view))
    {event : (graph service.setup).EventId} (chance : (graph service.setup).actor? event = none)
    (readyView : view.application.publicView.EventReady event)
    (law : PMF (service.model.Choice who site.1)) :
    let comparison := service.model.assessmentComparisonWith (service.model.truncatedRunner
        service.fuel) service.readout
      approx.assessment who (site, (approx.assessment.strategy who).withLaw site.1 law)
    comparison.alternative = comparison.prescribed := by
  apply approx.comparison_eq_of_phase_invariant who site
  intro history remaining execution current info phase first second firstAllowed secondAllowed
  have input := (service.infoOf_decision history current).symm.trans (info.trans observed)
  have readyNow :=
    (congrArg (fun pair : List (application service.setup service.leaks).PlayerEntry ×
      (application service.setup service.leaks).PlayerView =>
        pair.2.application.publicView.EventReady event) (Option.some.inj input)).mpr readyView
  have same : phase.event = event := (phase.sole.2 event readyNow).symm
  subst same
  have trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  have ending : rosterPhaseEnding service.setup phase.event =
      .sample phase.event :: List.replicate (phase.event.val + 1) .tick ++
        [.expire phase.event] := by
    simp only [rosterPhaseEnding, chance, List.cons_append, List.nil_append]
  have law (response : (application service.setup service.leaks).Action)
      (allowed : response ∈ service.menu.actions who (execution.recall who)
        (execution.observe (application service.setup service.leaks) who)) :=
    sourceService_sample_response_application_law service.setup service.leaks service.rosters
      approx.timing approx.profile service.network phase.event chance who execution phase.sole
      response
      (approx.sample_response_transport trace chance phase.sole response allowed) phase.visits
      (phase.event.val + 1)
  have applications := (law first firstAllowed).trans (law second secondAllowed).symm
  simp only [phaseConfigLaw, phaseLaw, DecisionPhase.tail, ending]
  simpa only [PMF.map_comp, Function.comp_def] using
    congrArg (PMF.map EventGraphRuntime.State.config) applications

end TimedApproximant

end Vegas
