/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecisionRecallPosterior

/-! # Actual compiler marginals at protected unrecorded turns

At a clear legal prefix, the timing posterior is derived from all actual prior
owner turns. A protected unrecorded current turn therefore makes the original
compiler decision with geometric probability `1 - weight`, and waits otherwise.
The canonical rendering retains the actual own recall and current observation.
Earlier protected deferrals do not reweight the source compiler's choices.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- At its actual inclusion gate, an unrecorded opportunity is exactly the
canonical source response law, including its complete response syntax. -/
theorem sourceServiceCanonicalOpportunity_protected
    (bound : (graph setup).EventId → Nat) (profile : BehavioralProfile setup.program)
    (who : Player) (event : (graph setup).EventId)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (unrecorded : (runtime setup).eventRecorded leaks past event = false)
    (fits : view.application.publicView.InclusionFitsDeadline (runtime setup) bound event) :
    sourceServiceCanonicalOpportunity setup leaks bound profile who event past view =
      sourceServiceCanonicalPolicy setup leaks profile who past view := by
  let app := application setup leaks
  have kernel (response : app.Action) :
      (if response.transmission = none then app.silentPolicy past view else PMF.pure response) =
        PMF.pure response := by
    rcases response with ⟨transmission⟩
    cases transmission <;> rfl
  unfold sourceServiceCanonicalOpportunity
  simp only [unrecorded, Bool.false_eq_true, ↓reduceIte, fits]
  calc
    _ = (sourceServiceCanonicalPolicy setup leaks profile who past view).bind PMF.pure := by
      apply bind_congr_on_support _
      intro response _
      exact kernel response
    _ = _ := PMF.bind_pure _

variable [Fintype Player]

/-- The physical response marginal preserves the original typed compiler
kernel at every actual protected unrecorded turn, after any number of earlier
protected deferrals. The timing hazard is proved from actual recall. -/
theorem sourceServiceDecision_clear_protected_compiled_response {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (execution : (application setup leaks).Execution)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (clear : ∀ player, (runtime setup).persistentServiceRisk leaks bound player
      (execution.recall player) (execution.observe (application setup leaks) player) = false)
    (event : (graph setup).EventId)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall who) event = false)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound
      event)
    (weight : ℝ) (positive : 0 < weight) (below : weight < 1) :
    sourceServiceTurnPolicy setup leaks bound horizon
        (geometricTiming setup horizon weight positive.le below.le) profile who
        (execution.recall who) (execution.observe (application setup leaks) who) =
      mix weight positive.le below.le (PMF.pure ⟨none⟩)
        (((compileEventProfile setup.program profile) who event
          (PublicView.ownTurn?_spec _ who event turn).2
          (setup.eventGraph.fromModeObservation .sequential who
            ((graph setup).playerObserve who execution.application.config))).map
              ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
                (execution.observe (application setup leaks) who) event)) := by
  rw [sourceServiceDecision_clear_geometric_response bounds bound profile who execution trace
    clear event unrecorded turn weight positive below,
    sourceServiceCanonicalOpportunity_protected bound profile who event (execution.recall who)
      (execution.observe (application setup leaks) who) unrecorded fits,
    sourceServiceCanonicalPolicy_at_event setup leaks profile who execution event turn
      (PublicView.ownTurn?_spec _ who event turn).2]

end Vegas
