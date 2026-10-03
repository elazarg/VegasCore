/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCanonicalPolicy
import Vegas.Game.SourceServiceAlignedConstructors
import Vegas.Game.SourceServiceDisclosure
import Vegas.Pending.ReactiveCompiledResolution

/-! # Explicit disclosure decisions at protected opportunities

An unrecorded protected resolution sends either an evidence-free withholding
or a typed opening. Its selected source policy therefore has zero probability
of silence, for either source disclosure choice. A closed deadline gate returns
silence; the generic opportunity risk test distinguishes that input.

These are operational response laws, without a source belief or equilibrium
transport assertion.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem canonicalOpportunity_eq_policy
    (bound : (graph setup).EventId → Nat) (profile : BehavioralProfile setup.program)
    (who : Player) (event : (graph setup).EventId)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (unrecorded : (runtime setup).eventRecorded leaks past event = false)
    (fits : view.application.publicView.InclusionFitsDeadline (runtime setup) bound event) :
    sourceServiceCanonicalOpportunity setup leaks bound profile who event past view =
      sourceServiceCanonicalPolicy setup leaks profile who past view := by
  unfold sourceServiceCanonicalOpportunity
  simp only [unrecorded, Bool.false_eq_true, ↓reduceIte, fits]
  have kernel : (fun response : (application setup leaks).Action =>
      if response.transmission = none then
        (application setup leaks).silentPolicy past view else PMF.pure response) =
        PMF.pure := by
    funext response
    rcases response with ⟨transmission⟩
    cases transmission <;> rfl
  rw [kernel, PMF.bind_pure]

/-- Both source disclosure choices emit an actual decision at a protected
unsent resolution. No source choice can be mistaken for deferral. -/
theorem RevealSource.canonicalOpportunity_silent_mass_zero
    {profile : BehavioralProfile setup.program} {event : (graph setup).EventId}
    (bound : (graph setup).EventId → Nat)
    (execution : (application setup leaks).Execution)
    (site : RevealSource setup profile event execution.application.config)
    (ready : execution.application.config.cut.Ready event)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall site.owner) event = false)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event) :
    ((sourceServiceCanonicalOpportunity setup leaks bound profile site.owner event
      (execution.recall site.owner) (execution.observe (application setup leaks) site.owner))
        ⟨none⟩).toReal = 0 := by
  classical
  have outputEq := site.outputEq
  obtain ⟨Γ, names, published, owner, name, payload, fresh, binding, unresolved, next,
    residual, refs, source, embedding, refsBefore, aligned, agree, history, head, _, _⟩ := site
  dsimp only at *
  subst head
  let event := embedding.event ⟨0, by simp [eventCount]⟩
  rw [canonicalOpportunity_eq_policy bound profile owner event _ _ unrecorded fits]
  have policyLaw := sourceServiceCanonicalPolicy_reveal setup leaks fresh binding unresolved next
    profile residual refs source embedding refsBefore event.val aligned execution agree history
      ready
  let decision (disclose : Bool) := (runtime setup).canonicalServiceDecision leaks owner
    (execution.recall owner) (execution.observe (application setup leaks) owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
  have law : sourceServiceCanonicalPolicy setup leaks profile owner
      (execution.recall owner) (execution.observe (application setup leaks) owner) =
        (revealKernel residual (source.view owner)).map decision := policyLaw
  rw [law, ← PMF.bind_pure_comp, toReal_bind_apply]
  change expect (revealKernel residual (source.view owner))
    (fun disclose => ((PMF.pure (decision disclose)) ⟨none⟩).toReal) = _
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations binding) :=
    by
      change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
        ((toEventGraph setup.program).nodes (embedding.event ⟨0, by simp [eventCount]⟩)) = _
      simpa [compileRankedNodes] using aligned.graphSuffix.nodeEq
        ⟨0, by simp [eventCount]⟩
  have node : nodeView (graph setup) event =
      .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations binding)
        outputEq codeEq :=
    EventGraphRuntime.nodeView_eq_resolve _ _
  have nonSilent (disclose : Bool) : decision disclose ≠ ⟨none⟩ := by
    unfold decision
    rw [(runtime setup).canonicalServiceDecision_eq_of_not_bind leaks owner
      (execution.recall owner) (execution.observe (application setup leaks) owner) event _
      (fun _ _ _ _ bind => by rw [node] at bind; cases bind)]
    rcases (runtime setup).serviceDecision_resolution_cases leaks owner (execution.recall owner)
        (execution.observe (application setup leaks) owner) event owner payload (refs.get binding)
        _ outputEq codeEq node disclose with withheld | ⟨candidate, value, evidence, _, _, _, sent⟩
    · rw [withheld]
      intro equal
      cases congrArg ReactiveApplication.Action.transmission equal
    · rw [sent]
      intro equal
      cases congrArg ReactiveApplication.Action.transmission equal
  calc
    _ = expect (revealKernel residual (source.view owner)) (fun _ => (0 : ℝ)) := by
      apply expect_congr_on_support
      intro disclose _
      rw [PMF.pure_apply_of_ne _ _ (Ne.symm (nonSilent disclose)), ENNReal.toReal_zero]
    _ = 0 := expect_zero _

/-- A closed inclusion gate defers the selected decision. An unrecorded
ready owned event at this input is an unprotected opportunity. -/
theorem sourceServiceCanonicalOpportunity_closed_likelihood
    (bound : (graph setup).EventId → Nat) (profile : BehavioralProfile setup.program)
    (who : Player) (event : (graph setup).EventId)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (closed : ¬ view.application.publicView.InclusionFitsDeadline (runtime setup) bound event) :
    ((sourceServiceCanonicalOpportunity setup leaks bound profile who event past view)
      ⟨none⟩).toReal = 1 := by
  by_cases recorded : (runtime setup).eventRecorded leaks past event = true
  · simp only [sourceServiceCanonicalOpportunity, recorded, ↓reduceIte,
      ReactiveApplication.silentPolicy, PMF.pure_apply, ENNReal.toReal_one]
  · simp only [sourceServiceCanonicalOpportunity, recorded, closed, Bool.false_eq_true,
      ↓reduceIte, ReactiveApplication.silentPolicy, PMF.pure_apply, ENNReal.toReal_one]

end Vegas
