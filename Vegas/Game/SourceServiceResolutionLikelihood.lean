/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCanonicalPolicy
import Vegas.Game.SourceServiceBindingSource
import Vegas.Game.SourceServiceDisclosure
import Vegas.Pending.ReactiveDisclosure

/-! # The source likelihood of an actual silent resolution response

At a protected unrecorded resolution, an effective source disclosure is silent
exactly when it selects false. Supported true choices have an authentic opening,
derived from the guarded source result and the actual binding invariant.
Outside the protected inclusion window, the canonical opportunity is silent
regardless of the source choice. Binding-only risk recall does not exclude that
case for resolutions.

These are local operational likelihood laws. They do not assert source-view
stability across earlier turns or a source posterior at a native information site.
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

private theorem canonical_resolution_false
    (who : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding who payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks)
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (execution : (application setup leaks).Execution) :
    (runtime setup).canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) false) = ⟨none⟩ := by
  simp only [canonicalServiceDecision, canonicalReactiveDecision, node,
    reactiveResolutionPacket, cast_cast, cast_eq, Bool.false_eq_true, ↓reduceIte,
    disclosureSubmission_normalize_withhold]
  rfl

private theorem canonical_resolution_true_not_silent
    (who : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding who payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks)
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (execution : (application setup leaks).Execution)
    (valid : execution.application.BindingInvariant) (value : L.Val payload)
    (resolved : EventGraph.EventCode.resolveOutput? binding checks true
      execution.application.config.store = some (.success value)) :
    (runtime setup).canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) ≠ ⟨none⟩ := by
  obtain ⟨candidate, _, _, _, packet⟩ := reactiveResolutionPacket_provenance
    (runtime setup) leaks execution.application valid who event payload binding checks outputEq
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
      (by simp only [cast_cast, cast_eq]) value resolved
  change reactiveResolutionPacket who event payload binding checks outputEq
    (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
    (execution.observe (application setup leaks) who).application = _ at packet
  have normal := reactiveResolutionSubmission_normal (runtime setup) leaks execution.application
    valid who event payload binding checks outputEq
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
  change (disclosureSubmission (reactiveResolutionPacket who event payload binding checks outputEq
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
      (execution.observe (application setup leaks) who).application)).normalizeReactive who
        (execution.observe (application setup leaks) who).application [] =
      disclosureSubmission (reactiveResolutionPacket who event payload binding checks outputEq
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
        (execution.observe (application setup leaks) who).application) at normal
  simp only [canonicalServiceDecision, canonicalReactiveDecision, node]
  rw [normal, packet]
  simp only [disclosureSubmission, ReactiveApplication.SubmissionNormalization.action]
  intro equal
  cases congrArg ReactiveApplication.Action.transmission equal

/-- At an actual protected unsent resolution with an aligned effective source
profile, the silent-response likelihood is exactly its source false mass.
No source observation or likelihood equality is assumed as a separate premise. -/
theorem RevealSource.canonicalOpportunity_silent_likelihood
    {profile : BehavioralProfile setup.program} {event : (graph setup).EventId}
    (bound : (graph setup).EventId → Nat)
    (execution : (application setup leaks).Execution)
    (site : RevealSource setup profile event execution.application.config)
    (ready : execution.application.config.cut.Ready event)
    (valid : execution.application.BindingInvariant)
    (effective : (site.residual site.owner).EffectiveDisclosures
      (.reveal site.published site.owner site.name site.fresh site.binding site.unresolved
        site.next) site.source.registry site.source.revelations)
    (unrecorded : (runtime setup).eventRecorded leaks (execution.recall site.owner) event = false)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event) :
    ((sourceServiceCanonicalOpportunity setup leaks bound profile site.owner event
      (execution.recall site.owner) (execution.observe (application setup leaks) site.owner))
        ⟨none⟩).toReal =
      ((revealKernel site.residual (site.source.view site.owner)) false).toReal := by
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
  calc
    _ = expect (revealKernel residual (source.view owner))
        (fun disclose => if false = disclose then (1 : ℝ) else 0) := by
      apply expect_congr_on_support
      intro disclose supported
      rcases effective_reveal_supported fresh binding unresolved next residual source effective
        disclose supported with rfl | ⟨value, rfl, success⟩
      · have quiet := canonical_resolution_false owner event payload (refs.get binding) _
          outputEq codeEq node execution
        change ((PMF.pure (decision false)) ⟨none⟩).toReal = _
        simp only [decision, quiet, PMF.pure_apply, ENNReal.toReal_one, ↓reduceIte]
      · have resolved := compiled_disclosure_result (graph := graph setup) published binding source
          refs execution.application.config.store agree true
        rw [success, EventGraph.EventCode.resolveOutput?_playerStore] at resolved
        have loud := canonical_resolution_true_not_silent owner event payload (refs.get binding) _
          outputEq codeEq node execution valid value resolved
        change ((PMF.pure (decision true)) ⟨none⟩).toReal = _
        rw [PMF.pure_apply_of_ne _ _ (Ne.symm loud)]
        simp only [ENNReal.toReal_zero, Bool.false_eq_true, ↓reduceIte]
    _ = _ := by rw [expect_ite_eq]; exact mul_one _

/-- A closed inclusion gate forces selected silence even if an authentic
opening remains available. The binding risk scan does not rule this out for
an unrecorded resolution. -/
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
