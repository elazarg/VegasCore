/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceChoiceSupport
import Vegas.Game.SourceServiceDecisionSupport

/-! # Actual native choices supported by the source compiler

At every legal retained decision, each physical response is either a replay
alias or lies in the actual source compiler's response law. This includes
every typed binding value and every effective guarded disclosure. The proof
uses the derived residual support property at the actual source checkpoint;
neither source-state reachability nor a normalized equilibrium is assumed.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Every semantic decision at an actual owned source-service input has
positive source compiler probability when the residual effective choices
have full support. This includes withholding at guarded disclosures. -/
theorem sourceService_decision_supported
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (full : ∀ player, (profile player).SupportsEffectiveChoices setup.program
      (CommitmentInterface.values setup.program) [] (Revelations.initial setup.context))
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (target : (graph setup).EventId)
    (grantedTarget : control.execution.application.serviceGrant = some target)
    (owned : (graph setup).actor? target = some who)
    (response : (application setup leaks).Action)
    (member : response ∈ bounds.decisionActions (runtime setup) leaks who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who)) :
    response ∈ (sourceServicePolicy setup leaks profile who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who)).support := by
  classical
  let app := application setup leaks
  let execution := control.execution
  obtain ⟨event, slot, initial, _, _, Γ, names, remaining, remainingProfile, source,
      refs, embedding, refsBefore, aligned, _, ⟨inherited, _⟩,
      granted, prior, sample, _, grant, _, _, _, _, publicEq, checkpoint, _⟩ :=
    sourceService_decision_boundary setup leaks bounds values capacity rosters opportunities
      network profile who control trace active
  have grantNow : execution.application.serviceGrant = some event :=
    (congrArg PublicView.serviceGrant publicEq).trans grant
  have ready : execution.application.config.cut.Ready event :=
    (ready_iff_rank setup _ event.val checkpoint.ordered event).mpr rfl
  have readyView : (execution.observe app who).application.publicView.EventReady event :=
    (execution.application.publicView_eventReady event).mpr ready
  have same : target = event := Option.some.inj (grantedTarget.symm.trans grantNow)
  subst target
  have decision := member
  change response ∈ bounds.decisionActions (runtime setup) leaks who
    (execution.recall who) (execution.observe app who) at decision
  cases remaining with
  | ret result =>
      have count := aligned.graphSuffix.countEq
      simp only [eventCount, Nat.add_zero] at count
      have inside := event.isLt
      change event.val < eventCount setup.program at inside
      omega
  | sample name fresh law next =>
      let index : Fin (eventCount (.sample name fresh law next)) :=
        ⟨0, by simp [eventCount]⟩
      have same : embedding.event index = event := by
        apply Fin.ext
        simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
      have actor := aligned.actorEq index
      rw [same] at actor
      change (graph setup).actor? event = none at actor
      rw [owned] at actor
      cases actor
  | @commit Γ names name owner payload fresh guard next =>
      let index : Fin (eventCount (.commit name owner fresh guard next)) :=
        ⟨0, by simp [eventCount]⟩
      have same : embedding.event index = event := by
        apply Fin.ext
        simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
      have actor := aligned.actorEq index
      rw [same] at actor
      change (graph setup).actor? event = some owner at actor
      cases Option.some.inj (owned.symm.trans actor)
      have outputEq : (graph setup).outputLayout (embedding.event index) =
          .binding who payload := by
        change outputLayout setup.program (embedding.event index) = _
        simpa [index, outputLayout, eventCount] using embedding.layout_eq index
      have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes (embedding.event index)) = .bind who payload := by
        change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
          ((toEventGraph setup.program).nodes (embedding.event index)) = _
        simpa [index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
      have node : nodeView (graph setup) (embedding.event index) =
          .bind who payload outputEq codeEq :=
        EventGraphRuntime.nodeView_eq_bind _ _
      have grantedHead : execution.application.serviceGrant =
          some (embedding.event index) := by rw [same]; exact grantNow
      have ownedHead : (graph setup).actor? (embedding.event index) = some who := by
        rw [same]; exact owned
      have readyHead : (execution.observe app who).application.publicView.EventReady
          (embedding.event index) := by rw [same]; exact readyView
      have grantedView : (execution.observe app who).application.publicView.serviceGrant =
          some (embedding.event index) := grantedHead
      simp only [MessageBounds.decisionActions, grantedView, ownedHead, readyHead,
        and_self, ↓reduceIte, node, Finset.mem_image] at decision
      obtain ⟨value, _, choiceEq⟩ := decision
      rw [sourceServicePolicy_commit setup leaks fresh guard next profile remainingProfile
        refs source embedding refsBefore event.val aligned execution checkpoint.agrees
        checkpoint.history grantedHead, PMF.support_map]
      refine ⟨.success value, ?_, choiceEq⟩
      exact (inherited full who).1 rfl (source.view who) (.success value) trivial
  | @reveal Γ names published owner name payload fresh binding unresolved next =>
      let index : Fin (eventCount
          (.reveal published owner name fresh binding unresolved next)) :=
        ⟨0, by simp [eventCount]⟩
      have same : embedding.event index = event := by
        apply Fin.ext
        simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
      have actor := aligned.actorEq index
      rw [same] at actor
      change (graph setup).actor? event = some owner at actor
      cases Option.some.inj (owned.symm.trans actor)
      have outputEq : (graph setup).outputLayout (embedding.event index) =
          .publication payload := by
        change outputLayout setup.program (embedding.event index) = _
        simpa [index, outputLayout, eventCount] using embedding.layout_eq index
      let checks := compileChecks (published := published) refs
        source.registry source.revelations binding
      have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes (embedding.event index)) =
            .resolve who payload (refs.get binding) checks := by
        change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
          ((toEventGraph setup.program).nodes (embedding.event index)) = _
        simpa [index, compileRankedNodes, checks] using aligned.graphSuffix.nodeEq index
      have node : nodeView (graph setup) (embedding.event index) =
          .resolve who payload (refs.get binding) checks outputEq codeEq :=
        EventGraphRuntime.nodeView_eq_resolve _ _
      have grantedHead : execution.application.serviceGrant =
          some (embedding.event index) := by rw [same]; exact grantNow
      have ownedHead : (graph setup).actor? (embedding.event index) = some who := by
        rw [same]; exact owned
      have readyHead : (execution.observe app who).application.publicView.EventReady
          (embedding.event index) := by rw [same]; exact readyView
      have grantedView : (execution.observe app who).application.publicView.serviceGrant =
          some (embedding.event index) := grantedHead
      simp only [MessageBounds.decisionActions, grantedView, ownedHead, readyHead,
        and_self, ↓reduceIte, node, Finset.mem_image] at decision
      obtain ⟨disclose, _, choiceEq⟩ := decision
      rw [sourceServicePolicy_reveal setup leaks fresh binding unresolved next profile
        remainingProfile refs source embedding refsBefore event.val aligned execution
        checkpoint.agrees checkpoint.history grantedHead, PMF.support_map]
      refine ⟨effectiveDisclosure published binding source disclose, ?_, ?_⟩
      · apply (inherited full who).1 rfl (source.view who)
        simpa only [Config.view, effectiveDisclosureView_observe] using
          effectiveDisclosure_idempotent published binding source disclose
      · exact (serviceDecision_effectiveDisclosure (runtime setup) leaks published binding
          source refs execution checkpoint.agrees (embedding.event index) outputEq codeEq
            node disclose).symm.trans choiceEq

/-- A retained response at any actual source-service decision is supported
by its replay law or by the actual compiled source decision law. -/
theorem sourceService_response_supported
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (full : ∀ player, (profile player).SupportsEffectiveChoices setup.program
      (CommitmentInterface.values setup.program) [] (Revelations.initial setup.context))
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (response : (application setup leaks).Action)
    (member : response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who)) :
    response ∈ ((application setup leaks).replayPolicy (control.execution.recall who)
      (control.execution.observe (application setup leaks) who)).support ∨
    response ∈ (sourceServicePolicy setup leaks profile who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who)).support := by
  classical
  let app := application setup leaks
  obtain ⟨event, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, grant,
      _, _, _, _, publicEq, _, _⟩ :=
    sourceService_decision_boundary setup leaks bounds values capacity rosters opportunities
      network profile who control trace active
  have granted : control.execution.application.serviceGrant = some event :=
    (congrArg PublicView.serviceGrant publicEq).trans grant
  have member := sourceServiceMenu_in_compiled setup leaks bounds rosters who _ _ member
  by_cases owned : (graph setup).actor? event = some who
  · rcases Finset.mem_union.mp (Finset.mem_inter.mp member).1 with decision | replay
    · exact Or.inr (sourceService_decision_supported setup leaks bounds values capacity rosters
        opportunities network profile full who control trace active event granted owned response
        (Finset.mem_filter.mp decision).1)
    · exact Or.inl (((application setup leaks).mem_replayActions_iff _ _ _).mp replay)
  · exact Or.inl (bounds.compiled_foreign_transport (runtime setup) leaks who
      (control.execution.recall who) (control.execution.observe app who)
      event granted owned response member)

end Vegas
