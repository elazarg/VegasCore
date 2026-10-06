/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRetainedSlots
import Vegas.Compile.EventGraphObservationEncoding
import Vegas.Source.ProtocolBehavioralPolicy
import Vegas.Pending.ReactiveBoundedValues

/-! # Prescribed policy support on retained service histories

A completed binding miss still supplies its failure-valued output to later
source observations. The compiler therefore decodes every ready source-ranked
decision, including decisions reached after misses. Value-only source admission
then supplies successful binding choices at these abstract views.

This is local policy admissibility. It does not identify a miss-reached source
continuation with a legal history of the original value-only game, and does not
assert that retained histories have zero audit charges.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem compilePolicyTable_admitted_binding
    {Field : Type} {layout : Field → EventGraph.EventField Player L} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (refs : ContextRefs layout Γ) →
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event)) →
    (who : Player) → (policy : BehavioralPolicy who program) →
    policy.Admitted program (CommitmentInterface.values program) →
    (event : Fin (eventCount program)) → (store : EventGraph.Store layout) →
    (history : List (OwnAction Player L)) →
    (∀ {name cell} (source : HasVar Γ name cell), cellVisibleTo who cell →
      ((refs.get source).get? store).isSome = true) →
    (∀ prior, prior.val < event.val → (outputLayout program prior).VisibleTo who →
      ((outputs prior).get? store).isSome = true) →
    ∀ (payload : L.Ty) (kind : outputLayout program event = .binding who payload)
      (choice : EventGraph.EventField.Action (outputLayout program event)),
      choice ∈ (compilePolicyTable program refs outputs who policy event store history).support →
      ∃ value : L.Val payload,
        choice = cast (congrArg EventGraph.EventField.Action kind.symm)
          (PublicationResult.success value) := by
  intro Γ O program
  induction program with
  | ret payoffs =>
      intro refs outputs who policy permitted event
      exact nomatch event
  | sample name fresh law next ih =>
      intro refs outputs who policy permitted event
      refine Fin.cases ?_ (fun tail => ?_) event
      · intro store history available previous payload kind
        cases kind
      · intro store history available previous payload kind choice supported
        let headIndex : Fin (eventCount (.sample name fresh law next)) :=
          ⟨0, by simp [eventCount]⟩
        let headRef : EventGraph.FieldRef layout (.publicData _) := by
          simpa [outputLayout, eventCount, headIndex] using outputs headIndex
        apply ih (refs.cons headRef)
          (fun prior => outputs prior.succ) who policy permitted tail store history
          ?_ ?_ payload kind choice supported
        · intro readName cell source visible
          cases source with
          | here =>
              exact previous headIndex (by simp [headIndex])
                (by simpa [headIndex, outputLayout, eventCount, cellField] using visible)
          | there source => exact available source visible
        · intro prior before visible
          exact previous prior.succ (by simpa using before) visible
  | commit name owner fresh guard next ih =>
      intro refs outputs who policy permitted event
      refine Fin.cases ?_ (fun tail => ?_) event
      · intro store history available previous payload kind choice supported
        cases kind
        obtain ⟨observation, decoded⟩ := exists_decodeObservation_of_available owner refs store
          available
        change choice ∈ (if same : owner = owner then
          match decodeObservation? owner refs store with
          | some view => policy.1 same (view, history)
          | none => PMF.pure PublicationResult.failure
          else PMF.pure PublicationResult.failure).support at supported
        simp only [decoded] at supported
        have admitted := permitted.1 rfl (observation, history) choice supported
        cases choice with
        | failure => cases admitted
        | success value => exact ⟨value, rfl⟩
      · intro store history available previous payload kind choice supported
        let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
          ⟨0, by simp [eventCount]⟩
        let headRef : EventGraph.FieldRef layout (.binding owner _) := by
          simpa [outputLayout, eventCount, headIndex] using outputs headIndex
        apply ih (refs.cons headRef)
          (fun prior => outputs prior.succ) who policy.2 permitted.2 tail store history
          ?_ ?_ payload kind choice supported
        · intro readName cell source visible
          cases source with
          | here =>
              exact previous headIndex (by simp [headIndex])
                (by simpa [headIndex, outputLayout, eventCount, cellField] using visible)
          | there source => exact available source visible
        · intro prior before visible
          exact previous prior.succ (by simpa using before) visible
  | reveal published owner name fresh selected unresolved next ih =>
      intro refs outputs who policy permitted event
      refine Fin.cases ?_ (fun tail => ?_) event
      · intro store history available previous payload kind
        cases kind
      · intro store history available previous payload kind choice supported
        let headIndex : Fin (eventCount
          (.reveal published owner name fresh selected unresolved next)) :=
          ⟨0, by simp [eventCount]⟩
        let headRef : EventGraph.FieldRef layout (.publication _) := by
          simpa [outputLayout, eventCount, headIndex] using outputs headIndex
        apply ih (refs.cons headRef)
          (fun prior => outputs prior.succ) who policy.2 permitted tail store history
          ?_ ?_ payload kind choice supported
        · intro readName cell source visible
          cases source with
          | here =>
              exact previous headIndex (by simp [headIndex])
                (by simpa [headIndex, outputLayout, eventCount, cellField] using visible)
          | there source => exact available source visible
        · intro prior before visible
          exact previous prior.succ (by simpa using before) visible

variable {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A ready binding decision decodes even after earlier binding misses. Source
admission constrains its kernel at every abstract view, so failure is excluded. -/
theorem retained_compiled_binding_success
    (profile : BehavioralProfile setup.program) (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    (execution : (application setup leaks).Execution) (event : (graph setup).EventId)
    (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some who)
    (payload : L.Ty) (kind : (graph setup).outputLayout event = .binding who payload)
    (choice : (graph setup).Action event)
    (supported : choice ∈ ((compileEventProfile setup.program profile) who event owned
      (setup.eventGraph.fromModeObservation .sequential who
        ((graph setup).playerObserve who execution.application.config))).support) :
    ∃ value : L.Val payload,
      choice = cast (congrArg EventGraph.EventField.Action kind.symm)
        (PublicationResult.success value) := by
  let config : (graph setup).Config := execution.application.config
  apply compilePolicyTable_admitted_binding setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputRef setup.program) who (profile who) permitted event
    ((graph setup).playerStore who config.store) _
    ?_ ?_ payload kind choice supported
  · intro name cell source visible
    let ref : EventGraph.FieldRef (graph setup).layout (cellField cell) :=
      (ContextRefs.initial setup.context (outputLayout setup.program)).get source
    have available : (ref.get? config.store).isSome = true := ref.get?_isSome config.store (by
      change (some (config.inputs (inputId source))).isSome = true
      rfl)
    exact (congrArg Option.isSome (ref.get?_playerStore (graph := graph setup) who config.store
      ((cellVisibleTo_iff_fieldVisibleTo who cell).mp visible))).trans available
  · intro prior before visible
    let ref : EventGraph.FieldRef (graph setup).layout ((graph setup).outputLayout prior) :=
      outputRef setup.program prior
    have available : (ref.get? config.store).isSome = true := ref.get?_isSome config.store (by
      change (config.outputs prior).isSome = true
      exact (config.output_available prior).mpr
        (ready.2 ((EventOrder.sequential.mem_predecessors prior event).mpr before)))
    exact (congrArg Option.isSome (ref.get?_playerStore (graph := graph setup) who config.store
      visible)).trans available

variable [Fintype Player]

/-- The retained menu uses only bounded raw responses. -/
theorem canonicalMenu_in_raw (bounds : MessageBounds (graph setup)) :
    (bounds.canonicalMenu (runtime setup) leaks).IncludedIn
      (bounds.rawMenu (runtime setup) leaks) := by
  intro who past view response member
  obtain ⟨original, allowed, normal⟩ := ((runtime setup).reactiveNormalization leaks).menu_mem
    (bounds.rawMenu (runtime setup) leaks) who past view response |>.mp
      (bounds.canonicalActions_effective (runtime setup) leaks who past view member)
  rw [← normal]
  exact bounds.rawMenu_closed (runtime setup) leaks who past view original allowed

omit [Fintype Player] in
private theorem retained_resolutionPacket_allowed
    (bounds : MessageBounds (graph setup)) (execution : (application setup leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (values : bounds.CandidateValues execution.application)
    (handles : bounds.AcceptedHandles execution.application)
    (who : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding who payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (choice : (graph setup).Action event) (packet : Payload (graph setup))
    (sent : reactiveResolutionPacket who event payload binding checks outputEq
      choice (execution.observe (application setup leaks) who).application = some packet) :
    bounds.AllowsPacket packet := by
  dsimp only [reactiveResolutionPacket] at sent
  split at sent
  · split at sent
    · rename_i value resolved
      split at sent
      · rename_i candidate accepted
        split at sent
        · cases sent
          refine ⟨handles binding.field candidate accepted, ?_⟩
          apply bounds.resolved_value_covered execution.application valid values binding checks
            value
          change EventGraph.EventCode.resolveOutput? binding checks true
            ((graph setup).playerStore who execution.application.config.store) = _ at resolved
          rwa [EventGraph.EventCode.resolveOutput?_playerStore] at resolved
        · cases sent
      · cases sent
    · cases sent
    · cases sent
  · cases sent

/-- Local decision admission depends on the actual bounded record and its
selected canonical slot, rather than on how the history reached that record. -/
theorem sourceServiceCanonicalPolicy_retained_of_resources
    (bounds : MessageBounds (graph setup)) (covered : bounds.CoversBindingValues)
    (profile : BehavioralProfile setup.program) (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    (execution : (application setup leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (values : bounds.CandidateValues execution.application)
    (handles : bounds.AcceptedHandles execution.application)
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (timely : execution.application.publicView.WithinDeadline (runtime setup) event)
    (unsent : (runtime setup).eventRecorded leaks (execution.recall who) event = false)
    (counted : execution.application.publicView.bindingCount who < bounds.candidateCount)
    (selected : canonicalFreshSlot who
      (execution.observe (application setup leaks) who).application =
        some (execution.application.publicView.bindingCount who))
    (response : (application setup leaks).Action)
    (supported : response ∈ (sourceServiceCanonicalPolicy setup leaks profile who
      (execution.recall who) (execution.observe (application setup leaks) who)).support) :
    response ∈ bounds.canonicalActions (runtime setup) leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) := by
  have readyView := (PublicView.ownTurn?_spec _ who event turn).1
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (execution.application.publicView_eventReady event).mp readyView
  rw [sourceServiceCanonicalPolicy_at_event setup leaks profile who execution event
    turn owned] at supported
  obtain ⟨choice, chosen, rfl⟩ := PMF.support_map .. ▸ supported
  cases node : nodeView (graph setup) event with
  | sample payload law outputEq codeEq =>
      have ownerless := nodeView_sample_actor outputEq codeEq
      rw [owned] at ownerless
      cases ownerless
  | bind actor payload outputEq codeEq =>
      have actorEq : actor = who :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst actorEq
      obtain ⟨value, rfl⟩ := retained_compiled_binding_success profile actor permitted
        execution event ready owned payload outputEq choice chosen
      apply bounds.canonical_binding_value_retained (runtime setup) leaks actor _ _ event
        payload outputEq codeEq node turn owned readyView timely unsent _ selected counted value
      have all := covered event
      rw [outputEq] at all
      exact all value
  | resolve actor payload binding checks outputEq codeEq =>
      have actorEq : actor = who :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst actorEq
      obtain ⟨disclose, rfl⟩ : ∃ disclose : Bool,
          choice = cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose :=
        ⟨cast (congrArg EventGraph.EventField.Action outputEq) choice,
          ((cast_cast (congrArg EventGraph.EventField.Action outputEq)
            (congrArg EventGraph.EventField.Action outputEq.symm) choice).trans
              (cast_eq _ choice)).symm⟩
      apply bounds.canonical_resolution_retained (runtime setup) leaks actor _ _ event actor
        payload binding checks outputEq codeEq node turn owned readyView timely unsent disclose
      exact retained_resolutionPacket_allowed bounds execution valid values handles actor event
        payload binding checks outputEq _

/-- Every timely prescribed canonical decision is in the retained menu at
every legal retained history, including histories with prior public misses. -/
theorem sourceServiceCanonicalPolicy_retained
    (bounds : MessageBounds (graph setup)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (profile : BehavioralProfile setup.program) (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    (control : (application setup leaks).Control)
    (trace : ((bounds.canonicalMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (timely : control.execution.application.publicView.WithinDeadline (runtime setup) event)
    (unsent : (runtime setup).eventRecorded leaks (control.execution.recall who) event = false)
    (response : (application setup leaks).Action)
    (supported : response ∈ (sourceServiceCanonicalPolicy setup leaks profile who
      (control.execution.recall who)
      (control.execution.observe (application setup leaks) who)).support) :
    response ∈ bounds.canonicalActions (runtime setup) leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) := by
  obtain ⟨counted, _, selected⟩ := retainedCanonicalSlot_resources bounds capacity control trace
    who event turn unsent
  have rawTrace := (bounds.canonicalMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
    horizon scheduler trace
  have facts := legalFacts setup leaks horizon scheduler control rawTrace
  have boundedTrace := (canonicalMenu_in_raw bounds).trace (initialLaw setup) horizon scheduler
    trace
  have values := bounds.candidateValues_raw_history (runtime setup) leaks (initialLaw setup)
    horizon scheduler initialCovered boundedTrace
  rw [initialLaw_eq_inputs] at boundedTrace
  have handles := bounds.executionHandles_raw_history (runtime setup) leaks
    (setup.initialLaw.map setup.eventInputs) horizon scheduler boundedTrace
  exact sourceServiceCanonicalPolicy_retained_of_resources bounds covered profile who permitted
    control.execution facts.binding values handles.1 event turn timely unsent counted selected
    response supported

/-- A guarded opportunity is either silence or a retained canonical source
decision. The protection gate implies the menu's actual deadline gate. -/
theorem sourceServiceCanonicalOpportunity_retained
    (bounds : MessageBounds (graph setup)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (bound : (graph setup).EventId → Nat) (profile : BehavioralProfile setup.program)
    (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    (control : (application setup leaks).Control)
    (trace : ((bounds.canonicalMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (response : (application setup leaks).Action)
    (supported : response ∈ (sourceServiceCanonicalOpportunity setup leaks bound profile who
      event (control.execution.recall who)
      (control.execution.observe (application setup leaks) who)).support) :
    response ∈ bounds.canonicalActions (runtime setup) leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) := by
  have silent : ∀ action ∈ ((application setup leaks).silentPolicy
      (control.execution.recall who)
      (control.execution.observe (application setup leaks) who)).support,
      action ∈ bounds.canonicalActions (runtime setup) leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) := by
    intro action chosen
    cases (PMF.mem_support_pure_iff _ _).mp chosen
    exact bounds.silence_canonical (runtime setup) leaks who _ _
  unfold sourceServiceCanonicalOpportunity at supported
  split at supported
  · exact silent response supported
  · rename_i unrecorded
    split at supported
    · rename_i fits
      rw [PMF.support_bind] at supported
      obtain ⟨decided, decisionSupported, member⟩ := Set.mem_iUnion₂.mp supported
      split at member
      · exact silent response member
      · have same : response = decided := (PMF.mem_support_pure_iff _ _).mp member
        rw [same]
        exact sourceServiceCanonicalPolicy_retained bounds covered initialCovered capacity profile
          who permitted control trace event turn fits.withinDeadline (by simpa using unrecorded)
          decided decisionSupported
    · exact silent response supported

/-- Every turn-counted prescribed policy is admissible at every legal retained
history. This includes the first-turn policy and all deferral approximants. -/
theorem sourceServiceTurnPolicy_retained
    (bounds : MessageBounds (graph setup)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    (control : (application setup leaks).Control)
    (trace : ((bounds.canonicalMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (response : (application setup leaks).Action)
    (supported : response ∈ (sourceServiceTurnPolicy setup leaks bound turns timing profile who
      (control.execution.recall who)
      (control.execution.observe (application setup leaks) who)).support) :
    response ∈ bounds.canonicalActions (runtime setup) leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) := by
  have silent : ∀ action ∈ ((application setup leaks).silentPolicy
      (control.execution.recall who)
      (control.execution.observe (application setup leaks) who)).support,
      action ∈ bounds.canonicalActions (runtime setup) leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) := by
    intro action chosen
    cases (PMF.mem_support_pure_iff _ _).mp chosen
    exact bounds.silence_canonical (runtime setup) leaks who _ _
  unfold sourceServiceTurnPolicy at supported
  split at supported
  · exact silent response supported
  · rename_i event turn
    split at supported
    · rw [ReactiveApplication.policyMixture_policy, PMF.support_bind] at supported
      obtain ⟨slot, _, member⟩ := Set.mem_iUnion₂.mp supported
      unfold sourceServiceTurnFamily ReactiveApplication.turnScheduledPolicy at member
      dsimp only at member
      split at member
      · exact sourceServiceCanonicalOpportunity_retained bounds covered initialCovered capacity
          bound profile who permitted control trace event turn response member
      · exact silent response member
    · exact silent response supported

end Vegas
