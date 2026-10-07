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

variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- A ready binding decision decodes even after earlier binding misses. Source
admission constrains its kernel at every abstract view, so failure is excluded. -/
theorem retained_compiled_binding_success
    (profile : BehavioralProfile setup.program) (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (event : (serviceGraph setup mode).EventId)
    (ready : execution.application.config.cut.Ready event)
    (owned : (serviceGraph setup mode).actor? event = some who)
    (payload : L.Ty) (kind : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (choice : (serviceGraph setup mode).Action event)
    (supported : choice ∈ ((compileEventProfile setup.program profile) who event owned
      (setup.eventGraph.fromModeObservation mode who
        ((serviceGraph setup mode).playerObserve who execution.application.config))).support) :
    ∃ value : L.Val payload,
      choice = cast (congrArg EventGraph.EventField.Action kind.symm)
        (PublicationResult.success value) := by
  let config : (serviceGraph setup mode).Config := execution.application.config
  apply compilePolicyTable_admitted_binding setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputRef setup.program) who (profile who) permitted event
    ((serviceGraph setup mode).playerStore who config.store) _
    ?_ ?_ payload kind choice supported
  · intro name cell source visible
    let ref : EventGraph.FieldRef (serviceGraph setup mode).layout (cellField cell) :=
      (ContextRefs.initial setup.context (outputLayout setup.program)).get source
    have available : (ref.get? config.store).isSome = true := ref.get?_isSome config.store (by
      change (some (config.inputs (inputId source))).isSome = true
      rfl)
    exact (congrArg Option.isSome
            (ref.get?_playerStore (graph := serviceGraph setup mode) who config.store
            ((cellVisibleTo_iff_fieldVisibleTo who cell).mp visible))).trans available
  · intro prior before visible
    let ref : EventGraph.FieldRef (serviceGraph setup mode).layout
        ((serviceGraph setup mode).outputLayout prior) := outputRef setup.program prior
    have available : (ref.get? config.store).isSome = true := ref.get?_isSome config.store (by
      change (config.outputs prior).isSome = true
      have notPublication : ¬ ((serviceGraph setup mode).outputLayout event).IsPublication := by
        rw [kind]
        exact id
      exact (config.output_available prior).mpr
        (((serviceGraph_revealRelaxedOrdered setup mode).ready_visible_iff config.cut ready owned
          visible (fun independent => notPublication independent.2.1)
          (fun independent => notPublication independent.1)).mpr before))
    exact (congrArg Option.isSome
            (ref.get?_playerStore (graph := serviceGraph setup mode) who config.store
            visible)).trans available

variable [Fintype Player]

/-- The retained menu uses only bounded raw responses. -/
theorem canonicalMenu_in_raw (bounds : MessageBounds (serviceGraph setup mode)) :
    (bounds.canonicalMenu (serviceRuntime setup mode deadline) leaks).IncludedIn
      (bounds.rawMenu (serviceRuntime setup mode deadline) leaks) := by
  intro who past view response member
  obtain ⟨original, allowed, normal⟩ :=
      ((serviceRuntime setup mode deadline).reactiveNormalization leaks).menu_mem
      (bounds.rawMenu (serviceRuntime setup mode deadline) leaks) who past view response |>.mp
      (bounds.canonicalActions_effective (serviceRuntime setup mode deadline) leaks who past
          view member)
  rw [← normal]
  exact bounds.rawMenu_closed (serviceRuntime setup mode deadline) leaks who past view
      original allowed

omit [Fintype Player] in
private theorem retained_resolutionPacket_allowed
    (bounds : MessageBounds (serviceGraph setup mode))
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (values : bounds.CandidateValues execution.application)
    (handles : bounds.AcceptedHandles execution.application)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : EventGraph.FieldRef (serviceGraph setup mode).layout (.binding who payload))
    (checks : List (EventGraph.GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (choice : (serviceGraph setup mode).Action event) (packet : Payload (serviceGraph setup mode))
    (sent : reactiveResolutionPacket who event payload binding checks outputEq
      choice (execution.observe (serviceApplication setup mode deadline leaks) who).application =
          some packet) :
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
            ((serviceGraph setup mode).playerStore who execution.application.config.store) = _
            at resolved
          rwa [EventGraph.EventCode.resolveOutput?_playerStore] at resolved
        · cases sent
      · cases sent
    · cases sent
    · cases sent
  · cases sent

/-- Local decision admission depends on the actual bounded record and its
selected canonical slot, rather than on how the history reached that record. -/
theorem sourceServiceCanonicalPolicy_retained_of_resources
    (bounds : MessageBounds (serviceGraph setup mode)) (covered : bounds.CoversBindingValues)
    (profile : BehavioralProfile setup.program) (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (values : bounds.CandidateValues execution.application)
    (handles : bounds.AcceptedHandles execution.application)
    (event : (serviceGraph setup mode).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (timely : execution.application.publicView.WithinDeadline
        (serviceRuntime setup mode deadline) event)
    (unsent : (serviceRuntime setup mode deadline).eventRecorded leaks (execution.recall who)
        event = false)
    (counted : execution.application.publicView.bindingCount who < bounds.candidateCount)
    (selected : canonicalFreshSlot who
      (execution.observe (serviceApplication setup mode deadline leaks) who).application =
        some (execution.application.publicView.bindingCount who))
    (response : (serviceApplication setup mode deadline leaks).Action)
    (supported : response ∈ (serviceCanonicalPolicy setup mode deadline leaks profile who
      (execution.recall who)
      (execution.observe (serviceApplication setup mode deadline leaks) who)).support) :
    response ∈ bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who
        (execution.recall who)
      (execution.observe (serviceApplication setup mode deadline leaks) who) := by
  have readyView := (PublicView.ownTurn?_spec _ who event turn).1
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (execution.application.publicView_eventReady event).mp readyView
  rw [sourceServiceCanonicalPolicy_at_event setup leaks profile who execution event
    turn owned] at supported
  obtain ⟨choice, chosen, rfl⟩ := PMF.support_map .. ▸ supported
  cases node : nodeView (serviceGraph setup mode) event with
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
      apply bounds.canonical_binding_value_retained (serviceRuntime setup mode deadline) leaks actor
          _ _ event payload outputEq codeEq node turn owned readyView timely unsent _ selected
          counted value
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
      apply bounds.canonical_resolution_retained (serviceRuntime setup mode deadline) leaks actor _
          _ event actor payload binding checks outputEq codeEq node turn owned readyView timely
          unsent disclose
      exact retained_resolutionPacket_allowed bounds execution valid values handles actor event
        payload binding checks outputEq _

/-- Every timely prescribed canonical decision is in the retained menu at every
bounded raw history where the owner's submissions were made at its own turns
and its used prepared slots stay canonical. The other players' responses are
arbitrary bounded raw responses. -/
theorem sourceServiceCanonicalPolicy_retained_of_slots
    (bounds : MessageBounds (serviceGraph setup mode)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (serviceInitialLaw setup mode).support,
        bounds.CandidateValues state)
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
    (profile : BehavioralProfile setup.program) (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace :
        ((bounds.rawMenu (serviceRuntime setup mode deadline) leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (atTurn : OwnSubmissionsAtTurn setup leaks control.execution who)
    (valid : CanonicalSlotsUsed setup leaks control.execution who)
    (event : (serviceGraph setup mode).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (timely : control.execution.application.publicView.WithinDeadline
        (serviceRuntime setup mode deadline) event)
    (unsent : (serviceRuntime setup mode deadline).eventRecorded leaks
        (control.execution.recall who) event = false)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (supported : response ∈ (serviceCanonicalPolicy setup mode deadline leaks profile who
      (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who)).support) :
    response ∈ bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who
        (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who) := by
  have rawTrace := (bounds.rawMenu (serviceRuntime setup mode deadline) leaks).toRawTrace
      (serviceInitialLaw setup mode) horizon scheduler trace
  obtain ⟨counted, _, selected⟩ := canonicalSlot_resources_of_used bounds capacity rawTrace
    who atTurn valid event turn unsent
  have facts := legalFacts setup leaks horizon scheduler control rawTrace
  have values := bounds.candidateValues_raw_history (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler initialCovered trace
  have boundedTrace := trace
  rw [serviceInitialLaw_eq_inputs] at boundedTrace
  have handles := bounds.executionHandles_raw_history (serviceRuntime setup mode deadline) leaks
    (setup.initialLaw.map setup.eventInputs) horizon scheduler boundedTrace
  exact sourceServiceCanonicalPolicy_retained_of_resources bounds covered profile who permitted
    control.execution facts.binding values handles.1 event turn timely unsent counted selected
    response supported

/-- Every timely prescribed canonical decision is in the retained menu at
every legal retained history, including histories with prior public misses. -/
theorem sourceServiceCanonicalPolicy_retained
    (bounds : MessageBounds (serviceGraph setup mode)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (serviceInitialLaw setup mode).support,
        bounds.CandidateValues state)
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
    (profile : BehavioralProfile setup.program) (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace :
        ((bounds.canonicalMenu (serviceRuntime setup mode deadline) leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (event : (serviceGraph setup mode).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (timely : control.execution.application.publicView.WithinDeadline
        (serviceRuntime setup mode deadline) event)
    (unsent : (serviceRuntime setup mode deadline).eventRecorded leaks
        (control.execution.recall who) event = false)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (supported : response ∈ (serviceCanonicalPolicy setup mode deadline leaks profile who
      (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who)).support) :
    response ∈ bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who
        (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who) := by
  obtain ⟨atTurn, valid⟩ := retainedCanonicalSlots_history bounds control trace who
  exact sourceServiceCanonicalPolicy_retained_of_slots bounds covered initialCovered capacity
    profile who permitted control
    ((canonicalMenu_in_raw bounds).trace (serviceInitialLaw setup mode) horizon scheduler trace)
    atTurn valid
    event turn timely unsent response supported

/-- A guarded opportunity is either silence or a canonical source decision; it
is retained wherever every timely unrecorded canonical decision at the event is.
The protection gate implies the menu's actual deadline gate. -/
theorem sourceServiceCanonicalOpportunity_retained_of
    (bounds : MessageBounds (serviceGraph setup mode))
    (bound : (serviceGraph setup mode).EventId → Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (event : (serviceGraph setup mode).EventId)
    (decided : execution.application.publicView.WithinDeadline (serviceRuntime setup mode deadline)
        event → (serviceRuntime setup mode deadline).eventRecorded leaks (execution.recall who)
        event = false → ∀ response ∈
        (serviceCanonicalPolicy setup mode deadline leaks profile who (execution.recall who)
        (execution.observe (serviceApplication setup mode deadline leaks) who)).support, response ∈
        bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who
        (execution.recall who)
        (execution.observe (serviceApplication setup mode deadline leaks) who))
    (response : (serviceApplication setup mode deadline leaks).Action)
    (supported : response ∈ (serviceCanonicalOpportunity setup mode deadline leaks bound profile who
      event (execution.recall who)
          (execution.observe (serviceApplication setup mode deadline leaks) who)).support) :
    response ∈ bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who
        (execution.recall who)
      (execution.observe (serviceApplication setup mode deadline leaks) who) := by
  have silent : ∀ action ∈
      ((serviceApplication setup mode deadline leaks).silentPolicy (execution.recall who)
          (execution.observe (serviceApplication setup mode deadline leaks) who)).support, action ∈
      bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who (execution.recall who)
        (execution.observe (serviceApplication setup mode deadline leaks) who) := by
    intro action chosen
    cases (PMF.mem_support_pure_iff _ _).mp chosen
    exact bounds.silence_canonical (serviceRuntime setup mode deadline) leaks who _ _
  unfold serviceCanonicalOpportunity at supported
  split at supported
  · exact silent response supported
  · rename_i unrecorded
    split at supported
    · rename_i fits
      rw [PMF.support_bind] at supported
      obtain ⟨chosen, decisionSupported, member⟩ := Set.mem_iUnion₂.mp supported
      split at member
      · exact silent response member
      · have same : response = chosen := (PMF.mem_support_pure_iff _ _).mp member
        rw [same]
        exact decided fits.withinDeadline (by simpa using unrecorded) chosen decisionSupported
    · exact silent response supported

/-- A guarded opportunity is either silence or a retained canonical source
decision. The protection gate implies the menu's actual deadline gate. -/
theorem sourceServiceCanonicalOpportunity_retained
    (bounds : MessageBounds (serviceGraph setup mode)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (serviceInitialLaw setup mode).support,
        bounds.CandidateValues state)
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
    (bound : (serviceGraph setup mode).EventId → Nat) (profile : BehavioralProfile setup.program)
    (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace :
        ((bounds.canonicalMenu (serviceRuntime setup mode deadline) leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (event : (serviceGraph setup mode).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (supported : response ∈ (serviceCanonicalOpportunity setup mode deadline leaks bound profile who
      event (control.execution.recall who)
      (control.execution.observe (serviceApplication setup mode deadline leaks) who)).support) :
    response ∈ bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who
        (control.execution.recall who)
        (control.execution.observe (serviceApplication setup mode deadline leaks) who) :=
  sourceServiceCanonicalOpportunity_retained_of bounds bound profile who control.execution event
    (fun timely unsent => sourceServiceCanonicalPolicy_retained bounds covered initialCovered
      capacity profile who permitted control trace event turn timely unsent) response supported

/-- The turn-counted prescribed policy is retained wherever every timely
unrecorded canonical decision at the owner's turn is. -/
theorem sourceServiceTurnPolicy_retained_of
    (bounds : MessageBounds (serviceGraph setup mode))
    (bound : (serviceGraph setup mode).EventId → Nat)
    (turns : Nat) (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (who : Player) (execution : (serviceApplication setup mode deadline leaks).Execution)
    (decided : ∀ event, execution.application.publicView.ownTurn? who = some event →
      execution.application.publicView.WithinDeadline (serviceRuntime setup mode deadline) event →
      (serviceRuntime setup mode deadline).eventRecorded leaks (execution.recall who)
      event = false →
      ∀ response ∈
          (serviceCanonicalPolicy setup mode deadline leaks profile who (execution.recall who)
              (execution.observe (serviceApplication setup mode deadline leaks) who)).support,
          response ∈ bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who
          (execution.recall who)
          (execution.observe (serviceApplication setup mode deadline leaks) who))
    (response : (serviceApplication setup mode deadline leaks).Action)
    (supported : response ∈
        (serviceTurnPolicy setup mode deadline leaks bound turns timing profile who
        (execution.recall who)
        (execution.observe (serviceApplication setup mode deadline leaks) who)).support) :
    response ∈ bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who
        (execution.recall who)
      (execution.observe (serviceApplication setup mode deadline leaks) who) := by
  have silent : ∀ action ∈
      ((serviceApplication setup mode deadline leaks).silentPolicy (execution.recall who)
          (execution.observe (serviceApplication setup mode deadline leaks) who)).support, action ∈
      bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who (execution.recall who)
        (execution.observe (serviceApplication setup mode deadline leaks) who) := by
    intro action chosen
    cases (PMF.mem_support_pure_iff _ _).mp chosen
    exact bounds.silence_canonical (serviceRuntime setup mode deadline) leaks who _ _
  unfold serviceTurnPolicy at supported
  split at supported
  · exact silent response supported
  · rename_i event turn
    split at supported
    · rw [ReactiveApplication.policyMixture_policy, PMF.support_bind] at supported
      obtain ⟨slot, _, member⟩ := Set.mem_iUnion₂.mp supported
      unfold serviceTurnFamily ReactiveApplication.turnScheduledPolicy at member
      dsimp only at member
      split at member
      · exact sourceServiceCanonicalOpportunity_retained_of bounds bound profile who execution
          event (decided event turn) response member
      · exact silent response member
    · exact silent response supported

/-- Every turn-counted prescribed policy is admissible at every legal retained
history. This includes the first-turn policy and all deferral approximants. -/
theorem sourceServiceTurnPolicy_retained
    (bounds : MessageBounds (serviceGraph setup mode)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (serviceInitialLaw setup mode).support,
        bounds.CandidateValues state)
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode)
    (profile : BehavioralProfile setup.program) (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace :
        ((bounds.canonicalMenu (serviceRuntime setup mode deadline) leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (response : (serviceApplication setup mode deadline leaks).Action)
    (supported : response ∈
        (serviceTurnPolicy setup mode deadline leaks bound turns timing profile who
        (control.execution.recall who)
        (control.execution.observe (serviceApplication setup mode deadline leaks) who)).support) :
    response ∈ bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who
        (control.execution.recall who)
        (control.execution.observe (serviceApplication setup mode deadline leaks) who) :=
  sourceServiceTurnPolicy_retained_of bounds bound turns timing profile who control.execution
    (fun event turn timely unsent => sourceServiceCanonicalPolicy_retained bounds covered
      initialCovered capacity profile who permitted control trace event turn timely unsent)
    response supported

/-- The turn-counted prescribed policy is in the retained menu at every bounded
raw history where the owner's submissions were made at its own turns and its
used prepared slots stay canonical, whatever the other players did. -/
theorem sourceServiceTurnPolicy_retained_of_slots
    (bounds : MessageBounds (serviceGraph setup mode)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (serviceInitialLaw setup mode).support,
        bounds.CandidateValues state)
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode)
    (profile : BehavioralProfile setup.program) (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace :
        ((bounds.rawMenu (serviceRuntime setup mode deadline) leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (atTurn : OwnSubmissionsAtTurn setup leaks control.execution who)
    (valid : CanonicalSlotsUsed setup leaks control.execution who)
    (response : (serviceApplication setup mode deadline leaks).Action)
    (supported : response ∈
        (serviceTurnPolicy setup mode deadline leaks bound turns timing profile who
        (control.execution.recall who)
        (control.execution.observe (serviceApplication setup mode deadline leaks) who)).support) :
    response ∈ bounds.canonicalActions (serviceRuntime setup mode deadline) leaks who
        (control.execution.recall who)
        (control.execution.observe (serviceApplication setup mode deadline leaks) who) :=
  sourceServiceTurnPolicy_retained_of bounds bound turns timing profile who control.execution
    (fun event turn timely unsent => sourceServiceCanonicalPolicy_retained_of_slots bounds covered
      initialCovered capacity profile who permitted control trace atTurn valid event turn timely
      unsent)
    response supported

end Vegas
