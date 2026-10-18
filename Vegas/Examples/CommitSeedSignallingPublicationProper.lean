/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingPublicationAfterSubmission
import Vegas.Examples.CommitSeedSignallingBindingPersistence
import Vegas.Examples.CommitSeedSignallingRememberedRequest
import Vegas.Examples.CommitSeedSignallingPublicationInclusion
import Vegas.Examples.CommitSeedSignallingTailDecision
import Vegas.Examples.CommitSeedSignallingPublicationChoice
import Vegas.Pending.PhaseBindingReceiptResolution
import Interaction.ReactiveAnchoredMixture
import Interaction.ReactiveInvariantPrefix
import Interaction.ReactiveRecordedResponseAfter
import Interaction.ReactiveResponseEvaluation
import GameTheory.Protocol.HistoryEvents

/-! # Proper publication continuations after an arbitrary authentic own past -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem prefixes_comparable {ι : Type*} {E : ExecutionProtocol ι}
    {first second last : E.State} {left : E.Trace first} {right : E.Trace second}
    {final : E.Trace last} (leftKept : TracePrefix left final)
    (rightKept : TracePrefix right final) :
    TracePrefix left right ∨ TracePrefix right left := by
  rcases le_total left.length right.length with before | after
  · exact Or.inl
      (leftKept.reachesWithin.ancestor_comparable rightKept.reachesWithin before).tracePrefix
  · exact Or.inr
      (rightKept.reachesWithin.ancestor_comparable leftKept.reachesWithin after).tracePrefix

private theorem publication_callback_after_reference
    (selected : app.Scheduler) (source : app.Control)
    (sourceTrace : (countedMenu.protocol initial horizon selected).Trace (some source))
    (final : app.Control)
    (trace : (countedMenu.protocol initial horizon selected).Trace (some final))
    (sourceKept : TracePrefix sourceTrace trace)
    (owner : Player)
    (unserved : ∀ entry ∈ source.execution.recall owner,
      ∀ coordinate : CommitAttemptEvent graph, coordinate.event = revealEvent owner →
        ¬ PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)
    (remaining : Nat) (execution : app.Execution)
    (prior : (countedMenu.protocol initial horizon selected).Trace
      (some ⟨remaining, some owner, execution⟩))
    (entry : app.PlayerEntry)
    (postTrace : (countedMenu.protocol initial horizon selected).Trace
      (some ⟨remaining, none, execution.respond app owner entry.action⟩))
    (postKept : TracePrefix postTrace trace) (beforePost : TracePrefix prior postTrace)
    (length : postTrace.length = prior.length + 1)
    (viewed : entry.beforeView = execution.observe app owner)
    (coordinate : CommitAttemptEvent graph) (publication : coordinate.event = revealEvent owner)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate) :
    TracePrefix sourceTrace prior := by
  have notPostBefore : ¬ TracePrefix postTrace sourceTrace := by
    intro past
    have retained := app.reaches_recall_prefix initial horizon selected
      (countedMenu.reaches_raw initial horizon selected past.reachesWithin)
        ⟨remaining, none, execution.respond app owner entry.action⟩ source rfl rfl owner
    obtain ⟨emitted, recalled⟩ := app.respond_recall_entry execution owner entry.action
    have present : (⟨execution.observe app owner, entry.action, emitted⟩ : app.PlayerEntry) ∈
        source.execution.recall owner := retained.subset (by
      rw [recalled]
      exact List.mem_append_right _ (List.mem_singleton_self _))
    exact unserved _ present coordinate publication (by rwa [viewed] at requested)
  have sourceBeforePost := (prefixes_comparable sourceKept postKept).resolve_right notPostBefore
  rcases prefixes_comparable sourceKept (beforePost.trans postKept) with before | after
  · exact before
  · have shorter := after.length_le
    have longer := sourceBeforePost.length_le
    by_cases equal : sourceTrace.length = postTrace.length
    · have same := sourceBeforePost.eq_of_length equal
      have reversed : TracePrefix postTrace sourceTrace := by
        cases same
        exact .refl
      exact (notPostBefore reversed).elim
    · have sameLength : prior.length = sourceTrace.length := by omega
      have same := after.eq_of_length sameLength
      cases same
      exact .refl

/-- Recover a genuine retained publication callback after the reference,
including its successful current store and its actual future-policy choice.
The complete old own word is retained literally. -/
theorem anchored_recorded_publication_data
    (selected : app.Scheduler) (source : app.Control)
    (sourceTrace : (countedMenu.protocol initial horizon selected).Trace (some source))
    (tail : source.execution.application.phases <:+ [publicationPhase])
    (owner : Player) (value : Bool)
    (stored : source.execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (unserved : ∀ entry ∈ source.execution.recall owner,
      ∀ coordinate : CommitAttemptEvent graph, coordinate.event = revealEvent owner →
        ¬ PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)
    (players : Player → app.Policy)
    (final : app.Control)
    (trace : (countedMenu.protocol initial horizon selected).Trace (some final))
    (sourceKept : TracePrefix sourceTrace trace)
    (consistent : (app.anchoredPolicy source.execution players owner).Consistent
      (final.execution.recall owner))
    (coordinate : CommitAttemptEvent graph) (publication : coordinate.event = revealEvent owner)
    (entry : app.PlayerEntry) (recorded : entry ∈ final.execution.recall owner)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate) :
    ∃ (remaining : Nat) (execution : app.Execution)
      (_prior : (countedMenu.protocol initial horizon selected).Trace
        (some ⟨remaining, some owner, execution⟩))
      (postTrace : (countedMenu.protocol initial horizon selected).Trace
        (some ⟨remaining, none, execution.respond app owner entry.action⟩)),
      TracePrefix postTrace trace ∧
      entry.action ∈ countedMenu.actions owner (execution.recall owner)
        (execution.observe app owner) ∧
      execution.application.SeedRequest owner
        ⟨execution.application.attempt, revealEvent owner⟩ ∧
      execution.application.current.native.config.store (.inr (bindingEvent owner)) =
        some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
          (PublicationResult.success value)) ∧
      execution.application.attempt ≠ originalAttempt ∧
      entry.action ∈ (players owner (execution.recall owner)
        (execution.observe app owner)).support := by
  obtain ⟨earlier, later, recalled⟩ := List.mem_iff_append.mp recorded
  obtain ⟨remaining, execution, prior, postTrace, postKept, past, viewed, allowed,
    beforePost, postLength⟩ :=
    countedMenu.recorded_response_after initial horizon selected final trace owner
      earlier entry later recalled
  have kept := publication_callback_after_reference selected source sourceTrace final trace
    sourceKept owner unserved remaining execution prior entry postTrace postKept beforePost
      postLength viewed coordinate publication requested
  have retained := (publication_tail_store_invariant
    source.execution.application.current.native).tracePrefix countedMenu initial horizon
      selected source ⟨remaining, some owner, execution⟩ sourceTrace prior kept
        ⟨tail, fun _ _ same => same⟩
  have currentStored := retained.2 (.inr (bindingEvent owner)) _ stored
  have ownPrefix := app.reaches_recall_prefix initial horizon selected
    (countedMenu.reaches_raw initial horizon selected kept.reachesWithin)
      source ⟨remaining, some owner, execution⟩ rfl rfl owner
  have firstConsistent : (app.anchoredPolicy source.execution players owner).Consistent
      (earlier ++ [entry]) := by
    apply ReactiveApplication.Policy.Consistent.of_append (after := later)
    simpa only [List.append_assoc, List.singleton_append] using (recalled ▸ consistent)
  have sampled := ((app.anchoredPolicy source.execution players owner).consistent_snoc_iff
    earlier entry).mp firstConsistent
  have chosen : entry.action ∈ (players owner (execution.recall owner)
      (execution.observe app owner)).support := by
    have choice := sampled.2
    rw [← past, viewed, app.anchoredPolicy_of_extends source.execution players owner
      (execution.recall owner) (execution.observe app owner) ownPrefix] at choice
    exact choice
  have valid := raw_native_valid selected ⟨remaining, some owner, execution⟩
    (countedMenu.toRawTrace initial horizon selected prior)
  rw [viewed] at requested
  have request := (execution.application.requests_publicView valid owner coordinate).mp requested
  have coordinateEq : coordinate = ⟨execution.application.attempt, revealEvent owner⟩ := by
    cases coordinate with
    | mk attempt event => exact congrArg₂ CommitAttemptEvent.mk request.1 publication
  have currentRequest : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩ := coordinateEq ▸ request
  obtain ⟨phase, installed, _inside⟩ := currentRequest.2.1
  obtain ⟨rest, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp installed)
  have present : phase ∈ execution.application.phases := by
    rw [phases]
    exact List.mem_cons_self
  have same : phase = publicationPhase := List.mem_singleton.mp
    (retained.1.sublist.subset present)
  subst phase
  have head : execution.application.phases.head? = some publicationPhase :=
    Option.mem_def.mp installed
  have retired : execution.application.attempt ≠ originalAttempt := by
    intro original
    have phaseEq := congrArg CommitAttemptId.phase original
    simp only [PhaseRuntimeState.attempt, head, Option.map_some, Option.getD_some] at phaseEq
    change 2 = 0 at phaseEq
    omega
  exact ⟨remaining, execution, prior, postTrace, postKept, allowed, currentRequest,
    currentStored, retired, chosen⟩

/-- Proper future play supplies the successful opening at the genuine retained
callback recovered by the common publication chronology proof. -/
theorem anchored_recorded_publication_survives
    (seed : Seeds) (source : app.Control)
    (sourceTrace : (countedMenu.protocol initial horizon (family seed)).Trace (some source))
    (tail : source.execution.application.phases <:+ [publicationPhase])
    (owner : Player) (value : Bool)
    (stored : source.execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (unserved : ∀ entry ∈ source.execution.recall owner,
      ∀ coordinate : CommitAttemptEvent graph, coordinate.event = revealEvent owner →
        ¬ PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool)
    (players : Player → app.Policy) (proper : players owner = properPolicy rule owner)
    (final : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace (some final))
    (sourceKept : TracePrefix sourceTrace trace)
    (consistent : (app.anchoredPolicy source.execution players owner).Consistent
      (final.execution.recall owner))
    (coordinate : CommitAttemptEvent graph) (publication : coordinate.event = revealEvent owner)
    (entry : app.PlayerEntry) (recorded : entry ∈ final.execution.recall owner)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate) :
    owner ∉ final.execution.application.current.excluded := by
  obtain ⟨remaining, execution, prior, postTrace, postKept, _allowed, currentRequest,
    currentStored, retired, chosen⟩ :=
    anchored_recorded_publication_data (family seed) source sourceTrace tail owner value stored
      unserved players final trace sourceKept consistent coordinate publication entry recorded
        requested
  rw [proper] at chosen
  have unsubmitted := fixed_tail_callback_unsubmitted seed remaining execution owner prior
    ⟨execution.application.attempt, revealEvent owner⟩ retired currentRequest
  have recallEq := PhaseCount.countRecall_history runtime leaks
    (countedMenu.toRawTrace initial horizon (family seed) prior)
  have unsent (message : Message Player (CommitAttemptPacket graph))
      (present : message ∈ app.outputs (execution.recall owner)) :
      PhaseCount.event? message.payload ≠
        some ⟨execution.application.attempt, revealEvent owner⟩ := by
    rw [← recallEq.1 owner] at present
    exact unsubmitted message (List.mem_filter.mp present).1
      (of_decide_eq_true (List.mem_filter.mp present).2)
  obtain ⟨checks, codeEq, node⟩ := own_reveal_descriptor owner
  have typed : (ownBindingRef owner).get? execution.application.current.native.config.store =
      some (.success value) := by
    fin_cases owner <;> exact currentStored
  obtain ⟨candidate, _accepted, literal⟩ :=
    properPolicy_opening_response rule (family seed)
    ⟨remaining, some owner, execution⟩ prior owner (revealEvent owner) (ownBindingRef owner) checks
      (revealEvent_layout owner) codeEq node currentRequest unsent value typed
  rw [literal, PMF.mem_support_pure_iff] at chosen
  let material : WitnessedSubmission graph :=
    disclosureSubmission (.opening (revealEvent owner) candidate ⟨.bool, value⟩)
  have actionEq : entry.action = (⟨some material⟩ : app.Action) := chosen
  have supported : (⟨some material⟩ : app.Action) ∈
      (properPolicy rule owner (execution.recall owner)
        (execution.observe app owner)).support := by
    rw [literal]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have offered := properPolicy_counted rule owner (execution.recall owner)
    (execution.observe app owner) ⟨some material⟩ supported
  rcases entry with ⟨entryView, ⟨transmission⟩, emitted⟩
  have transmissionEq : transmission = some material :=
    congrArg (fun action : app.Action => action.transmission) actionEq
  cases transmissionEq
  exact family_publication_after_submission_survives seed remaining execution owner prior retired
    currentRequest value currentStored material offered postTrace final trace postKept

private theorem excluded_permanent (owner : Player) :
    app.Invariant (fun state => owner ∈ state.current.excluded) where
  submit state actor material excluded :=
    (phaseApplication_exclusion_monotone runtime leaks).submit state actor material excluded
  handle state message next excluded handled :=
    (phaseApplication_exclusion_monotone runtime leaks).handle state message next handled excluded
  environment state command next excluded reached :=
    (phaseApplication_exclusion_monotone runtime leaks).environment state command next reached
      excluded

private theorem publication_passive_survives
    (selected : app.Scheduler) (source : app.Control)
    (sourceTrace : (countedMenu.protocol initial horizon selected).Trace (some source))
    (tail : source.execution.application.phases <:+ [publicationPhase])
    (owner : Player) (value : Bool)
    (stored : source.execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (remaining : Nat) (execution : app.Execution)
    (prior : (countedMenu.protocol initial horizon selected).Trace
      (some ⟨remaining, none, execution⟩))
    (sourceBefore : TracePrefix sourceTrace prior)
    (afterRemaining : Nat) (after : app.Execution)
    (joint : Player → Option app.Action)
    (legal : (countedMenu.protocol initial horizon selected).Legal
      (some ⟨remaining, none, execution⟩) joint)
    (moved : some (⟨afterRemaining, none, after⟩ : app.Control) ∈
      (app.transition initial horizon selected
        (some ⟨remaining, none, execution⟩) joint).support)
    (final : app.Control)
    (trace : (countedMenu.protocol initial horizon selected).Trace (some final))
    (kept : TracePrefix (prior.extend joint legal moved) trace)
    (requestRecorded : ∀ remaining execution
      (_prior : (countedMenu.protocol initial horizon selected).Trace
        (some ⟨remaining, none, execution⟩)) (coordinate : CommitAttemptEvent graph),
      execution.application.SeedRequest owner coordinate →
      0 < PhaseSeedScheduler.elapsed runtime leaks coordinate
        (execution.observeEnvironment app) →
      ∃ entry ∈ execution.recall owner,
        PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)
    (responseSurvives : ∀ (coordinate : CommitAttemptEvent graph),
      coordinate.event = revealEvent owner → ∀ entry ∈ final.execution.recall owner,
      PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate →
      owner ∉ final.execution.application.current.excluded)
    (active : owner ∉ execution.application.current.excluded) :
    owner ∉ after.application.current.excluded := by
  classical
  let nextTrace := prior.extend joint legal moved
  have current := (publication_tail_store_invariant
    source.execution.application.current.native).tracePrefix countedMenu initial horizon
      selected source ⟨remaining, none, execution⟩ sourceTrace prior sourceBefore
        ⟨tail, fun _ _ same => same⟩
  have currentStored := current.2 (.inr (bindingEvent owner)) _ stored
  have nextPrefix : TracePrefix prior nextTrace := by
    change TracePrefix prior (prior.extend joint legal moved)
    exact @TracePrefix.extend Player (countedMenu.protocol initial horizon selected)
      _ prior _ _ prior .refl joint legal moved
  cases phases : execution.application.phases with
  | nil =>
      have positioned := (raw_phase_geometry selected ⟨remaining, none, execution⟩
        (countedMenu.toRawTrace initial horizon selected prior)).1.positioned
      rw [phases] at positioned
      change execution.application.current.native.config.cut.IsPrefix graph.order.eventCount
        at positioned
      exact ((finished_owner_invariant owner).tracePrefix countedMenu initial horizon selected
        ⟨remaining, none, execution⟩ ⟨afterRemaining, none, after⟩ prior nextTrace nextPrefix
          ⟨by rw [phases]; exact List.nil_suffix,
            fun event _ => (positioned.2 event).mpr event.isLt, active⟩).2.2
  | cons phase rest =>
      have same : phase = publicationPhase := List.mem_singleton.mp
        (current.1.sublist.subset (by rw [phases]; exact List.mem_cons_self))
      subst phase
      have installed : execution.application.phases.head? = some publicationPhase := by
        rw [phases]
        rfl
      intro excluded
      obtain ⟨operation, stepped⟩ :=
        PhaseService.new_exclusion_application_command runtime leaks plan
        (setup.initialLaw.map encodeInputs) horizon selected
          ⟨remaining, none, execution⟩ ⟨afterRemaining, none, after⟩ joint moved owner active
            excluded (by
              intro message next handled
              exact phase_handle_keeps_successful_binding_owner execution.application next message
                owner value currentStored active handled)
      obtain ⟨updated, updatedSupport, equal⟩ := PMF.support_map .. ▸ stepped
      obtain ⟨native, supported, stateEq⟩ := PMF.support_map .. ▸ updatedSupport
      have afterApplication : after.application = native :=
        (congrArg (fun result : app.Execution => result.application) equal).symm.trans
          (congrArg (fun result : app.Execution => result.application) stateEq).symm
      obtain ⟨event, _native, commandEq, inside, request, _step, _completed, _normalized⟩ :=
        PhaseRuntimeState.environment_new_exclusion_request runtime execution.application native
          publicationPhase (Option.mem_def.mpr installed) operation supported owner active
            (by simpa only [afterApplication] using excluded)
      have publication : event = revealEvent owner := by
        have interval := (RuntimePhase.mem_events publicationPhase event).mp inside
        change 2 ≤ event.val ∧ event.val < 4 at interval
        have actor : graph.actor? event = some owner := request.2.2.2.1
        fin_cases event
        · change 2 ≤ 0 ∧ 0 < 4 at interval; omega
        · change 2 ≤ 1 ∧ 1 < 4 at interval; omega
        · change some alice = some owner at actor
          cases Option.some.inj actor
          rfl
        · change some bob = some owner at actor
          cases Option.some.inj actor
          rfl
      have expiry : after ∈
          (execution.environmentStep app (.application (.expire event))).support := by
        rwa [commandEq] at stepped
      have nativeMoved : after.application ∈
          (execution.application.environment runtime (.expire event)).support := by
        simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at expiry
        obtain ⟨state, reached, rfl⟩ := PMF.support_map .. ▸ expiry
        exact reached
      have valid := raw_native_valid selected ⟨remaining, none, execution⟩
        (countedMenu.toRawTrace initial horizon selected prior)
      obtain ⟨entered, stamp⟩ := Option.isSome_iff_exists.mp
        ((valid.active.activated_iff event).mpr
          ⟨request.2.2.1, by rw [request.2.2.2.1]; rfl⟩)
      have due : runtime.deadline event ≤ execution.application.current.native.clock - entered := by
        by_contra early
        have timely : execution.application.current.native.WithinDeadline runtime event := by
          rw [State.WithinDeadline, stamp]
          omega
        exact (PhaseRuntimeState.expiry_request_before_deadline runtime execution.application
          after.application owner _ request timely nativeMoved).2.2.2.2 excluded
      have positive : 0 < PhaseSeedScheduler.elapsed runtime leaks
          ⟨execution.application.attempt, event⟩ (execution.observeEnvironment app) := by
        change 0 < execution.application.current.native.clock -
          (execution.application.current.native.activatedAt event).getD
            execution.application.current.native.clock
        rw [stamp, Option.getD_some]
        change 6 ≤ execution.application.current.native.clock - entered at due
        omega
      obtain ⟨entry, recorded, requested⟩ := requestRecorded remaining execution prior
        ⟨execution.application.attempt, event⟩ request positive
      have recalled := app.reaches_recall_prefix initial horizon selected
        (countedMenu.reaches_raw initial horizon selected
          (nextPrefix.trans kept).reachesWithin)
          ⟨remaining, none, execution⟩ final rfl rfl owner
      have survives := responseSurvives ⟨execution.application.attempt, event⟩ publication
        entry (recalled.subset recorded) requested
      have finalExcluded := (excluded_permanent owner).tracePrefix countedMenu initial horizon
        selected ⟨afterRemaining, none, after⟩ final nextTrace trace kept excluded
      exact survives finalExcluded

/-- The actual first-exclusion induction reduces publication-suffix survival
to the existence and protection of its retained own publication callbacks. -/
theorem publication_trace_survives
    (selected : app.Scheduler) (source : app.Control)
    (sourceTrace : (countedMenu.protocol initial horizon selected).Trace (some source))
    (tail : source.execution.application.phases <:+ [publicationPhase])
    (owner : Player) (value : Bool)
    (stored : source.execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (active : owner ∉ source.execution.application.current.excluded)
    (final : app.Control)
    (trace : (countedMenu.protocol initial horizon selected).Trace (some final))
    (kept : TracePrefix sourceTrace trace)
    (requestRecorded : ∀ remaining execution
      (_prior : (countedMenu.protocol initial horizon selected).Trace
        (some ⟨remaining, none, execution⟩)) (coordinate : CommitAttemptEvent graph),
      execution.application.SeedRequest owner coordinate →
      0 < PhaseSeedScheduler.elapsed runtime leaks coordinate
        (execution.observeEnvironment app) →
      ∃ entry ∈ execution.recall owner,
        PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)
    (responseSurvives : ∀ (coordinate : CommitAttemptEvent graph),
      coordinate.event = revealEvent owner → ∀ entry ∈ final.execution.recall owner,
      PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate →
      owner ∉ final.execution.application.current.excluded) :
    owner ∉ final.execution.application.current.excluded := by
  have along {state : app.ProtocolState}
      (past : (countedMenu.protocol initial horizon selected).Trace state)
      (sourceBefore : TracePrefix sourceTrace past) :
      TracePrefix past trace → ∃ current : app.Control, state = some current ∧
        owner ∉ current.execution.application.current.excluded := by
    refine Trace.rec (motive := fun state past =>
      TracePrefix sourceTrace past → TracePrefix past trace →
        ∃ current : app.Control, state = some current ∧
          owner ∉ current.execution.application.current.excluded) ?_ ?_ past sourceBefore
    · intro impossible
      cases impossible
    · intro before after prior joint legal moved ih sourceBefore afterKept
      cases sourceBefore with
      | refl => exact ⟨source, rfl, active⟩
      | extend beforeKept _ _ _ =>
        obtain ⟨current, rfl, currentActive⟩ :=
          ih beforeKept ((TracePrefix.extend .refl joint legal moved).trans afterKept)
        have realized := moved
        change after ∈ (app.transition initial horizon selected (some current) joint).support
          at realized
        obtain ⟨next, rfl, _recall⟩ := app.transition_recall_prefix initial horizon selected
          current after joint realized
        refine ⟨next, rfl, ?_⟩
        rcases current with ⟨remaining, actor, execution⟩
        cases actor with
        | some responder =>
            cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp realized)
            rcases action : (joint responder).getD ⟨none⟩ with ⟨transmission⟩
            cases transmission <;> exact currentActive
        | none =>
            cases remaining with
            | zero =>
                cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp realized)
                exact currentActive
            | succ remaining =>
                have actualMove := realized
                obtain ⟨command, _selected, stepped⟩ :=
                  Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ realized)
                obtain ⟨result, environment, equal⟩ := PMF.support_map .. ▸ stepped
                cases Option.some.inj equal
                cases command with
                | wait =>
                    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
                      at environment
                    cases (PMF.mem_support_pure_iff _ _).mp environment
                    exact currentActive
                | activate responder =>
                    obtain ⟨observed, observedSupport, exactResult⟩ :=
                      PMF.support_map .. ▸ environment
                    obtain ⟨view, _chosen, exactObserved⟩ := PMF.support_map .. ▸ observedSupport
                    cases exactObserved
                    cases exactResult
                    exact currentActive
                | «include» identifier =>
                    exact publication_passive_survives selected source sourceTrace tail owner
                      value stored (remaining + 1) execution prior
                        beforeKept
                        remaining result joint legal actualMove final trace afterKept
                          requestRecorded responseSurvives currentActive
                | application operation =>
                    exact publication_passive_survives selected source sourceTrace tail owner
                      value stored (remaining + 1) execution prior
                        beforeKept
                        remaining result joint legal actualMove final trace afterKept
                          requestRecorded responseSurvives currentActive
  obtain ⟨current, same, survives⟩ := along trace kept .refl
  cases Option.some.inj same
  exact survives

/-- The proper policy supplies the local response-survival obligation in the
shared first-exclusion induction, retaining the complete authentic old word. -/
theorem anchored_publication_trace_survives
    (seed : Seeds) (source : app.Control)
    (sourceTrace : (countedMenu.protocol initial horizon (family seed)).Trace (some source))
    (tail : source.execution.application.phases <:+ [publicationPhase])
    (owner : Player) (value : Bool)
    (stored : source.execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (unserved : ∀ entry ∈ source.execution.recall owner,
      ∀ coordinate : CommitAttemptEvent graph, coordinate.event = revealEvent owner →
        ¬ PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)
    (active : owner ∉ source.execution.application.current.excluded)
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool)
    (players : Player → app.Policy) (proper : players owner = properPolicy rule owner)
    (final : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace (some final))
    (kept : TracePrefix sourceTrace trace)
    (consistent : (app.anchoredPolicy source.execution players owner).Consistent
      (final.execution.recall owner)) :
    owner ∉ final.execution.application.current.excluded := by
  apply publication_trace_survives (family seed) source sourceTrace tail owner value stored active
    final trace kept
  · intro remaining execution prior coordinate request positive
    exact positive_age_own_request seed remaining execution prior coordinate owner request positive
  · intro coordinate publication entry recorded requested
    exact anchored_recorded_publication_survives seed source sourceTrace tail owner value stored
      unserved rule players proper final trace kept consistent coordinate publication entry
        recorded requested

/-- The complete physical continuation from the authentic publication entry
retains its original past and all opposing policies. Proper future play alone
protects the successful owner; no previous-word policy consistency is assumed. -/
theorem proper_publication_run_survives
    (seed : Seeds) (remaining : Nat) (execution : app.Execution)
    (sourceTrace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (tail : execution.application.phases <:+ [publicationPhase])
    (owner : Player) (value : Bool)
    (stored : execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (unserved : ∀ entry ∈ execution.recall owner,
      ∀ coordinate : CommitAttemptEvent graph, coordinate.event = revealEvent owner →
        ¬ PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)
    (active : owner ∉ execution.application.current.excluded)
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (proper : players owner = properPolicy rule owner)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players remaining execution).support) :
    owner ∉ final.application.current.excluded := by
  let source : app.Control := ⟨remaining, none, execution⟩
  let anchored := app.anchoredPolicy execution players
  have anchoredReached : final ∈
      (app.runRounds (family seed) anchored remaining execution).support := by
    simpa only [anchored, app.runRounds_anchoredPolicy] using reached
  have consistency := (app.consistentRecall_policyInvariant anchored).runRounds (family seed)
    remaining execution final (fun who => app.anchoredPolicy_consistent execution players who)
      anchoredReached
  have coveredAnchored : ∀ who past view action, action ∈ (anchored who past view).support →
      action ∈ countedMenu.actions who past view := by
    intro who
    exact countedMenu.anchoredPolicy_covered initial horizon (family seed) source sourceTrace
      players who (covered who)
  let policies :
      ∀ who, (countedMenu.information initial horizon (family seed)).BehavioralPolicy who :=
    fun who => countedMenu.restrictPolicy initial horizon (family seed) who (anchored who)
  have decoded : countedMenu.decodeProfile initial horizon (family seed) policies = anchored := by
    funext who
    exact countedMenu.decode_restrictPolicy_of_covered initial horizon (family seed) who
      (anchored who) (coveredAnchored who)
  let history : (countedMenu.protocol initial horizon (family seed)).History :=
    ⟨some source, sourceTrace⟩
  let fuel := app.rank horizon history.state
  have law := countedMenu.run_eq_finish initial horizon (family seed) policies fuel history le_rfl
  rw [decoded] at law
  have physical : some (⟨0, none, final⟩ : app.Control) ∈
      (app.finish initial horizon (family seed) anchored (some source)).support := by
    simp only [ReactiveApplication.finish, source, ReactiveApplication.resume, PMF.pure_bind]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, anchoredReached, rfl⟩
  rw [← law, PMF.support_map] at physical
  obtain ⟨ending, supported, stateEq⟩ := physical
  have path :=
    (countedMenu.information initial horizon (family seed)).runBehavioralFrom_reachesWithin
    policies fuel history ending supported
  rcases ending with ⟨endingState, endingTrace⟩
  change endingState = some (⟨0, none, final⟩ : app.Control) at stateEq
  subst endingState
  have kept : TracePrefix sourceTrace endingTrace := path.tracePrefix
  exact anchored_publication_trace_survives seed source sourceTrace tail owner value stored
    unserved active rule players proper ⟨0, none, final⟩ endingTrace kept (consistency owner)

end Vegas.Examples.CommitSeedSignalling
