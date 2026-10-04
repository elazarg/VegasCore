/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateResolutionNativePerturbation
import Interaction.ReactiveResponseKernel
import Interaction.ReactiveTraceDepth

/-! # The actual first owner input is deterministic

Initialization and the two public samples precede every player response. This
identifies the first input from the actual control kernel for arbitrary native
profiles, rather than postulating its source or information likelihood.
-/

noncomputable section

namespace Vegas.LateResolutionService

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory GameTheory.Math.Probability

def firstInitialState : app.State := State.initial (setup.eventInputs sourceInitial)

theorem firstSample0Ready : firstInitialState.config.cut.Ready sample0 := by decide

def firstSample0State : app.State := firstInitialState.complete sample0 firstSample0Ready
  PUnit.unit true

theorem firstSample1Ready : firstSample0State.config.cut.Ready sample1 := by decide

def firstSample1State : app.State := firstSample0State.complete sample1 firstSample1Ready
  PUnit.unit true

def firstInitialExecution : app.Execution := ReactiveApplication.Execution.initial app
  firstInitialState

def firstSample0Execution : app.Execution :=
  { firstInitialExecution with
    application := firstSample0State
    environmentRecall := [⟨firstInitialExecution.observeEnvironment app,
      .application (.executeSample sample0)⟩] }

def firstSample1Execution : app.Execution :=
  { firstSample0Execution with
    application := firstSample1State
    environmentRecall := firstSample0Execution.environmentRecall ++
      [⟨firstSample0Execution.observeEnvironment app, .application (.executeSample sample1)⟩] }

def firstExecution : app.Execution :=
  { firstSample1Execution with environmentRecall := firstSample1Execution.environmentRecall ++
      [⟨firstSample1Execution.observeEnvironment app, .activate owner⟩] }

theorem first_sample_environment (state : app.State) (event : nativeGraph.EventId)
    (ready : state.config.cut.Ready event)
    (outputEq : nativeGraph.outputLayout event = .publicData BaseTy.bool)
    (law : PublicDist (L := simpleExpr) nativeGraph.layout BaseTy.bool)
    (codeEq : cast (congrArg (EventCode (L := simpleExpr) nativeGraph.layout) outputEq)
      (nativeGraph.nodes event) = EventCode.sample (L := simpleExpr) BaseTy.bool law)
    (evaluated : (nativeGraph.nodes event).eval?
      (cast (congrArg EventField.Action outputEq.symm) PUnit.unit) state.config.store =
      some ((PMF.pure true).map (cast (congrArg EventField.Value outputEq.symm)))) :
    environmentStep (runtime setup) state (.executeSample event) =
      PMF.pure (state.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventField.Value outputEq.symm) true)) := by
  rw [environmentStep_executeSample_eq (runtime setup) state event ready BaseTy.bool law
    outputEq codeEq
    (nodeView_eq_sample outputEq codeEq),
    state.config.step_eq_map_of_eval event ready _ _ evaluated,
    PMF.pure_map, PMF.pure_map, PMF.pure_map]
  rfl

theorem first_control_initial (players : Player → app.Policy) :
    app.controlStep (initialLaw setup) horizon scheduler players none =
      PMF.pure (some ⟨10, none, firstInitialExecution⟩) := by
  change ((PMF.pure sourceInitial).map _).map _ = _
  rw [PMF.pure_map, PMF.pure_map]
  rfl

theorem first_control_sample0 (players : Player → app.Policy) :
    app.controlStep (initialLaw setup) horizon scheduler players
      (some ⟨10, none, firstInitialExecution⟩) =
      PMF.pure (some ⟨9, none, firstSample0Execution⟩) := by
  have sampled := first_sample_environment firstInitialState sample0 firstSample0Ready rfl
    (compilePublicDist (ContextRefs.initial setup.context (outputLayout setup.program))
      (.weighted (.pure true))) rfl (by
        simp only [PMF.pure_map]
        change some (RationalLaw.pure true).denote = some (PMF.pure true)
        exact congrArg some (RationalLaw.denote_pure true))
  change ((PMF.pure (.application (.executeSample sample0) : app.Command)).bind _ ) = _
  rw [PMF.pure_bind]
  change (((environmentStep (runtime setup) firstInitialState
    (.executeSample sample0)).map _).map _).map _ = _
  rw [sampled, PMF.pure_map, PMF.pure_map, PMF.pure_map]
  rfl

theorem first_control_sample1 (players : Player → app.Policy) :
    app.controlStep (initialLaw setup) horizon scheduler players
      (some ⟨9, none, firstSample0Execution⟩) =
      PMF.pure (some ⟨8, none, firstSample1Execution⟩) := by
  have sampled := first_sample_environment firstSample0State sample1 firstSample1Ready rfl
    (compilePublicDist (ContextRefs.cons (name := 1) (cell := .publicData BaseTy.bool)
      ((outputEmbedding setup.program).ref sample0)
      (ContextRefs.initial setup.context (outputLayout setup.program)))
        (.weighted (.pure true))) rfl (by
          simp only [PMF.pure_map]
          change some (RationalLaw.pure true).denote = some (PMF.pure true)
          exact congrArg some (RationalLaw.denote_pure true))
  change ((PMF.pure (.application (.executeSample sample1) : app.Command)).bind _) = _
  rw [PMF.pure_bind]
  change (((environmentStep (runtime setup) firstSample0State
    (.executeSample sample1)).map _).map _).map _ = _
  rw [sampled, PMF.pure_map, PMF.pure_map, PMF.pure_map]
  rfl

theorem first_control_activation (players : Player → app.Policy) :
    app.controlStep (initialLaw setup) horizon scheduler players
      (some ⟨8, none, firstSample1Execution⟩) =
      PMF.pure (some ⟨7, some owner, firstExecution⟩) := by
  change ((PMF.pure (.activate owner : app.Command)).bind _) = _
  rw [PMF.pure_bind]
  change (((PMF.pure ∅).map _).map _).map _ = _
  simp only [PMF.pure_map]
  simp only [MessageNetwork.learn_empty]
  rfl

theorem first_native_prefix (bounds : MessageBounds nativeGraph)
    (profile : ∀ who, (nativeModel bounds).BehavioralPolicy who) :
    ((nativeModel bounds).runBehavioral profile 4).map ExecutionProtocol.History.state =
      PMF.pure (some ⟨7, some owner, firstExecution⟩) := by
  change (((nativeModel bounds).runBehavioralFrom profile 4
    ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).map
      ExecutionProtocol.History.state) = _
  rw [(nativeMenu bounds).run_map_controlStep (initialLaw setup) horizon scheduler profile 4]
  let players := (nativeMenu bounds).decodeProfile (initialLaw setup) horizon scheduler profile
  change ((((PMF.pure none).bind
    (app.controlStep (initialLaw setup) horizon scheduler players)).bind
    (app.controlStep (initialLaw setup) horizon scheduler players)).bind
      (app.controlStep (initialLaw setup) horizon scheduler players)).bind
        (app.controlStep (initialLaw setup) horizon scheduler players) = _
  rw [PMF.pure_bind, first_control_initial, PMF.pure_bind, first_control_sample0, PMF.pure_bind,
    first_control_sample1, PMF.pure_bind, first_control_activation]

/-- Every legal native first-activation history has this actual initialized
state, independently of the profile subsequently used to evaluate it. -/
theorem first_native_history_state (bounds : MessageBounds nativeGraph)
    (history : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).History)
    (control : app.Control) (current : history.state = some control)
    (active : control.actor = some owner)
    (position : control.execution.environmentRecall.length = 3) :
    history.state = some ⟨7, some owner, firstExecution⟩ := by
  rcases history with ⟨state, originalTrace⟩
  cases current
  let history : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).History :=
    ⟨some control, originalTrace⟩
  let trace : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) := history.trace
  let rawTrace := (nativeMenu bounds).toRawTrace (initialLaw setup) horizon scheduler trace
  have phase := phase_history rawTrace
  have recalled : (control.execution.recall owner).length = 0 := by
    have count := phase.recallCount
    rw [position, active] at count
    exact count
  have length := app.trace_length_of_control (initialLaw setup) horizon scheduler control rawTrace
  have rawLength : rawTrace.length = history.trace.length := by
    dsimp only [rawTrace]
    rw [(nativeMenu bounds).toRawTrace_length]
  rw [rawLength] at length
  have nativeLength : history.trace.length = 4 := by
    rw [position, Fin.sum_univ_one, recalled] at length
    exact length
  let assessment := (nativeMenu bounds).uniformAssessment (initialLaw setup) horizon scheduler
  have mixed := (nativeMenu bounds).uniform_fullyMixed (initialLaw setup) horizon scheduler
  have supported := mixed.history_supported history.trace
  rw [nativeLength] at supported
  have stateSupported : history.state ∈
      (((nativeModel bounds).runBehavioral assessment.strategy 4).map
        ExecutionProtocol.History.state).support := by
    rw [PMF.support_map]
    exact Set.mem_image_of_mem _ supported
  rw [first_native_prefix] at stateSupported
  exact (PMF.mem_support_pure_iff _ _).mp stateSupported


def firstCandidate : Handle nativeGraph := ⟨owner, .initial ⟨0, by decide⟩⟩

theorem first_resolution_ready : firstExecution.application.config.cut.Ready resolution := by
  decide

theorem first_resolution_turn :
    (firstExecution.observe app owner).application.publicView.ownTurn? owner = some resolution :=
  ownTurn?_of_ready setup firstExecution.application first_resolution_ready resolution_actor

theorem first_resolution_fits :
    (firstExecution.observe app owner).application.publicView.InclusionFitsDeadline
      (runtime setup) bound resolution := by
  change 0 - 0 + 2 < 3
  decide

theorem first_risk_clear : (runtime setup).serviceRisk leaks bound owner
    (firstExecution.recall owner) (firstExecution.observe app owner) = false := by
  apply (runtime setup).serviceRisk_clear
  · change ((firstExecution.application.publicView.missedDecisionBy owner || false) || false) =
      false
    rfl
  · exact (runtime setup).firstUnprotectedOpportunity_protected leaks bound owner _ _ resolution
      first_resolution_turn first_resolution_fits

theorem first_canonical_response (disclose : Bool) :
    (runtime setup).canonicalServiceDecision leaks owner (firstExecution.recall owner)
      (firstExecution.observe app owner) resolution disclose =
        lateResponse firstCandidate disclose := by
  cases disclose
  · exact (runtime setup).canonicalServiceDecision_resolution_false leaks owner _ _ resolution
      owner .bool initialBinding [] resolution_output resolution_code resolution_node
  · have opening : reactiveResolutionPacket owner resolution .bool initialBinding []
        resolution_output true (firstExecution.observe app owner).application =
        .opening resolution firstCandidate ⟨.bool, true⟩ := by
      rfl
    have verified : (firstExecution.observe app owner).application.candidates firstCandidate.2 =
        .openable ⟨.bool, true⟩ := by rfl
    simp only [canonicalServiceDecision, canonicalReactiveDecision, resolution_node, opening,
      disclosureSubmission_normalize_opening owner _ resolution firstCandidate ⟨.bool, true⟩
        rfl verified]
    simp only [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
      WitnessedSubmission.normalizeReactive, Submission.normalizeReactive_none,
      disclosureSubmission]
    rfl

theorem first_native_response_cases (bounds : MessageBounds nativeGraph) (response : app.Action)
    (available : response ∈ (nativeMenu bounds).actions owner (firstExecution.recall owner)
      (firstExecution.observe app owner)) :
    response = ⟨none⟩ ∨ ∃ disclose : Bool, response = lateResponse firstCandidate disclose := by
  change response ∈ bounds.riskActions (runtime setup) leaks bound owner _ _ at available
  rw [bounds.riskActions_of_clear _ _ _ _ _ _ first_risk_clear] at available
  rcases bounds.canonicalActions_cases (runtime setup) leaks owner _ _ response available with
    waited | ⟨event, choice, turn, _, _, _, _, _, same⟩
  · exact Or.inl waited
  · have eq : event = resolution := Option.some.inj (turn.symm.trans first_resolution_turn)
    subst event
    change Bool at choice
    exact Or.inr ⟨choice, same.trans (first_canonical_response choice)⟩


theorem first_response_available (bounds : MessageBounds nativeGraph)
    (covers : (⟨BaseTy.bool, true⟩ : Raw simpleExpr) ∈ bounds.values) (disclose : Bool) :
    lateResponse firstCandidate disclose ∈ (nativeMenu bounds).actions owner
      (firstExecution.recall owner) (firstExecution.observe app owner) := by
  apply bounds.canonicalActions_subset_risk
  rw [← first_canonical_response disclose]
  apply bounds.canonical_resolution_retained (runtime setup) leaks owner _ _ resolution owner
    .bool initialBinding [] resolution_output resolution_code resolution_node first_resolution_turn
    resolution_actor ((firstExecution.application.publicView_eventReady resolution).mpr
      first_resolution_ready) (by change 0 - 0 < 3; decide) rfl disclose
  cases disclose
  · change True
    trivial
  · change True ∧ (⟨BaseTy.bool, true⟩ : Raw simpleExpr) ∈ bounds.values
    exact ⟨trivial, covers⟩

theorem first_information_resources (bounds : MessageBounds nativeGraph)
    (history : (nativeModel bounds).InformationHistory owner
      (some (firstExecution.recall owner, firstExecution.observe app owner))) :
    history.1.state = some ⟨7, some owner, firstExecution⟩ := by
  have observed := ((nativeMenu bounds).info (initialLaw setup) horizon scheduler owner
    history.1.trace).symm.trans history.2
  cases current : history.1.state with
  | none => simp [current, ReactiveApplication.observe] at observed
  | some control =>
      rw [current] at observed
      change (if control.actor = some owner then
        some (control.execution.recall owner, control.execution.observe app owner) else none) = _
        at observed
      split at observed
      · rename_i active
        have same := Option.some.inj observed
        have actualClock := congrArg (fun info : List app.PlayerEntry × app.PlayerView =>
          info.2.application.publicView.clock) same
        change control.execution.application.clock = 0 at actualClock
        have traced : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).Trace
            (some control) := current ▸ history.1.trace
        have phase := phase_history
          ((nativeMenu bounds).toRawTrace (initialLaw setup) horizon scheduler traced)
        have position : control.execution.environmentRecall.length = 3 := by
          rcases phase.activation (by rw [active]; rfl) with first | second
          · exact first
          · have clock := phase.clock
            rw [second] at clock
            change control.execution.application.clock = 1 at clock
            omega
        exact current.symm.trans
          (first_native_history_state bounds history.1 control current active position)
      · cases observed

theorem first_decision_site (bounds : MessageBounds nativeGraph) :
    (nativeModel bounds).IsDecisionInfo owner
      (some (firstExecution.recall owner, firstExecution.observe app owner)) := by
  let assessment := (nativeMenu bounds).uniformAssessment (initialLaw setup) horizon scheduler
  obtain ⟨history, supported⟩ :=
    ((nativeModel bounds).runBehavioral assessment.strategy 4).support_nonempty
  have mapped : history.state ∈ (((nativeModel bounds).runBehavioral assessment.strategy 4).map
      ExecutionProtocol.History.state).support := by
    rw [PMF.support_map]
    exact Set.mem_image_of_mem _ supported
  rw [first_native_prefix] at mapped
  have current := (PMF.mem_support_pure_iff _ _).mp mapped
  refine ⟨⟨history, ?_⟩, ?_, ⟨none⟩, ?_⟩
  · change ((nativeMenu bounds).signals (initialLaw setup) horizon scheduler).infoOf
      owner history.trace = _
    rw [(nativeMenu bounds).info (initialLaw setup) horizon scheduler owner history.trace, current]
    rfl
  · rw [current]
    change ¬ (7 = 0 ∧ (some owner : Option Player) = none)
    simp
  · exact ⟨⟨none⟩, silence_risk bounds owner _ _, rfl⟩

def firstSite (bounds : MessageBounds nativeGraph) : (nativeModel bounds).InformationSite owner :=
  ⟨some (firstExecution.recall owner, firstExecution.observe app owner), first_decision_site bounds⟩

end Vegas.LateResolutionService
