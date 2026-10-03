/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstActivationResources
import Vegas.Game.SourceServiceRecordedResolutionTraffic
import Vegas.Game.SourceServiceResolutionDecisionFactorization

/-! # Traffic before the first protected resolution response

The actual owner input and canonical call are derived from initialized
first-turn play. Public commands before that response and silent completion
after it retain the same full traffic channel.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

private theorem first_resolution_activation
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event =
      .resolve owner payload binding checks outputEq codeEq)
    (execution middle : (application setup leaks).Execution)
    (within : execution.environmentRecall.length < horizon)
    (initialized : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup)
      scheduler (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
        profile) execution.environmentRecall.length).support)
    (ready : execution.application.config.cut.Ready event)
    (absent : sourceServiceTurnInput? setup leaks owner event (execution.recall owner) = none)
    (selected : .activate owner ∈ (scheduler execution.environmentRecall
      (execution.observeEnvironment (application setup leaks))).support)
    (observed : middle ∈ (execution.environmentStep (application setup leaks)
      (.activate owner)).support)
    (disclose : Bool) :
    let response := (runtime setup).canonicalServiceDecision leaks owner (middle.recall owner)
      (middle.observe (application setup leaks) owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
    decidedProfile (leaks := leaks) bound owner event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) owner
        (middle.recall owner) (middle.observe (application setup leaks) owner) = PMF.pure response ∧
      (runtime setup).eventRecorded leaks
        ((middle.respond (application setup leaks) owner response).recall owner) event = true ∧
      FreshCallsConform setup leaks (middle.respond (application setup leaks) owner response)
        owner ∧
      Nonempty (((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨horizon - execution.environmentRecall.length - 1, none,
          middle.respond (application setup leaks) owner response⟩)) := by
  intro response
  let app := application setup leaks
  have owned := nodeView_resolve_actor outputEq codeEq
  obtain ⟨⟨middleTrace⟩, turn, first, fits, _atTurn, _slots, unrecorded, fresh, conform⟩ :=
    sourceServiceFirstActivation_resources setup leaks contract timely turns profile owner event
      owned execution middle within initialized ready absent selected observed
  have notBind who ty output code
      (impossible : nodeView (graph setup) event = .bind who ty output code) : False := by
    rw [node] at impossible
    cases impossible
  have nonempty : response.transmission ≠ none := by
    dsimp only [response]
    rw [(runtime setup).canonicalServiceDecision_eq_of_not_bind leaks owner _ _ event _ notBind]
    rcases (runtime setup).serviceDecision_resolution_cases leaks owner (middle.recall owner)
        (middle.observe app owner) event owner payload binding checks outputEq codeEq node
        disclose with withheld | ⟨candidate, value, evidence, _disclose, _owner, _ready, sent⟩
    · rw [withheld]
      exact Option.some_ne_none _
    · rw [sent]
      exact Option.some_ne_none _
  have named : (runtime setup).submittedEvent? leaks response = some event := by
    rcases (runtime setup).canonicalServiceDecision_cases leaks owner (middle.recall owner)
      (middle.observe app owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) with silent | addressed
    · exact (nonempty (congrArg ReactiveApplication.Action.transmission silent)).elim
    · exact addressed
  refine ⟨?_, (runtime setup).eventRecorded_respond leaks middle owner response event named,
    ?_, app.raw_trace_respond (initialLaw setup) horizon scheduler _ middle owner response
      middleTrace⟩
  · simp only [decidedProfile, Function.update_self, decidedTurnPolicy]
    rw [app.turnScheduledPolicy_selected _ (0 : Fin 1) _ _ _ _ first]
    simp only [decidedOpportunity, unrecorded, Bool.false_eq_true, ↓reduceIte]
    have fitsView : (middle.observe app owner).application.publicView.InclusionFitsDeadline
        (runtime setup) bound event := fits
    change (if _ then if response.transmission = none then _ else PMF.pure response else _) = _
    rw [ite_eq_left fitsView, ite_eq_right nonempty]
  · cases transmitted : response.transmission with
    | none => exact (nonempty transmitted).elim
    | some material =>
        have responseEq : response = ⟨some material⟩ := by
          rcases response with ⟨transmission⟩
          change transmission = some material at transmitted
          rw [transmitted]
        have canonical := canonicalServiceDecision_freshServiceEnvelope middleTrace event turn
          fits.withinDeadline fresh
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) material transmitted
        rw [responseEq]
        have recalled := respond_submit_recall middle owner material
        intro entry member other message submits emitted
        rw [recalled] at member
        rcases List.mem_append.mp member with old | recent
        · exact conform entry old other message submits emitted
        · rw [List.mem_singleton] at recent
          subst entry
          cases Option.some.inj submits
          cases Option.some.inj emitted
          exact canonical

private theorem decided_recorded_silent
    (bound : (graph setup).EventId → Nat) (owner : Player) (event : (graph setup).EventId)
    (action : (graph setup).Action event) (execution : (application setup leaks).Execution)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true)
    (who : Player) :
    decidedProfile (leaks := leaks) bound owner event action who (execution.recall who)
        (execution.observe (application setup leaks) who) =
      (application setup leaks).silentPolicy (execution.recall who)
        (execution.observe (application setup leaks) who) := by
  by_cases own : who = owner
  · subst who
    simp only [decidedProfile, Function.update_self, decidedTurnPolicy,
      ReactiveApplication.turnScheduledPolicy]
    split
    · simp only [decidedOpportunity, recorded, ↓reduceIte]
    · rfl
  · simp only [decidedProfile, Function.update_of_ne own]

private theorem decided_recorded_runUntil
    (scheduler : (application setup leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (owner : Player) (event : (graph setup).EventId)
    (action : (graph setup).Action event) (execution : (application setup leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true)
    (count : Nat) :
    (application setup leaks).runUntil scheduler
        (decidedProfile (leaks := leaks) bound owner event action)
        (fun final => event ∈ final.application.config.cut.completed) count execution =
      (application setup leaks).runUntil scheduler
        (fun _ => (application setup leaks).silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) count execution := by
  exact sourceServicePolicy_runUntil_of_recorded setup leaks scheduler _ count execution owner
    event ready recorded (fun current _ currentRecorded who =>
      decided_recorded_silent setup leaks bound owner event action current currentRecorded who)

private theorem first_nonhit_config
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (execution next : (application setup leaks).Execution)
    (within : next.environmentRecall.length ≤ horizon)
    (initialized : next ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      next.environmentRecall.length).support)
    (ready : execution.application.config.cut.Ready event)
    (moved : next ∈ ((application setup leaks).round scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      execution).support)
    (absent : sourceServiceTurnInput? setup leaks owner event (next.recall owner) = none) :
    next.application.config = execution.application.config := by
  let players := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
    profile
  rcases round_configStep setup leaks scheduler players execution next moved with
    same | ⟨target, targetReady, action, completed⟩
  · exact same
  · have targetEq := setup.eventGraph.sequentialize_ready_unique execution.application.config.cut
      targetReady ready
    subst target
    have finished : event ∈ next.application.config.cut.completed := by
      rw [execution.application.config.step_cut event ready action next.application.config
        completed, EventOrder.Cut.mem_complete]
      exact Or.inl rfl
    exact (sourceServiceFirstTurn_completed_input contract timely players owner turns profile rfl
      _ within next initialized event owned finished absent).elim

/-- A fixed effective resolution choice retains its complete traffic channel
through the first actual owner response and completion. All operational call
resources are derived from initialized first-turn prefixes. The source-store
agreement and equal effective successor views are the local compiler inputs. -/
theorem sourceServiceFirstResolution_decided_traffic_runUntil
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (refs : ContextRefs (graph setup).layout Γ) (leftSource rightSource : Config Player L Γ)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (focal : Player) (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (leftCode : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs leftSource.registry leftSource.revelations
          binding))
    (rightCode : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs rightSource.registry rightSource.revelations
          binding))
    (leftNode : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs leftSource.registry leftSource.revelations
        binding) outputEq leftCode)
    (rightNode : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs rightSource.registry rightSource.revelations
        binding) outputEq rightCode)
    (first second : Bool)
    (leftEffective : first = false ∨ ∃ value : L.Val payload,
      first = true ∧ disclosureResult published binding leftSource true = .success value)
    (rightEffective : second = false ∨ ∃ value : L.Val payload,
      second = true ∧ disclosureResult published binding rightSource true = .success value)
    (visible : (revealSuccessor published binding leftSource first).view focal =
      (revealSuccessor published binding rightSource second).view focal)
    (count : Nat) (left right : (application setup leaks).Execution)
    (leftAgrees : refs.Agrees leftSource.state left.application.config.store)
    (rightAgrees : refs.Agrees rightSource.state right.application.config.store)
    (within : left.environmentRecall.length + count ≤ horizon)
    (leftInitialized : left ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      left.environmentRecall.length).support)
    (rightInitialized : right ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      right.environmentRecall.length).support)
    (ready : left.application.config.cut.Ready event)
    (leftAbsent : sourceServiceTurnInput? setup leaks owner event (left.recall owner) = none)
    (rightAbsent : sourceServiceTurnInput? setup leaks owner event (right.recall owner) = none)
    (same : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right) :
    ((application setup leaks).runUntil scheduler
        (decidedProfile (leaks := leaks) bound owner event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) first))
        (fun final => event ∈ final.application.config.cut.completed) count left).map
          ((runtime setup).bindingTraffic leaks focal) =
      ((application setup leaks).runUntil scheduler
        (decidedProfile (leaks := leaks) bound owner event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) second))
        (fun final => event ∈ final.application.config.cut.completed) count right).map
          ((runtime setup).bindingTraffic leaks focal) := by
  classical
  let app := application setup leaks
  let players := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
    profile
  have owned := nodeView_resolve_actor outputEq leftCode
  induction count generalizing left right with
  | zero =>
      simpa only [ReactiveApplication.runUntil, PMF.pure_map] using congrArg PMF.pure same
  | succ count ih =>
      have networks := congrArg Prod.fst same
      have receipts := congrArg (fun traffic => traffic.2.1) same
      have environments := congrArg (fun traffic => traffic.2.2.1) same
      have publics := congrArg (fun traffic => traffic.2.2.2.2.2) same
      dsimp only [bindingTraffic] at networks receipts environments publics
      have environment : left.observeEnvironment app = right.observeEnvironment app := by
        change ReactiveApplication.EnvironmentView.mk left.network.publicView
          left.application.publicView left.receipts = _
        rw [networks, publics, receipts]
        rfl
      have rightReady : right.application.config.cut.Ready event := by
        apply (right.application.publicView_eventReady event).mp
        rw [← publics]
        exact (left.application.publicView_eventReady event).mpr ready
      obtain ⟨leftTrace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
        left.environmentRecall.length (by omega) left leftInitialized
      obtain ⟨rightTrace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
        right.environmentRecall.length (by rw [← environments]; omega) right rightInitialized
      have leftConform : FreshCallsConform setup leaks left owner := by
        intro entry member material message submitted emitted
        exact sourceServiceTurnPolicy_freshServiceEnvelope scheduler players owner
          (firstTurnTiming setup turns) profile rfl _ left leftInitialized entry member material
          submitted message emitted
      have leftRunning := ready.1
      have rightRunning := rightReady.1
      simp only [ReactiveApplication.runUntil, leftRunning, rightRunning, ↓reduceIte,
        PMF.map_bind, ReactiveApplication.round, PMF.bind_bind]
      rw [← environments, ← environment]
      apply bind_congr_on_support _
      intro command selected
      by_cases current : command = .activate owner
      · subst command
        have rightSelected : .activate owner ∈
            (scheduler right.environmentRecall (right.observeEnvironment app)).support := by
          rw [← environments, ← environment]
          exact selected
        simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.activation_samples,
          PMF.bind_map, PMF.bind_bind, Function.comp_def]
        rw [← networks]
        apply bind_congr_on_support _
        intro sample sampled
        let firstMiddle := left.sampledActivation app owner sample
        let secondMiddle := right.sampledActivation app owner sample
        have leftObserved : firstMiddle ∈ (left.environmentStep app (.activate owner)).support :=
          by rw [ReactiveApplication.Execution.activation_samples, PMF.support_map]
             exact ⟨sample, sampled, rfl⟩
        have rightObserved : secondMiddle ∈
            (right.environmentStep app (.activate owner)).support := by
          rw [ReactiveApplication.Execution.activation_samples, PMF.support_map, ← networks]
          exact ⟨sample, sampled, rfl⟩
        obtain ⟨leftPolicy, firstRecorded, firstConform, ⟨firstTrace⟩⟩ :=
          first_resolution_activation setup leaks contract timely turns profile owner event payload
            (refs.get binding) _ outputEq leftCode leftNode left firstMiddle (by omega)
            leftInitialized ready leftAbsent selected leftObserved first
        obtain ⟨rightPolicy, secondRecorded, _secondConform, ⟨secondTrace⟩⟩ :=
          first_resolution_activation setup leaks contract timely turns profile owner event payload
            (refs.get binding) _ outputEq rightCode rightNode right secondMiddle
            (by rw [← environments]; omega) rightInitialized rightReady rightAbsent rightSelected
              rightObserved second
        let firstResponse := (runtime setup).canonicalServiceDecision leaks owner
          (firstMiddle.recall owner) (firstMiddle.observe app owner) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) first)
        let secondResponse := (runtime setup).canonicalServiceDecision leaks owner
          (secondMiddle.recall owner) (secondMiddle.observe app owner) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) second)
        let firstNext := firstMiddle.respond app owner firstResponse
        let secondNext := secondMiddle.respond app owner secondResponse
        have firstReady : firstNext.application.config.cut.Ready event := by
          rw [((runtime setup).reactive_respond_application leaks firstMiddle owner _).1,
            activation_application setup leaks left firstMiddle owner leftObserved]
          exact ready
        have secondReady : secondNext.application.config.cut.Ready event := by
          rw [((runtime setup).reactive_respond_application leaks secondMiddle owner _).1,
            activation_application setup leaks right secondMiddle owner rightObserved]
          exact rightReady
        obtain ⟨firstMiddleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
          (horizon - left.environmentRecall.length - 1) left firstMiddle (.activate owner)
          (by
            convert leftTrace using 1
            congr 2
            omega) selected leftObserved
        obtain ⟨secondMiddleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
          (horizon - right.environmentRecall.length - 1) right secondMiddle (.activate owner)
          (by
            convert rightTrace using 1
            congr 2
            rw [← environments]
            omega)
          rightSelected rightObserved
        have firstFacts := legalFacts setup leaks horizon scheduler _ firstMiddleTrace
        have secondFacts := legalFacts setup leaks horizon scheduler _ secondMiddleTrace
        have firstAgrees : refs.Agrees leftSource.state firstMiddle.application.config.store := by
          rw [activation_application setup leaks left firstMiddle owner leftObserved]
          exact leftAgrees
        have secondAgrees : refs.Agrees rightSource.state secondMiddle.application.config.store :=
            by
          rw [activation_application setup leaks right secondMiddle owner rightObserved]
          exact rightAgrees
        have middleTraffic := (runtime setup).bindingTraffic_activation leaks left right focal
          owner same sample
        have submittedTraffic : (runtime setup).bindingTraffic leaks focal firstNext =
            (runtime setup).bindingTraffic leaks focal secondNext :=
          source_resolution_decision_traffic_congr setup leaks published binding refs leftSource
            rightSource firstMiddle secondMiddle firstAgrees secondAgrees firstFacts.binding
            secondFacts.binding firstFacts.inputs secondFacts.inputs event focal outputEq leftCode
            rightCode leftNode rightNode first second leftEffective rightEffective visible
            middleTraffic
        dsimp only [firstMiddle, secondMiddle, app] at leftPolicy rightPolicy
        simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
          ReactiveApplication.invoke, leftPolicy, rightPolicy, PMF.pure_map, PMF.pure_bind]
        rw [decided_recorded_runUntil setup leaks scheduler bound owner event _ firstNext
          firstReady firstRecorded count,
          decided_recorded_runUntil setup leaks scheduler bound owner event _ secondNext
            secondReady secondRecorded count]
        exact source_resolution_conforming_silent_runUntil setup leaks firstTrace secondTrace
          firstConform firstReady payload (refs.get binding) _ outputEq leftCode leftNode focal
          submittedTraffic count (by omega) (by rw [← environments]; omega)
      · have leftSilent := sourceServiceFirstTurn_nonowner_dispatch setup leaks bound turns
          profile owner event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) first) left ready owned
          command current
        have rightSilent := sourceServiceFirstTurn_nonowner_dispatch setup leaks bound turns
          profile owner event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) second) right rightReady owned
            command current
        rw [leftSilent.2, rightSilent.2]
        have dispatches := source_resolution_conforming_silent_dispatch setup leaks leftTrace
          rightTrace leftConform ready payload (refs.get binding) _ outputEq leftCode leftNode focal
          same command
        apply bind_eq_of_map_eq _ _ _ _ dispatches
        intro nextLeft leftMoved nextRight rightMoved nextSame
        have leftDispatch : nextLeft ∈ (app.dispatch players command left).support := by
          rw [← leftSilent.1, leftSilent.2]
          exact leftMoved
        have rightDispatch : nextRight ∈ (app.dispatch players command right).support := by
          rw [← rightSilent.1, rightSilent.2]
          exact rightMoved
        have leftActual : nextLeft ∈ (app.round scheduler players left).support := by
          rw [ReactiveApplication.round, PMF.support_bind]
          exact Set.mem_iUnion₂.mpr ⟨command, selected, leftDispatch⟩
        have rightSelected : command ∈
            (scheduler right.environmentRecall (right.observeEnvironment app)).support := by
          rw [← environments, ← environment]
          exact selected
        have rightActual : nextRight ∈ (app.round scheduler players right).support := by
          rw [ReactiveApplication.round, PMF.support_bind]
          exact Set.mem_iUnion₂.mpr ⟨command, rightSelected, rightDispatch⟩
        have leftLength := app.round_environmentRecall_length scheduler players left nextLeft
          leftActual
        have rightLength := app.round_environmentRecall_length scheduler players right nextRight
          rightActual
        have leftNextInitialized : nextLeft ∈ (app.roundsFrom (initialLaw setup) scheduler players
            nextLeft.environmentRecall.length).support := by
          rw [leftLength, app.roundsFrom_succ, PMF.support_bind]
          exact Set.mem_iUnion₂.mpr ⟨left, leftInitialized, leftActual⟩
        have rightNextInitialized : nextRight ∈ (app.roundsFrom (initialLaw setup) scheduler players
            nextRight.environmentRecall.length).support := by
          rw [rightLength, app.roundsFrom_succ, PMF.support_bind]
          exact Set.mem_iUnion₂.mpr ⟨right, rightInitialized, rightActual⟩
        have leftNextAbsent := sourceServiceTurnInput_nonowner_dispatch setup leaks players
          owner event left nextLeft command current leftAbsent leftDispatch
        have rightNextAbsent := sourceServiceTurnInput_nonowner_dispatch setup leaks players
          owner event right nextRight command current rightAbsent rightDispatch
        have leftConfig := first_nonhit_config setup leaks contract timely turns profile owner
          event owned left nextLeft (by omega) leftNextInitialized ready leftActual leftNextAbsent
        have rightConfig := first_nonhit_config setup leaks contract timely turns profile owner
          event owned right nextRight (by rw [rightLength, ← environments]; omega)
          rightNextInitialized rightReady rightActual rightNextAbsent
        exact ih nextLeft nextRight (by rw [leftConfig]; exact leftAgrees)
          (by rw [rightConfig]; exact rightAgrees) (by omega) leftNextInitialized
          rightNextInitialized (by rw [leftConfig]; exact ready) leftNextAbsent rightNextAbsent
          nextSame

/-- Untouched initialized completion boundaries have no earlier owner input.
Thus their real remaining horizon supplies the entire fixed-choice traffic
coupling, including actual owner activation and delayed inclusion. -/
theorem sourceServiceFirstResolution_decided_traffic
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (refs : ContextRefs (graph setup).layout Γ) (leftSource rightSource : Config Player L Γ)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (focal : Player) (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (leftCode : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs leftSource.registry leftSource.revelations
          binding))
    (rightCode : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs rightSource.registry rightSource.revelations
          binding))
    (leftNode : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs leftSource.registry leftSource.revelations
        binding) outputEq leftCode)
    (rightNode : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs rightSource.registry rightSource.revelations
        binding) outputEq rightCode)
    (first second : Bool)
    (leftEffective : first = false ∨ ∃ value : L.Val payload,
      first = true ∧ disclosureResult published binding leftSource true = .success value)
    (rightEffective : second = false ∨ ∃ value : L.Val payload,
      second = true ∧ disclosureResult published binding rightSource true = .success value)
    (visible : (revealSuccessor published binding leftSource first).view focal =
      (revealSuccessor published binding rightSource second).view focal)
    (left right : (application setup leaks).Execution)
    (leftAgrees : refs.Agrees leftSource.state left.application.config.store)
    (rightAgrees : refs.Agrees rightSource.state right.application.config.store)
    (leftBoundary : CompletionBoundary setup leaks scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      event.val left)
    (rightBoundary : CompletionBoundary setup leaks scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      event.val right)
    (within : left.environmentRecall.length ≤ horizon)
    (same : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right) :
    ((application setup leaks).runUntilHorizon scheduler
      (decidedProfile (leaks := leaks) bound owner event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) first))
      (fun final => event ∈ final.application.config.cut.completed) horizon left).map
        ((runtime setup).bindingTraffic leaks focal) =
    ((application setup leaks).runUntilHorizon scheduler
      (decidedProfile (leaks := leaks) bound owner event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) second))
      (fun final => event ∈ final.application.config.cut.completed) horizon right).map
        ((runtime setup).bindingTraffic leaks focal) := by
  have environments := congrArg (fun traffic => traffic.2.2.1) same
  dsimp only [bindingTraffic] at environments
  unfold ReactiveApplication.runUntilHorizon
  rw [← environments]
  apply sourceServiceFirstResolution_decided_traffic_runUntil setup leaks published binding refs
    leftSource rightSource contract timely turns profile focal event outputEq leftCode rightCode
    leftNode rightNode first second leftEffective rightEffective visible _ left right leftAgrees
    rightAgrees (by omega) leftBoundary.supported rightBoundary.supported
    ((ready_iff_rank setup _ event.val leftBoundary.ordered event).mpr rfl)
  · apply (sourceServiceTurnInput?_eq_none_iff owner event _).mpr
    intro entry member turn
    exact leftBoundary.untouched event rfl owner entry member
      ((PublicView.ownTurn?_spec _ owner event turn).1)
  · apply (sourceServiceTurnInput?_eq_none_iff owner event _).mpr
    intro entry member turn
    exact rightBoundary.untouched event rfl owner entry member
      ((PublicView.ownTurn?_spec _ owner event turn).1)
  · exact same

/-- An original intention and a parameter are carried unchanged with the
effective decision through its whole actual asynchronous phase. Only the prior
source-pair traffic factorization is an induction hypothesis. Its next traffic channel
is proved from actual protected response and completion coupling. -/
theorem sourceServiceFirstResolution_intention_factorization
    {Seed Parameter : Type*} {Γ : SourceCtx Player L} {name : VarId} {owner : Player}
    {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (refs : ContextRefs (graph setup).layout Γ)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (focal : Player) (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (prior : PMF Seed) (parameter : Seed → Parameter) (source original : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (agree : ∀ seed ∈ prior.support,
      refs.Agrees (source seed).state (execution seed).application.config.store)
    (codeEq : ∀ seed ∈ prior.support,
      cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs (source seed).registry
          (source seed).revelations binding))
    (node : ∀ seed (supported : seed ∈ prior.support),
      nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs (source seed).registry
        (source seed).revelations binding) outputEq (codeEq seed supported))
    (boundary : ∀ seed ∈ prior.support,
      CompletionBoundary setup leaks scheduler
        (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
        event.val (execution seed))
    (within : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (choice : Config Player L Γ → PMF Bool)
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => ((source seed, original seed, parameter seed),
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, original seed, parameter seed))).bind fun pair =>
        (noise (pair.1.view focal)).map fun extra => (pair, extra)) :
    ∃ nextNoise : DecisionView focal ((published, .publication payload) :: Γ) → PMF _,
      (prior.bind fun seed => (choice (original seed)).bind fun intended =>
        ((application setup leaks).runUntilHorizon scheduler
          (decidedProfile (leaks := leaks) bound owner event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm)
              (effectiveDisclosure published binding (source seed) intended)))
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            ((revealSuccessor published binding (source seed)
                (effectiveDisclosure published binding (source seed) intended),
              revealSuccessor published binding (original seed) intended, parameter seed),
                (runtime setup).bindingTraffic leaks focal final)) =
      ((prior.map (fun seed => (source seed, original seed, parameter seed))).bind fun pair =>
        (choice pair.2.1).map fun intended =>
          (revealSuccessor published binding pair.1
            (effectiveDisclosure published binding pair.1 intended),
            revealSuccessor published binding pair.2.1 intended, pair.2.2)).bind fun next =>
              (nextNoise (next.1.view focal)).map fun extra => (next, extra) := by
  have emittable (config : Config Player L Γ) (intended : Bool) :
      effectiveDisclosure published binding config intended = false ∨ ∃ value : L.Val payload,
        effectiveDisclosure published binding config intended = true ∧
          disclosureResult published binding config true = .success value := by
    cases intended with
    | false => exact Or.inl (effectiveDisclosure_false published binding config)
    | true =>
        cases result : disclosureResult published binding config true with
        | failure => exact Or.inl (by simp only [effectiveDisclosure, result])
        | success value =>
            exact Or.inr ⟨value, by simp only [effectiveDisclosure, result], rfl⟩
  obtain ⟨nextNoise, law⟩ := exists_updated_observation_kernel_of_readout prior
    (fun seed => (source seed, original seed, parameter seed))
    (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed))
    (fun pair => pair.1.view focal) noise factor (fun pair => choice pair.2.1)
    (fun pair intended =>
      (revealSuccessor published binding pair.1
        (effectiveDisclosure published binding pair.1 intended),
        revealSuccessor published binding pair.2.1 intended, pair.2.2))
      (fun pair => pair.1.view focal)
    (fun seed intended => ((application setup leaks).runUntilHorizon scheduler
      (decidedProfile (leaks := leaks) bound owner event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (effectiveDisclosure published binding (source seed) intended)))
      (fun final => event ∈ final.application.config.cut.completed) horizon
      (execution seed)).map ((runtime setup).bindingTraffic leaks focal))
    (by
      intro left _ first _ right _ second _ same
      exact reveal_view_reflects focal published binding left.1 right.1
        (effectiveDisclosure published binding left.1 first)
        (effectiveDisclosure published binding right.1 second) same)
    (by
      intro left leftSupport first _ right rightSupport second _ same traffic
      exact sourceServiceFirstResolution_decided_traffic setup leaks published binding refs
        (source left) (source right) contract timely turns profile focal event outputEq
        (codeEq left leftSupport) (codeEq right rightSupport)
        (node left leftSupport) (node right rightSupport)
        (effectiveDisclosure published binding (source left) first)
        (effectiveDisclosure published binding (source right) second)
        (emittable (source left) first) (emittable (source right) second) same
        (execution left) (execution right) (agree left leftSupport) (agree right rightSupport)
        (boundary left leftSupport) (boundary right rightSupport) (within left leftSupport) traffic)
  refine ⟨nextNoise, ?_⟩
  simpa only [PMF.map_comp, Function.comp_def] using law

end Vegas
