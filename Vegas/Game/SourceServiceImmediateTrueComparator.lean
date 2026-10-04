/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCommittedImmediateComparator
import Vegas.Game.SourceServiceProtectedDecisionCompletion
import Vegas.Game.SourceServiceWithholdingGuessBound
import Vegas.EventGraph.ResolutionProvenance
import Vegas.Game.SourceServiceResolutionResponseLaw
import Vegas.Game.SourceServiceRecordedResolutionAlignment

/-! # A protected TRUE comparator through its complete continuation

An actual compatible input fixes one operationally successful canonical TRUE
response. The same implementable immediate policy follows it. Protected receipt
and stored-value persistence give HIGH at the complete endpoint; authentic
partial sampling collects no owner charge. Foreign policies remain arbitrary.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory GameTheory.Math.Probability
  GameTheory.Enforcement GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
local notation "runtime" => runtime service.setup
local notation "menu" => service.bounds.menu (runtime) service.leaks

/-- The genuine normalized source support at this aligned residual contains
TRUE whenever its actual physical guard evaluation succeeds. No native or
source posterior is supplied. -/
theorem sourceCompatibleInfo_immediate_true_supported
    (profile : BehavioralProfile service.setup.program)
    (supports : ∀ who, (profile who).SupportsEffectiveChoices service.setup.program
      (CommitmentInterface.values service.setup.program) []
      (Revelations.initial service.setup.context))
    (remaining : Nat) (execution : (app).Execution)
    (event : (graph service.setup).EventId)
    (site : RevealSource service.setup profile event execution.application.config)
    (trace : ((app).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
      (some ⟨remaining, some site.owner, execution⟩))
    (compatible : service.sourceCompatibleInfo site.owner
      (some (execution.recall site.owner, execution.observe (app) site.owner)))
    (turn : execution.application.publicView.ownTurn? site.owner = some event)
    (unrecorded : (runtime).eventRecorded service.leaks
      (execution.recall site.owner) event = false)
    (value : L.Val site.payload)
    (successful : EventCode.resolveOutput? (site.refs.get site.binding)
      (compileChecks (published := site.published) site.refs site.source.registry
        site.source.revelations site.binding) true execution.application.config.store =
          some (.success value)) :
    (runtime).canonicalServiceDecision service.leaks site.owner (execution.recall site.owner)
      (execution.observe (app) site.owner) event
        (cast (congrArg EventField.Action site.outputEq.symm) true) ∈
      (sourceServiceImmediatePolicy service.setup service.leaks service.bound profile site.owner
        (execution.recall site.owner) (execution.observe (app) site.owner)).support := by
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ site.owner event turn).1
  obtain ⟨clear, _atTurn, _slots, _⟩ := service.sourceCompatibleInfo_raw_prefixFacts
    ⟨remaining, some site.owner, execution⟩ trace site.owner compatible
  have fits := (runtime).serviceRisk_clear_protected_opportunity service.leaks service.bound
    site.owner (execution.recall site.owner) (execution.observe (app) site.owner) event rfl
      turn unrecorded clear
  have result := compiled_disclosure_result (graph := graph service.setup) site.published
    site.binding site.source site.refs execution.application.config.store site.agree true
  rw [EventCode.resolveOutput?_playerStore, successful] at result
  have sourceSuccess : disclosureResult site.published site.binding site.source true =
      .success value := Option.some.inj result.symm
  have chosen : true ∈ (revealKernel site.residual (site.source.view site.owner)).support := by
    apply (site.supported supports site.owner).1 rfl (site.source.view site.owner) true
    change effectiveDisclosureView site.published site.binding site.source.registry
      site.source.revelations (sourceObserve site.owner site.source.state) true = true
    rw [effectiveDisclosureView_observe]
    simp only [effectiveDisclosure, sourceSuccess]
  rw [sourceServiceImmediatePolicy_at_event clear turn,
    sourceServiceCanonicalOpportunity_protected service.bound profile site.owner event
      (execution.recall site.owner) (execution.observe (app) site.owner) unrecorded fits,
    RevealSource.canonical_response_law execution site ready, PMF.support_map]
  exact ⟨true, chosen, rfl⟩

open Classical in
/-- Actual protected inclusion fixes this TRUE publication for the whole
physical immediate continuation and every authentic partial audit. -/
theorem sourceCompatibleInfo_immediate_true_finish
    (profile : BehavioralProfile service.setup.program) (who : Player)
    (remaining : Nat) (execution : (app).Execution)
    (trace : ((app).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (compatible : service.sourceCompatibleInfo who
      (some (execution.recall who, execution.observe (app) who)))
    (event : (graph service.setup).EventId) (payload : L.Ty)
    (binding : FieldRef (graph service.setup).layout (.binding who payload))
    (checks : List (GuardCheck (graph service.setup).layout payload))
    (outputEq : (graph service.setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph service.setup).layout) outputEq)
      ((graph service.setup).nodes event) = .resolve who payload binding checks)
    (node : nodeView (graph service.setup) event =
      .resolve who payload binding checks outputEq codeEq)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime).eventRecorded service.leaks (execution.recall who) event = false)
    (value : L.Val payload)
    (successful : EventCode.resolveOutput? binding checks true
      execution.application.config.store = some (.success value))
    (chosen : (runtime).canonicalServiceDecision service.leaks who (execution.recall who)
      (execution.observe (app) who) event
        (cast (congrArg EventField.Action outputEq.symm) true) ∈
      (sourceServiceImmediatePolicy service.setup service.leaks service.bound profile who
        (execution.recall who) (execution.observe (app) who)).support)
    (foreign : Player → (app).Policy) (final : (app).ProtocolState)
    (reached : final ∈ ((app).finish (initialLaw service.setup) service.horizon service.scheduler
      (Function.update foreign who (sourceServiceImmediatePolicy service.setup service.leaks
        service.bound profile who)) (some ⟨remaining, none, execution.respond (app) who
          ((runtime).canonicalServiceDecision service.leaks who (execution.recall who)
            (execution.observe (app) who) event
              (cast (congrArg EventField.Action outputEq.symm) true))⟩)).support)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    ∃ next : (app).Execution, final = (app).finished next ∧
      next.application.config.outputs event = some
        (cast (congrArg EventField.Value outputEq.symm) (.success value)) ∧
      TerminalAudit.charge ((runtime).serviceAuditObservation service.leaks)
        (sourceServiceAudit service.setup service.leaks sample) final who = 0 := by
  let players := Function.update foreign who
    (sourceServiceImmediatePolicy service.setup service.leaks service.bound profile who)
  have follows : players who = sourceServiceImmediatePolicy service.setup service.leaks
      service.bound profile who := Function.update_self ..
  let action : (graph service.setup).Action event :=
    cast (congrArg EventField.Action outputEq.symm) true
  let response := (runtime).canonicalServiceDecision service.leaks who (execution.recall who)
    (execution.observe (app) who) event action
  let start := execution.respond (app) who response
  have accounted := (app).raw_trace_accounted (initialLaw service.setup) service.horizon
    service.scheduler trace
  change execution.environmentRecall.length + remaining = service.horizon at accounted
  have startAccounted : start.environmentRecall.length + remaining = service.horizon := by
    rw [show start.environmentRecall = execution.environmentRecall from
      (app).respond_environmentRecall execution who response]
    exact accounted
  change final ∈ ((app).finish (initialLaw service.setup) service.horizon service.scheduler players
    (some ⟨remaining, none, start⟩)).support at reached
  have runner := (app).finish_eq_runToHorizon service.scheduler players (initialLaw service.setup)
    service.horizon remaining start startAccounted
  rw [runner, PMF.support_map] at reached
  obtain ⟨next, continued, rfl⟩ := reached
  have fullRounds : next ∈ ((app).runRounds service.scheduler players remaining start).support :=
    by simpa only [ReactiveApplication.runToHorizon,
      show service.horizon - start.environmentRecall.length = remaining by omega] using continued
  have zero := service.sourceCompatibleInfo_immediate_audit_clear_after_response execution who
    trace compatible players profile follows response chosen remaining le_rfl next fullRounds
      sample authentic
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  obtain ⟨clear, atTurn, slots, _⟩ := service.sourceCompatibleInfo_raw_prefixFacts
    ⟨remaining, some who, execution⟩ trace who compatible
  have fits := (runtime).serviceRisk_clear_protected_opportunity service.leaks service.bound who
    (execution.recall who) (execution.observe (app) who) event rfl turn unrecorded clear
  obtain ⟨_material, _responseEq, _call, recorded⟩ := sourceServiceImmediatePolicy_call trace
    atTurn slots clear event turn unrecorded response chosen
  have startReady : start.application.config.cut.Ready event := by
    rw [((runtime).reactive_respond_application service.leaks execution who response).1]
    exact ready
  have effective : EffectiveAction execution.application.config event action := by
    simp only [EffectiveAction, node]
    intro _
    exact ⟨value, successful⟩
  let stop := fun current : (app).Execution => event ∈ current.application.config.cut.completed
  have stoppedLaw : (app).runUntilHorizon service.scheduler players stop service.horizon start =
      (app).runUntilHorizon service.scheduler (Function.update players who (app).silentPolicy)
        stop service.horizon start := by
    unfold ReactiveApplication.runUntilHorizon
    apply sourceServicePolicy_runUntil_owner_silent service.setup service.leaks service.scheduler
      players who _ start event startReady recorded
    intro current currentReady currentRecorded
    rw [follows]
    exact service.sourceServiceImmediatePolicy_input_of_recorded profile current who event
      currentReady owned currentRecorded
  rw [(app).runToHorizon_eq_runUntilHorizon_bind service.scheduler players stop
    service.horizon start, PMF.support_bind] at continued
  obtain ⟨stopped, stoppedReached, suffix⟩ := Set.mem_iUnion₂.mp continued
  have completed := sourceServiceCanonicalDecision_protected_completion service.contract who
    execution trace event owned ready unrecorded fits action effective
    (Function.update players who (app).silentPolicy) (Function.update_self ..) stopped
      (stoppedLaw ▸ stoppedReached)
  have law := execution.application.config.step_eq_map_of_code event ready outputEq
    (.resolve who payload binding checks) codeEq true (PMF.pure (.success value))
  rw [EventCode.resolve_eval?, successful] at law
  specialize law rfl
  simp only [PMF.pure_map] at law
  have stoppedEq := (PMF.mem_support_pure_iff _ _).mp (law ▸ completed.2.2.2)
  have output : stopped.application.config.outputs event = some
      (cast (congrArg EventField.Value outputEq.symm) (.success value)) := by
    rw [stoppedEq]
    exact execution.application.config.complete_output_same event ready action _
  have preserved := ((runtime).reactiveStoreInvariant service.leaks (.inr event)
    (cast (congrArg EventField.Value outputEq.symm) (.success value))).policyInvariant (app) players
  have retained := preserved.runRounds service.scheduler
    (service.horizon - stopped.environmentRecall.length) stopped next output suffix
  refine ⟨next, ?_, retained, ?_⟩
  · rfl
  · simpa only [Nat.sub_self, ReactiveApplication.finished] using zero

open Classical in
/-- The same committed native comparator has the HIGH-correct initial payoff
on its whole continuation. Its actual authentic charge is zero, independently
of the opponents' later effective policies and the size of the deposit. -/
theorem effectiveImmediateComparator_true_guess_value
    (profile : BehavioralProfile service.setup.program) (who : Player)
    (permitted : (profile who).Admitted service.setup.program (CommitmentInterface.values _))
    (baseline : ∀ player, ((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).BehavioralPolicy player)
    (history : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).History)
    (remaining : Nat) (execution : (app).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (compatible : service.sourceCompatibleInfo who
      (some (execution.recall who, execution.observe (app) who)))
    (event : (graph service.setup).EventId) (payload : L.Ty)
    (binding : FieldRef (graph service.setup).layout (.binding who payload))
    (checks : List (GuardCheck (graph service.setup).layout payload))
    (outputEq : (graph service.setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph service.setup).layout) outputEq)
      ((graph service.setup).nodes event) = .resolve who payload binding checks)
    (node : nodeView (graph service.setup) event =
      .resolve who payload binding checks outputEq codeEq)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime).eventRecorded service.leaks (execution.recall who) event = false)
    (value : L.Val payload)
    (successful : EventCode.resolveOutput? binding checks true
      execution.application.config.store = some (.success value))
    (choice : ((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).Choice who (((menu).information (initialLaw service.setup)
        service.horizon service.scheduler).infoOf who history.trace))
    (selected : choice.1 = some ((runtime).canonicalServiceDecision service.leaks who
      (execution.recall who) (execution.observe (app) who) event
        (cast (congrArg EventField.Action outputEq.symm) true)))
    (chosen : (runtime).canonicalServiceDecision service.leaks who (execution.recall who)
      (execution.observe (app) who) event
        (cast (congrArg EventField.Action outputEq.symm) true) ∈
      (sourceServiceImmediatePolicy service.setup service.leaks service.bound profile who
        (execution.recall who) (execution.observe (app) who)).support)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (high : Bool) (deposit : Player → ℝ) :
    expect (((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).runBehavioralTerminalFrom
        ((menu).bounded (initialLaw service.setup) service.horizon
          service.scheduler).wellFoundedHistories
        (Profile.update (sig := ((menu).information (initialLaw service.setup)
          service.horizon service.scheduler).behavioralSignature) baseline who
          ((service.effectiveImmediateComparator profile who).commit
            (((menu).information (initialLaw service.setup) service.horizon
              service.scheduler).infoOf who history.trace) choice)) history)
      (fun final => TerminalAudit.utility
        (fun state _ => sourcePublicationGuessValue service.setup service.leaks event payload
          outputEq high state) ((runtime).serviceAuditObservation service.leaks)
        (sourceServiceAudit service.setup service.leaks sample) deposit final.state who) =
      if high then 1 else 0 := by
  let model := (menu).information (initialLaw service.setup) service.horizon service.scheduler
  let certificate := ((menu).bounded (initialLaw service.setup) service.horizon
    service.scheduler).wellFoundedHistories
  let updated := Profile.update (sig := model.behavioralSignature) baseline who
    ((service.effectiveImmediateComparator profile who).commit
      (model.infoOf who history.trace) choice)
  let law := model.runBehavioralTerminalFrom certificate updated history
  have stateLaw := service.effectiveImmediateComparator_committed_terminal_law profile who
    permitted baseline history remaining execution current compatible choice _ selected chosen
  change expect law _ = _
  refine (expect_congr_on_support (μ := law) ?_).trans (expect_constant law _)
  intro final supported
  have member : final.state ∈ (law.map History.state).support :=
    PMF.support_map .. ▸ ⟨final, supported, rfl⟩
  rw [stateLaw] at member
  obtain ⟨next, finalEq, output, zero⟩ := service.sourceCompatibleInfo_immediate_true_finish
    profile who remaining execution
    (current ▸ (menu).toRawTrace (initialLaw service.setup) service.horizon
      service.scheduler history.trace) compatible event payload binding checks outputEq codeEq
      node turn unrecorded value successful chosen
      ((menu).decodeProfile (initialLaw service.setup) service.horizon service.scheduler baseline)
      final.state member sample authentic
  change sourcePublicationGuessValue service.setup service.leaks event payload outputEq high
    final.state - TerminalAudit.charge ((runtime).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) final.state who * deposit who = _
  rw [zero, zero_mul, sub_zero, finalEq]
  cases high <;> simp [sourcePublicationGuessValue, ReactiveApplication.finished, output,
    PublicationResult.isSuccess]

end Vegas.AsyncServiceSpec
