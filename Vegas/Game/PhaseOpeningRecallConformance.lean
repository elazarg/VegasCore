/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseIntendedOpeningSuccess
import Vegas.Game.PhaseSourcePolicyLaw
import Vegas.Game.SourceServiceAsyncTimeliness
import Vegas.Pending.PhaseNativeTrace
import Vegas.Pending.ReactiveEmissionTokens

/-! # Authentic remembered canonical openings satisfy protected-call conformance -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (source : ∀ who, setup.intendedModel.BehavioralPolicy who)

local notation "R" => serviceRuntime setup mode deadline

/-- An authentic earlier canonical opening is a fresh acceptable call at its
exact retained record. Guard success, raw value, accepted handle, certificate,
sender and readiness token all follow from actual histories and count-clean
emissions; only its actual protected inclusion window is supplied. -/
theorem phase_recalled_opening_freshCall
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source
      assessment.strategy)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication R leaks).Scheduler)
    {current before : (phaseApplication R leaks).Control}
    (trace : ((PhaseCount.onePacketMenu R leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some current))
    (prior : ((PhaseCount.onePacketMenu R leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some before))
    (isPrefix : TracePrefix prior trace)
    (clear : current.execution.application.current.excluded = ∅)
    (consistent : ∀ who, (phaseSourcePolicy setup mode R leaks bounds wellFormed assessment
      who).Consistent (current.execution.recall who))
    (owner : Player) (entry : (phaseApplication R leaks).PlayerEntry)
    (recorded : entry ∈ current.execution.recall owner)
    (viewed : entry.beforeView = before.execution.observe (phaseApplication R leaks) owner)
    (event : (serviceGraph setup mode).EventId)
    (publication : ((serviceGraph setup mode).outputLayout event).IsPublication)
    (request : before.execution.application.SeedRequest owner
      ⟨before.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication R leaks).outputs (before.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨before.execution.application.attempt, event⟩)
    (supported : entry.action ∈ (phaseSourcePolicy setup mode R leaks bounds wellFormed assessment
      owner (before.execution.recall owner)
        (before.execution.observe (phaseApplication R leaks) owner)).support)
    (bound : (serviceGraph setup mode).EventId → Nat)
    (fitting : before.execution.application.current.native.publicView.InclusionFitsDeadline R
      bound event)
    (values : ∀ payload, (serviceGraph setup mode).outputLayout event = .publication payload →
      ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    ∃ message, FreshCall setup (PhaseNativeProjection.nativeLeaks leaks plan) owner event bound
      (PhaseNativeProjection.playerEntry R leaks plan entry) message := by
  let app := phaseApplication R leaks
  let menu := PhaseCount.onePacketMenu R leaks bounds
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let nativeLeaks := PhaseNativeProjection.nativeLeaks leaks plan
  let nativeEntry := PhaseNativeProjection.playerEntry R leaks plan entry
  have ordered := serviceGraph_revealRelaxedOrdered setup mode
  have earlierClear := (phase_clear_nativeProgress_of_prefix R leaks menu initial horizon scheduler
    before current prior trace isPrefix clear).1
  have earlierConsistent : ∀ who, (phaseSourcePolicy setup mode R leaks bounds wellFormed assessment
      who).Consistent (before.execution.recall who) := by
    intro who
    have reaches := menu.reaches_raw initial horizon scheduler isPrefix.reachesWithin
    obtain ⟨suffix, kept⟩ := app.reaches_recall_prefix initial horizon scheduler reaches before
      current rfl rfl who
    have faithful := consistent who
    rw [← kept] at faithful
    exact faithful.of_append
  obtain ⟨payload, binding, checks, outputEq, codeEq, node, value, resolved⟩ :=
    phase_ready_publication_success setup mode R leaks bounds wellFormed source assessment copies
      plan maximal horizon scheduler prior earlierClear earlierConsistent owner event request
        publication
  have stored := EventCode.binding_success_of_resolve_success binding checks true
    before.execution.application.current.native.config.store value resolved
  obtain ⟨candidate, accepted, law⟩ := phaseSourcePolicy_opening_of_history setup mode R leaks
    bounds wellFormed assessment plan inputs horizon scheduler prior owner event payload binding
      checks
      outputEq codeEq node request unsent value stored (values payload outputEq value)
  have response : entry.action = PhaseCount.phaseOpeningResponse R leaks event candidate
      ⟨payload, value⟩ := by
    rw [law, PMF.mem_support_pure_iff] at supported
    exact supported
  obtain ⟨other, associated, owned, _verified, _legal⟩ := PhaseCount.phaseOpeningResponse_of_history
    R leaks bounds plan inputs horizon scheduler prior owner event payload binding checks outputEq
      codeEq node request unsent value stored (values payload outputEq value)
  have same : other = candidate := Option.some.inj (associated.symm.trans accepted)
  subst other
  let material := disclosureSubmission (.opening event candidate ⟨payload, value⟩)
  have transmitted : nativeEntry.action.transmission = some material := by
    change entry.action.transmission = some material
    rw [response]
    rfl
  have raw := menu.toRawTrace initial horizon scheduler trace
  have nativeTrace := PhaseNativeProjection.nativeTrace R leaks plan bounds ordered maximal inputs
    horizon scheduler trace (fun _ same => by cases same; exact clear)
  have nativeRecorded : nativeEntry ∈
      (PhaseNativeProjection.execution R leaks plan current.execution).recall owner :=
    List.mem_map.mpr ⟨entry, recorded, rfl⟩
  obtain ⟨message, emitted, call⟩ :=
    (reactiveEmission_history R nativeLeaks (inputs.map State.initial) horizon
      (PhaseNativeProjection.nativeScheduler R leaks plan scheduler)
      (PhaseNativeProjection.control R leaks plan current) nativeTrace owner).2
        nativeEntry nativeRecorded material transmitted
  have callEq : message.payload.call = .opening event candidate ⟨payload, value⟩ := call
  have token := history_emissionTokens R nativeLeaks (inputs.map State.initial) horizon
    (PhaseNativeProjection.nativeScheduler R leaks plan scheduler) nativeTrace owner nativeEntry
      nativeRecorded message emitted
  have nativeViewed : nativeEntry.beforeView.application =
      before.execution.application.current.native.playerView owner := by
    change entry.beforeView.application.1 = _
    rw [viewed]
    rfl
  have ready := request.2.2.1
  have readyView := (before.execution.application.current.native.publicView_eventReady event).mpr
    ready
  have attached : message.payload.token = some ⟨event⟩ := by
    rw [token, callEq, nativeViewed]
    exact before.execution.application.current.native.publicView_tokenFor_of_ready _ event rfl ready
  have projectedEmission : entry.emitted.map
      (Message.mapPayload CommitAttemptPacket.packet) = some message := emitted
  obtain ⟨physicalMessage, physicalEmitted, projected⟩ :=
    Option.map_eq_some_iff.mp projectedEmission
  have output : physicalMessage ∈ app.outputs (current.execution.recall owner) :=
    List.mem_filterMap.mpr ⟨entry, recorded, physicalEmitted⟩
  have recalled := app.history_inputRecall initial horizon scheduler raw
  rw [← recalled owner] at output
  have authored : message.sender = owner :=
    (congrArg Message.sender projected).symm.trans
      (of_decide_eq_true (List.mem_filter.mp output).2)
  have physical := PhaseCount.physicalBindings_history R leaks bounds plan inputs horizon scheduler
    trace
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp
    (physical.clean.2 physicalMessage (List.mem_filter.mp output).1)).2.1
  have named : physicalMessage.payload.packet.call = .opening event candidate ⟨payload, value⟩ :=
    (congrArg (fun envelope : Message Player (WitnessedPacket (serviceGraph setup mode)) =>
      envelope.payload.call) projected).trans callEq
  unfold CountCallCorrect at correct
  dsimp only [PhaseCount.nativeMessage] at correct
  rw [named] at correct
  have certified : certifiedOpening message.payload = true := by
    rw [← projected]
    exact correct.1
  have acceptedChecks : GuardCheck.allAccepted? checks
      nativeEntry.beforeView.application.publicView.observation.store (.success value) =
        some true := by
    rw [nativeViewed]
    change GuardCheck.allAccepted? checks
      ((serviceGraph setup mode).publicStore
        before.execution.application.current.native.config.store)
        (.success value) = some true
    rw [GuardCheck.allAccepted?_publicStore]
    exact EventCode.guards_pass_of_resolve_success binding checks true
      before.execution.application.current.native.config.store value resolved
  have guards : nativeEntry.beforeView.application.publicView.openingGuardsAccepted
      message.payload = true := by
    simp only [PublicView.openingGuardsAccepted, callEq, node, Raw.as?_mk, Option.any_some,
      acceptedChecks, decide_true]
  refine ⟨message, ⟨⟨material, transmitted⟩, emitted, authored, ?_, ?_, ?_, ?_⟩⟩
  · rw [callEq]
    rfl
  · rw [nativeViewed]
    exact readyView
  · rw [nativeViewed]
    exact fitting
  · change (R).freshServiceAcceptable nativeEntry.beforeView.application.publicView message
    simp only [freshServiceAcceptable, callEq, freshServiceEnvelope, node]
    refine ⟨?_, ?_, certified, guards, authored, owned, ?_, by trivial, attached⟩
    · rw [nativeViewed]
      exact readyView
    · rw [nativeViewed]
      exact fitting.withinDeadline
    · rw [nativeViewed]
      exact accepted

end Vegas
