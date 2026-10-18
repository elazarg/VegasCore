/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingPublicationResponse
import Vegas.Examples.CommitSeedSignallingSubmissionShape

/-! # Survival after actual truthful continuation-publication transmissions -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem counted_equilibrium_response_allowed
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (response : app.Action)
    (supported : response ∈ (rawMenu.decodeProfile initial horizon scheduler assessment.strategy
      owner (execution.recall owner) (execution.observe app owner)).support) :
    response ∈ (PhaseCount.onePacketMenu runtime leaks bounds).actions owner
      (execution.recall owner) (execution.observe (phaseApplication runtime leaks) owner) := by
  let history : countedProtocol.History := ⟨some ⟨remaining, some owner, execution⟩, trace⟩
  have running : ¬ countedProtocol.terminal history.state := by
    intro stopped
    cases stopped.2
  have acting : countedProtocol.active history.state owner := rfl
  obtain ⟨site, atSite⟩ :=
    countedModel.exists_informationSite_of_active owner history running acting
  have native : site.1 = some (execution.recall owner, execution.observe app owner) := by
    rw [atSite]
    change (countedMenu.signals initial horizon scheduler).infoOf owner history.trace = _
    rw [countedMenu.info]
    change app.observe owner (some ⟨remaining, some owner, execution⟩) = _
    simp only [ReactiveApplication.observe, ite_true]
  exact raw_equilibrium_clean_response_counted assessment equilibrium owner
    ((countedInRaw.actionRestriction initial horizon scheduler).site owner site) _ _ native
      (counted_site_ownPastPermitted owner site _ _ native) response supported

/-- Every nonsilent admitted current response at a successful publication
is actually included next and makes its sender immune to all later raw play.
The theorem does not prescribe any later player policy. -/
theorem counted_publication_transmission_future_survives
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining + 1, some owner, execution⟩))
    (retired : execution.application.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (value : Bool)
    (stored : execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (material : WitnessedSubmission graph)
    (allowed : (⟨some material⟩ : (phaseApplication runtime leaks).Action) ∈
      (PhaseCount.onePacketMenu runtime leaks bounds).actions owner (execution.recall owner)
        (execution.observe (phaseApplication runtime leaks) owner))
    (players : Player → app.Policy) (after : app.Execution)
    (supported : after ∈ (app.runRounds scheduler players (remaining + 1)
      (execution.respond app owner ⟨some material⟩)).support) :
    owner ∉ after.application.current.excluded := by
  obtain ⟨candidate, openedValue, packet⟩ :=
    counted_submission_opening_shape scheduler (remaining + 1) execution owner trace request
      material allowed
  let responded := execution.respond app owner ⟨some material⟩
  have application : responded.application = execution.application := by
    rcases material with ⟨⟨call, preparation⟩, evidence⟩
    dsimp only at packet
    subst call
    rfl
  let message : Message Player (CommitAttemptPacket graph) :=
    ⟨(owner, execution.network.nextSerial owner), app.packet responded.application owner
      (execution.network.known owner) material⟩
  have attempt : message.payload.attempt = execution.application.attempt := by
    change responded.application.attempt = execution.application.attempt
    rw [application]
  have call : message.payload.packet.call =
      .opening (revealEvent owner) candidate openedValue := by
    change (responded.application.emit owner (execution.network.known owner) material).packet.call
      = _
    simp only [PhaseRuntimeState.emit, RecoveryState.emit]
    split <;> split <;> exact packet
  have member : message ∈ responded.network.inputs :=
    List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have serials := app.serialsBeforeNext_history scheduler initial horizon
    (countedMenu.toRawTrace initial horizon scheduler trace)
  have lookup : responded.network.lookup message.id = some message :=
    serials.lookup_submit owner
      (app.packet responded.application owner (execution.network.known owner) material)
  obtain ⟨respondedTrace⟩ := countedMenu.trace_respond initial horizon scheduler (remaining + 1)
    execution owner ⟨some material⟩ trace allowed
  have requested : responded.application.SeedRequest message.sender
      ⟨message.payload.attempt, revealEvent owner⟩ := by
    change responded.application.SeedRequest owner _
    rw [application, attempt]
    exact request
  have timely := counted_tail_request_timely (remaining + 1) execution owner trace
    ⟨execution.application.attempt, revealEvent owner⟩ retired request
  have timelyAfter : responded.application.current.native.WithinDeadline runtime
      (revealEvent owner) := by rwa [application]
  have storedAfter : responded.application.current.native.config.store
      (.inr (bindingEvent owner)) = some
        (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
          (PublicationResult.success value)) := by rwa [application]
  have scheduled : scheduler responded.environmentRecall (responded.observeEnvironment app) =
      PMF.pure (.include message.id) :=
    tail_submission_scheduler (remaining + 1) execution owner material
      (countedMenu.toRawTrace initial horizon scheduler trace) retired
  let next : app.Execution :=
    { responded.includePending app message.id with
      environmentRecall := responded.environmentRecall ++
        [⟨responded.observeEnvironment app, .include message.id⟩] }
  have step : responded.environmentStep app (.include message.id) = PMF.pure next := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map, next]
  have moved : next ∈ (responded.environmentStep app (.include message.id)).support := by
    rw [step]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  change after ∈ (app.runRounds scheduler players (remaining + 1) responded).support at supported
  rw [ReactiveApplication.runRounds, ReactiveApplication.round, scheduled, PMF.pure_bind,
    ReactiveApplication.dispatch, step, PMF.pure_bind] at supported
  simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume, PMF.pure_bind]
    at supported
  exact counted_successful_opening_future_survives scheduler ⟨remaining + 1, none, responded⟩
    respondedTrace owner message member lookup candidate openedValue call requested
      timelyAfter value storedAfter next moved scheduler players remaining after supported

/-- The incumbent's actual response at a successful counted publication
survives under every later raw policy. Charge reflection and the full-fiber
strict comparison derive its current admitted nonsilent response. -/
theorem counted_assessed_publication_response_future_survives
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining + 1, some owner, execution⟩))
    (retired : execution.application.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (value : Bool)
    (stored : execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (response : app.Action)
    (chosen : response ∈ (rawMenu.decodeProfile initial horizon scheduler assessment.strategy
      owner (execution.recall owner) (execution.observe app owner)).support)
    (players : Player → app.Policy) (after : app.Execution)
    (supported : after ∈ (app.runRounds scheduler players (remaining + 1)
      (execution.respond app owner response)).support) :
    owner ∉ after.application.current.excluded := by
  have allowed := counted_equilibrium_response_allowed assessment equilibrium (remaining + 1)
    execution owner trace response chosen
  have nonempty := counted_successful_publication_response_nonsilent assessment equilibrium
    (remaining + 1) execution owner trace retired request value stored response chosen
  cases response with
  | mk transmission =>
      cases transmission with
      | none => exact (nonempty rfl).elim
      | some material =>
          exact counted_publication_transmission_future_survives remaining execution owner trace
            retired request value stored material allowed players after supported

end Vegas.Examples.CommitSeedSignalling
