/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingFinishedPayoff
import Vegas.Examples.CommitSeedSignallingProtectedTail

/-! # Actual assessed continuation after a protected disclosure response -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- After a genuine continuation callback, the original mixed scheduler selects
the just-emitted envelope. The proof retains its original posterior on seeds. -/
theorem tail_submission_scheduler (remaining : Nat) (execution : app.Execution)
    (owner : Player) (submission : app.Submission)
    (trace : (app.protocol initial horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩))
    (retired : execution.application.attempt ≠ originalAttempt) :
    scheduler (execution.respond app owner ⟨some submission⟩).environmentRecall
        ((execution.respond app owner ⟨some submission⟩).observeEnvironment app) =
      PMF.pure (.include (owner, execution.network.nextSerial owner)) := by
  classical
  obtain ⟨seed, ⟨fixed⟩⟩ := fixed_seed_decision ⟨remaining, some owner, execution⟩ trace
  obtain ⟨chosen, past, view, recalled, serial⟩ :=
    tail_response_command seed fixed owner rfl retired ⟨some submission⟩
  have response :
      responseCommand owner (execution.respond app owner ⟨some submission⟩).environmentRecall
          ((execution.respond app owner ⟨some submission⟩).observeEnvironment app) =
        .include (owner, execution.network.nextSerial owner) := by
    rw [app.respond_environmentRecall, recalled,
      responseCommand_transmission execution owner past ⟨view, .activate owner⟩ rfl serial
        submission]
  rw [response] at chosen
  have respondedRetired :
      ((execution.respond app owner ⟨some submission⟩).observeEnvironment app).application.attempt
        ≠ originalAttempt := retired
  have common (other : Seeds) :
      choose other (execution.respond app owner ⟨some submission⟩).environmentRecall
          ((execution.respond app owner ⟨some submission⟩).observeEnvironment app) =
        .include (owner, execution.network.nextSerial owner) := by
    rw [choose, ite_eq_right respondedRetired] at chosen ⊢
    exact chosen
  rw [scheduler_eq_posterior]
  calc
    _ = (implementation.posterior
        (execution.respond app owner ⟨some submission⟩).environmentRecall).map
          (fun _ => .include (owner, execution.network.nextSerial owner)) := by
      apply map_congr_on_support
      intro other _
      exact common other
    _ = _ := PMF.map_const _ _

/-- A counted truthful current opening has nonnegative payoff under the
unchanged assessed continuation. The actual next scheduler turn and its
recorded native inclusion are derived from the current callback. -/
theorem counted_tail_opening_assessed_value_nonnegative
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution)
    (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining + 1, some owner, execution⟩))
    (retired : execution.application.attempt ≠ originalAttempt)
    (candidate : Handle graph) (value : Bool)
    (allowed : PhaseCount.phaseOpeningResponse runtime leaks (revealEvent owner) candidate
      ⟨.bool, value⟩ ∈ countedMenu.actions owner (execution.recall owner)
        (execution.observe app owner))
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (timely : execution.application.current.native.WithinDeadline runtime (revealEvent owner))
    (stored : execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value))) :
    0 ≤ expect (app.finish initial horizon scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
      (some ⟨remaining + 1, none, execution.respond app owner
        (PhaseCount.phaseOpeningResponse runtime leaks (revealEvent owner) candidate
          ⟨.bool, value⟩)⟩)) (fun state => netPayoff state owner) := by
  classical
  let submission := disclosureSubmission (.opening (revealEvent owner) candidate ⟨.bool, value⟩)
  let responded := execution.respond app owner ⟨some submission⟩
  let message : Message Player (CommitAttemptPacket graph) :=
    ⟨(owner, execution.network.nextSerial owner),
      app.packet responded.application owner (execution.network.known owner) submission⟩
  have application : responded.application = execution.application := rfl
  have payloadAttempt : message.payload.attempt = execution.application.attempt := rfl
  have call : message.payload.packet.call =
      .opening (revealEvent owner) candidate ⟨.bool, value⟩ := by
    dsimp only [message]
    change (responded.application.emit owner (execution.network.known owner) submission).packet.call
      = _
    simp only [PhaseRuntimeState.emit, RecoveryState.emit]
    split <;> split <;> rfl
  have member : message ∈ responded.network.inputs :=
    List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have serials := app.serialsBeforeNext_history scheduler initial horizon
    (countedMenu.toRawTrace initial horizon scheduler trace)
  have lookup : responded.network.lookup message.id = some message :=
    serials.lookup_submit owner
      (app.packet responded.application owner (execution.network.known owner) submission)
  have scheduled : scheduler responded.environmentRecall (responded.observeEnvironment app) =
      PMF.pure (.include message.id) :=
    tail_submission_scheduler (remaining + 1) execution owner submission
      (countedMenu.toRawTrace initial horizon scheduler trace) retired
  obtain ⟨respondedTrace⟩ := countedMenu.trace_respond initial horizon scheduler
    (remaining + 1) execution owner ⟨some submission⟩ trace allowed
  let next : app.Execution :=
    { responded.includePending app message.id with
      environmentRecall := responded.environmentRecall ++
        [⟨responded.observeEnvironment app, .include message.id⟩] }
  have step : responded.environmentStep app (.include message.id) = PMF.pure next := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map, next]
  have moved : next ∈ (responded.environmentStep app (.include message.id)).support := by
    rw [step]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have selected : (.include message.id : app.Command) ∈
      (scheduler responded.environmentRecall (responded.observeEnvironment app)).support := by
    rw [scheduled]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have ready : responded.application.SeedRequest message.sender
      ⟨message.payload.attempt, revealEvent owner⟩ := by
    change responded.application.SeedRequest owner
      ⟨message.payload.attempt, revealEvent owner⟩
    rw [application, payloadAttempt]
    exact request
  have timelyAfter : responded.application.current.native.WithinDeadline runtime
      (revealEvent owner) := by
    rwa [application]
  have storedAfter : responded.application.current.native.config.store
      (.inr (bindingEvent owner)) = some
        (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
          (PublicationResult.success value)) := by
    rwa [application]
  have bound := counted_successful_opening_assessed_value_nonnegative assessment equilibrium
    remaining responded respondedTrace owner message member lookup candidate ⟨.bool, value⟩
      call ready timelyAfter value storedAfter selected next moved
  change 0 ≤ expect (app.finish initial horizon scheduler
    (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
    (some ⟨remaining + 1, none, responded⟩)) (fun state => netPayoff state owner)
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind]
  rw [ReactiveApplication.runRounds, ReactiveApplication.round, scheduled, PMF.pure_bind,
    ReactiveApplication.dispatch, step, PMF.pure_bind]
  simpa only [ReactiveApplication.Command.actor?, ReactiveApplication.resume, PMF.pure_bind,
    ReactiveApplication.finish] using bound

end Vegas.Examples.CommitSeedSignalling
