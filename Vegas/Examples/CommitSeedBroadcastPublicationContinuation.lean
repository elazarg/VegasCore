/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastPublicationResponse
import Vegas.Examples.CommitSeedBroadcastPublicationOpeningValue
import Vegas.Examples.CommitSeedBroadcastPublicationAfterSubmission

/-! # Actual incumbent publication responses preserve survival under every raw tail -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

theorem counted_equilibrium_response_allowed
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

/-- The existing native handler factor supplies the finished-owner invariant
at the actual next include. Every later physical response may be arbitrary RAW. -/
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
    (allowed : (⟨some material⟩ : app.Action) ∈ countedMenu.actions owner
      (execution.recall owner) (execution.observe app owner))
    (players : Player → app.Policy) (after : app.Execution)
    (supported : after ∈ (app.runRounds scheduler players (remaining + 1)
      (execution.respond app owner ⟨some material⟩)).support) :
    owner ∉ after.application.current.excluded := by
  let responded := execution.respond app owner ⟨some material⟩
  obtain ⟨postTrace⟩ := countedMenu.trace_respond initial horizon scheduler (remaining + 1)
    execution owner ⟨some material⟩ trace allowed
  have timely := counted_tail_request_timely (remaining + 1) execution owner trace
    ⟨execution.application.attempt, revealEvent owner⟩ retired request
  have scheduled := tail_submission_scheduler (remaining + 1) execution owner material
    (countedMenu.toRawTrace initial horizon scheduler trace) retired
  change after ∈ ((app.round scheduler players responded).bind
    (app.runRounds scheduler players remaining)).support at supported
  obtain ⟨middle, stepped, continued⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  change middle ∈ ((scheduler responded.environmentRecall (responded.observeEnvironment app)).bind
    (fun command => app.dispatch players command responded)).support at stepped
  rw [scheduled, PMF.pure_bind] at stepped
  simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?] at stepped
  change middle ∈ ((responded.environmentStep app
    (.include (owner, execution.network.nextSerial owner))).bind PMF.pure).support at stepped
  rw [PMF.bind_pure] at stepped
  have finished := publication_inclusion_finished scheduler remaining execution owner trace
    request value stored timely material allowed postTrace middle stepped
  exact finished_owner_run_survives scheduler players remaining middle after owner finished.1
    finished.2.1 finished.2.2 continued

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

/-- At a genuine protected successful publication callback, the actual
incumbent finish law survives. Its current non-WAIT choice is forced by the
full native information-fiber comparison, and its future is unchanged. -/
theorem counted_assessed_publication_finish_survives
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
    (after : app.Execution)
    (reached : app.finished after ∈ (app.finish initial horizon scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        (some ⟨remaining + 1, some owner, execution⟩)).support) :
    owner ∉ after.application.current.excluded := by
  let players := rawMenu.decodeProfile initial horizon scheduler assessment.strategy
  change app.finished after ∈ (((app.resume players (some owner) execution).bind
    (app.runRounds scheduler players (remaining + 1))).map app.finished).support at reached
  obtain ⟨final, reached, equal⟩ := PMF.support_map .. ▸ reached
  have same : final = after := congrArg ReactiveApplication.Control.execution
    (Option.some.inj equal)
  subst final
  obtain ⟨responded, response, continued⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  change responded ∈ ((players owner (execution.recall owner)
    (execution.observe app owner)).map (execution.respond app owner)).support at response
  obtain ⟨action, chosen, rfl⟩ := PMF.support_map .. ▸ response
  exact counted_assessed_publication_response_future_survives assessment equilibrium remaining
    execution owner trace retired request value stored action chosen players after continued

end Vegas.Examples.CommitSeedBroadcast
