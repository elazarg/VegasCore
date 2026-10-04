/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateResolutionFirstActivation

/-! # Accepted first decisions and the completed second input

The first canonical FALSE and TRUE packets are actually included at clock zero.
Their later native menu has only silence; the pending risk expansion is reserved
for the actual unrecorded second opportunity.
-/

noncomputable section

namespace Vegas.LateResolutionService

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory GameTheory.Math.Probability

def firstDecisionState (disclose : Bool) : app.State :=
  firstExecution.application.complete resolution first_resolution_ready disclose
    (if disclose then .success true else .failure)

def firstDecisionMessage (disclose : Bool) : Message Player (WitnessedPacket nativeGraph) :=
  ⟨(owner, 0), app.packet firstExecution.application owner []
    (disclosureSubmission (if disclose then
      .opening resolution firstCandidate ⟨.bool, true⟩ else .withhold resolution))⟩

theorem first_decision_lookup (disclose : Bool) :
    (firstExecution.respond app owner (lateResponse firstCandidate disclose)).network.lookup
      (owner, 0) = some (firstDecisionMessage disclose) := by
  cases disclose <;> rfl

theorem first_decision_handled (disclose : Bool) :
    app.handle firstExecution.application (firstDecisionMessage disclose) =
      some (firstDecisionState disclose) := by
  have current : (firstDecisionMessage disclose).payload.token =
      firstExecution.application.publicView.tokenFor (firstDecisionMessage disclose).payload.call :=
    by cases disclose <;> rfl
  rw [(runtime setup).reactiveApplication_handle_of_current_token leaks _ _ current]
  cases disclose
  · exact handle_withhold_unremembered_eq (runtime setup) firstExecution.application (owner, 0)
      resolution owner .bool initialBinding [] resolution_output resolution_code resolution_node
      first_resolution_ready (by change 0 - 0 < 3; decide) rfl rfl
  · exact handle_opening_eq (runtime setup) firstExecution.application (owner, 0) resolution
      firstCandidate owner .bool initialBinding [] resolution_output resolution_code resolution_node
      first_resolution_ready (by change 0 - 0 < 3; decide) rfl rfl rfl true rfl rfl
      (.success true) rfl

theorem first_decision_included (disclose : Bool) :
    ((firstExecution.respond app owner (lateResponse firstCandidate disclose)).includePending app
      (owner, 0)).application = firstDecisionState disclose ∧
    ((owner, 0), true) ∈
      ((firstExecution.respond app owner (lateResponse firstCandidate disclose)).includePending app
        (owner, 0)).receipts := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  rw [first_decision_lookup]
  dsimp only
  rw [late_response_application, first_decision_handled]
  exact ⟨rfl, List.mem_append_right _ (List.mem_singleton_self _)⟩

theorem first_response_command (disclose : Bool) :
    latest ((firstExecution.respond app owner
      (lateResponse firstCandidate disclose)).observeEnvironment app) = .include (owner, 0) := by
  have packetCall (state : app.State) (known : List (Message Player (WitnessedPacket nativeGraph)))
      (submission : app.Submission) :
      (app.packet state owner known submission).call = submission.call.packet := rfl
  cases disclose <;>
    simp [latest, reactiveLatest, ReactiveApplication.Execution.observeEnvironment,
      ReactiveApplication.Execution.respond, lateResponse, disclosureSubmission,
      MessageNetwork.submit, MessageNetwork.empty, MessageNetwork.publicView,
      ReactiveApplication.EnvironmentView.Unpublished, firstExecution, firstSample1Execution,
      firstSample0Execution, firstInitialExecution, ReactiveApplication.Execution.initial,
      Payload.event?, Message.sender, packetCall]


def activateExecution (execution : app.Execution) : app.Execution :=
  { execution with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .activate owner⟩] }

theorem activate_environment (execution : app.Execution) :
    execution.environmentStep app (.activate owner) = PMF.pure (activateExecution execution) := by
  change ((PMF.pure ∅).map _).map _ = _
  simp only [PMF.pure_map, MessageNetwork.learn_empty]
  rfl

def firstIncludedExecution (disclose : Bool) : app.Execution :=
  includeExecution (firstExecution.respond app owner (lateResponse firstCandidate disclose))
    (owner, 0)

def secondDecisionExecution (disclose : Bool) : app.Execution :=
  activateExecution (tickExecution (firstIncludedExecution disclose))

def secondWaitExecution : app.Execution :=
  activateExecution (tickExecution (waitExecution (firstExecution.respond app owner ⟨none⟩)))

theorem second_decision_application (disclose : Bool) :
    (secondDecisionExecution disclose).application =
      { firstDecisionState disclose with clock := 1 } := by
  change { (firstIncludedExecution disclose).application with
    clock := (firstIncludedExecution disclose).application.clock + 1 } = _
  have included : (firstIncludedExecution disclose).application = firstDecisionState disclose :=
    (first_decision_included disclose).1
  rw [included]
  rfl

theorem second_decision_turn (disclose : Bool) :
    ((secondDecisionExecution disclose).observe app owner).application.publicView.ownTurn? owner =
      none := by
  change (secondDecisionExecution disclose).application.publicView.ownTurn? owner = none
  rw [second_decision_application]
  cases disclose <;> rfl

theorem second_decision_clear (disclose : Bool) :
    (runtime setup).serviceRisk leaks bound owner ((secondDecisionExecution disclose).recall owner)
      ((secondDecisionExecution disclose).observe app owner) = false := by
  apply (runtime setup).serviceRisk_clear
  · change (((secondDecisionExecution disclose).application.publicView.missedDecisionBy owner ||
      (runtime setup).recalledSubmissionRisk leaks bound owner
        ((firstExecution.respond app owner (lateResponse firstCandidate disclose)).recall owner)) ||
          (runtime setup).recalledOpportunityRisk leaks bound owner
            ((firstExecution.respond app owner
              (lateResponse firstCandidate disclose)).recall owner))
              = false
    have publicClear : (secondDecisionExecution disclose).application.publicView.missedDecisionBy
        owner = false := by
      rw [second_decision_application]
      cases disclose <;> rfl
    have fits : ∀ event, (runtime setup).submittedEvent? leaks
        (lateResponse firstCandidate disclose) = some event →
        (firstExecution.observe app owner).application.publicView.InclusionFitsDeadline
          (runtime setup) bound event := by
      intro event named
      have same : event = resolution := by
        cases disclose <;> exact (Option.some.inj named).symm
      subst event
      exact first_resolution_fits
    have recalled := (runtime setup).recalledSubmissionRisk_respond_protected leaks bound
      firstExecution owner (lateResponse firstCandidate disclose) fits
    have opportunity := (runtime setup).recalledOpportunityRisk_respond_clear leaks bound
      firstExecution owner (lateResponse firstCandidate disclose)
        ((runtime setup).firstUnprotectedOpportunity_protected leaks bound owner _ _ resolution
          first_resolution_turn first_resolution_fits)
    rw [publicClear, recalled, opportunity]
    rfl
  · simp only [firstUnprotectedOpportunity, second_decision_turn, ite_self]

theorem second_decision_response_silent (bounds : MessageBounds nativeGraph) (disclose : Bool)
    (response : app.Action)
    (available : response ∈ (nativeMenu bounds).actions owner
      ((secondDecisionExecution disclose).recall owner)
      ((secondDecisionExecution disclose).observe app owner)) : response = ⟨none⟩ := by
  change response ∈ bounds.riskActions (runtime setup) leaks bound owner _ _ at available
  rw [bounds.riskActions_of_clear _ _ _ _ _ _ (second_decision_clear disclose)] at available
  rcases bounds.canonicalActions_cases (runtime setup) leaks owner _ _ response available with
    waited | ⟨event, _, turn, _⟩
  · exact waited
  · rw [second_decision_turn] at turn
    cases turn


theorem first_control_include (players : Player → app.Policy) (disclose : Bool) :
    app.controlStep (initialLaw setup) horizon scheduler players
      (some ⟨7, none, firstExecution.respond app owner (lateResponse firstCandidate disclose)⟩) =
      PMF.pure (some ⟨6, none, firstIncludedExecution disclose⟩) := by
  change (PMF.pure (latest ((firstExecution.respond app owner
    (lateResponse firstCandidate disclose)).observeEnvironment app))).bind _ = _
  rw [first_response_command, PMF.pure_bind]
  change ((firstExecution.respond app owner (lateResponse firstCandidate disclose)).environmentStep
    app (.include (owner, 0))).map _ = _
  rw [include_environment, PMF.pure_map]
  rfl

theorem first_control_tick (players : Player → app.Policy) (disclose : Bool) :
    app.controlStep (initialLaw setup) horizon scheduler players
      (some ⟨6, none, firstIncludedExecution disclose⟩) =
      PMF.pure (some ⟨5, none, tickExecution (firstIncludedExecution disclose)⟩) := by
  change (PMF.pure (.application .advanceClock : app.Command)).bind _ = _
  rw [PMF.pure_bind]
  change ((firstIncludedExecution disclose).environmentStep app (.application .advanceClock)).map
    _ = _
  rw [tick_environment, PMF.pure_map]
  rfl

theorem first_control_second_activation (players : Player → app.Policy) (disclose : Bool) :
    app.controlStep (initialLaw setup) horizon scheduler players
      (some ⟨5, none, tickExecution (firstIncludedExecution disclose)⟩) =
      PMF.pure (some ⟨4, some owner, secondDecisionExecution disclose⟩) := by
  change (PMF.pure (.activate owner : app.Command)).bind _ = _
  rw [PMF.pure_bind]
  change ((tickExecution (firstIncludedExecution disclose)).environmentStep app
    (.activate owner)).map
    _ = _
  rw [activate_environment, PMF.pure_map]
  rfl

theorem first_control_wait (players : Player → app.Policy) :
    app.controlStep (initialLaw setup) horizon scheduler players
      (some ⟨7, none, firstExecution.respond app owner ⟨none⟩⟩) =
      PMF.pure (some ⟨6, none, waitExecution (firstExecution.respond app owner ⟨none⟩)⟩) := by
  change (PMF.pure (.wait : app.Command)).bind _ = _
  rw [PMF.pure_bind]
  change ((firstExecution.respond app owner ⟨none⟩).environmentStep app .wait).map _ = _
  rw [wait_environment, PMF.pure_map]
  rfl

theorem first_control_wait_tick (players : Player → app.Policy) :
    app.controlStep (initialLaw setup) horizon scheduler players
      (some ⟨6, none, waitExecution (firstExecution.respond app owner ⟨none⟩)⟩) =
      PMF.pure (some ⟨5, none, tickExecution (waitExecution
        (firstExecution.respond app owner ⟨none⟩))⟩) := by
  change (PMF.pure (.application .advanceClock : app.Command)).bind _ = _
  rw [PMF.pure_bind]
  change ((waitExecution (firstExecution.respond app owner ⟨none⟩)).environmentStep app
    (.application .advanceClock)).map _ = _
  rw [tick_environment, PMF.pure_map]
  rfl

theorem first_control_wait_second_activation (players : Player → app.Policy) :
    app.controlStep (initialLaw setup) horizon scheduler players
      (some ⟨5, none, tickExecution (waitExecution (firstExecution.respond app owner ⟨none⟩))⟩) =
      PMF.pure (some ⟨4, some owner, secondWaitExecution⟩) := by
  change (PMF.pure (.activate owner : app.Command)).bind _ = _
  rw [PMF.pure_bind]
  change ((tickExecution (waitExecution (firstExecution.respond app owner ⟨none⟩))).environmentStep
    app (.activate owner)).map _ = _
  rw [activate_environment, PMF.pure_map]
  rfl

end Vegas.LateResolutionService
