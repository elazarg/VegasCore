/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateResolutionFirstPayoff
import Vegas.Examples.LateResolutionFreeLate

/-! # Optimality of the protected first opening in the native game -/

noncomputable section

namespace Vegas.LateResolutionService

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory GameTheory.Math.Probability

theorem second_decision_choice_law (bounds : MessageBounds nativeGraph) (disclose : Bool)
    (law : PMF ((nativeModel bounds).Choice owner
      (some ((secondDecisionExecution disclose).recall owner,
        (secondDecisionExecution disclose).observe app owner)))) :
    law.map Subtype.val = PMF.pure (some (⟨none⟩ : app.Action)) := by
  calc
    _ = law.map (fun _ => some (⟨none⟩ : app.Action)) := by
      apply map_congr_on_support _
      intro choice _
      obtain ⟨action, available, chosen⟩ := choice.2
      rw [chosen, second_decision_response_silent bounds disclose action available]
    _ = _ := PMF.map_const _ _

theorem second_decision_decoded_law (bounds : MessageBounds nativeGraph)
    (profile : ∀ who, (nativeModel bounds).BehavioralPolicy who) (disclose : Bool) :
    ((nativeMenu bounds).decodeProfile (initialLaw setup) horizon scheduler profile) owner
      ((secondDecisionExecution disclose).recall owner)
      ((secondDecisionExecution disclose).observe app owner) = PMF.pure (⟨none⟩ : app.Action) := by
  simp only [ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
    ReactiveApplication.ResponseMenu.embedPolicy, PMF.map_comp]
  change (profile owner _).map (fun choice => choice.val.getD ⟨none⟩) = _
  calc
    _ = ((profile owner _).map Subtype.val).map
        (fun action : Option app.Action => action.getD ⟨none⟩) :=
      (PMF.map_comp Subtype.val _ _).symm
    _ = _ := by rw [second_decision_choice_law, PMF.pure_map]; rfl

theorem first_decided_round_include (players : Player → app.Policy) (disclose : Bool) :
    app.round scheduler players (firstExecution.respond app owner
      (lateResponse firstCandidate disclose)) = PMF.pure (firstIncludedExecution disclose) := by
  change (PMF.pure (latest ((firstExecution.respond app owner
    (lateResponse firstCandidate disclose)).observeEnvironment app))).bind _ = _
  rw [first_response_command, PMF.pure_bind]
  change ((firstExecution.respond app owner (lateResponse firstCandidate disclose)).environmentStep
    app (.include (owner, 0))).bind PMF.pure = _
  rw [PMF.bind_pure, include_environment]
  rfl

theorem first_decided_round_tick (players : Player → app.Policy) (disclose : Bool) :
    app.round scheduler players (firstIncludedExecution disclose) =
      PMF.pure (tickExecution (firstIncludedExecution disclose)) := by
  change (PMF.pure (.application .advanceClock : app.Command)).bind _ = _
  rw [PMF.pure_bind]
  change ((firstIncludedExecution disclose).environmentStep app
    (.application .advanceClock)).bind PMF.pure = _
  rw [PMF.bind_pure, tick_environment]

theorem first_decided_round_activation (bounds : MessageBounds nativeGraph)
    (profile : ∀ who, (nativeModel bounds).BehavioralPolicy who) (disclose : Bool) :
    app.round scheduler ((nativeMenu bounds).decodeProfile (initialLaw setup) horizon scheduler
      profile) (tickExecution (firstIncludedExecution disclose)) =
      PMF.pure ((secondDecisionExecution disclose).respond app owner ⟨none⟩) := by
  change (PMF.pure (.activate owner : app.Command)).bind _ = _
  rw [PMF.pure_bind]
  change ((tickExecution (firstIncludedExecution disclose)).environmentStep app
    (.activate owner)).bind _ = _
  rw [activate_environment, PMF.pure_bind]
  change (((nativeMenu bounds).decodeProfile (initialLaw setup) horizon scheduler profile) owner
    ((secondDecisionExecution disclose).recall owner)
    ((secondDecisionExecution disclose).observe app owner)).map _ = _
  rw [second_decision_decoded_law, PMF.pure_map]
  rfl

theorem first_decided_native_physical_run (bounds : MessageBounds nativeGraph)
    (profile : ∀ who, (nativeModel bounds).BehavioralPolicy who) (disclose : Bool) :
    app.runRounds scheduler
      ((nativeMenu bounds).decodeProfile (initialLaw setup) horizon scheduler profile) 7
      (firstExecution.respond app owner (lateResponse firstCandidate disclose)) =
      PMF.pure (firstDecisionEndpoint disclose) := by
  rw [ReactiveApplication.runRounds, first_decided_round_include, PMF.pure_bind,
    ReactiveApplication.runRounds, first_decided_round_tick, PMF.pure_bind,
    ReactiveApplication.runRounds, first_decided_round_activation, PMF.pure_bind,
    late_rounds_policy_independent _ 4 _ (by rfl), first_completed_rounds]

theorem first_native_decided_run (bounds : MessageBounds nativeGraph)
    (profile : ∀ who, (nativeModel bounds).BehavioralPolicy who)
    (history : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).History)
    (current : history.state = some ⟨7, some owner, firstExecution⟩) (disclose : Bool)
    (chosen : (profile owner (some (firstExecution.recall owner,
      firstExecution.observe app owner))).map Subtype.val =
        PMF.pure (some (lateResponse firstCandidate disclose)))
    (fuel : Nat) (enough : 15 ≤ fuel) :
    ((nativeModel bounds).runBehavioralFrom profile fuel history).map
      ExecutionProtocol.History.state =
        PMF.pure (app.finished (firstDecisionEndpoint disclose)) := by
  rw [(nativeMenu bounds).run_eq_finish (initialLaw setup) horizon scheduler profile fuel
    history (by rw [current]; exact enough), current]
  let players := (nativeMenu bounds).decodeProfile (initialLaw setup) horizon scheduler profile
  have response : players owner (firstExecution.recall owner) (firstExecution.observe app owner) =
      PMF.pure (lateResponse firstCandidate disclose) := by
    simp only [players, ReactiveApplication.ResponseMenu.decodeProfile,
      ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy, PMF.map_comp]
    change (profile owner _).map (fun choice => choice.val.getD ⟨none⟩) = _
    calc
      _ = ((profile owner _).map Subtype.val).map
          (fun action : Option app.Action => action.getD ⟨none⟩) :=
        (PMF.map_comp Subtype.val _ _).symm
      _ = _ := by rw [chosen, PMF.pure_map]; rfl
  change ((app.invoke players owner firstExecution).bind (app.runRounds scheduler players 7)).map
    app.finished = _
  rw [ReactiveApplication.invoke, response, PMF.pure_map, PMF.pure_bind,
    first_decided_native_physical_run, PMF.pure_map]

theorem first_native_response_value (bounds : MessageBounds nativeGraph)
    (profile : ∀ who, (nativeModel bounds).BehavioralPolicy who)
    (history : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).History)
    (current : history.state = some ⟨7, some owner, firstExecution⟩) (disclose : Bool)
    (chosen : (profile owner (some (firstExecution.recall owner,
      firstExecution.observe app owner))).map Subtype.val =
        PMF.pure (some (lateResponse firstCandidate disclose)))
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) :
    expect ((nativeModel bounds).runBehavioralFrom profile 21 history)
      (fun final => auditedUtility sample deposit final.state owner) =
      if disclose then 1 else 0 := by
  calc
    _ = expect (((nativeModel bounds).runBehavioralFrom profile 21 history).map
        ExecutionProtocol.History.state) (fun state => auditedUtility sample deposit state owner) :=
      (expect_map ExecutionProtocol.History.state _ _).symm
    _ = _ := by
      rw [first_native_decided_run bounds profile history current disclose chosen 21 (by decide),
        expect_pure]
      exact first_endpoint_value disclose sample authentic deposit

theorem first_opening_locally_optimal (bounds : MessageBounds nativeGraph)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) (nonnegative : 0 ≤ deposit)
    (assessment : (nativeModel bounds).BehavioralAssessment)
    (chooses : (assessment.strategy owner (firstSite bounds).1).map Subtype.val =
      PMF.pure (some (lateResponse firstCandidate true))) :
    (assessment.truncatedContinuationContext (firstSite bounds)
      (fun final => auditedUtility sample deposit final.state owner) 21).IsLocallyOptimal
        Set.univ (assessment.strategy owner) := by
  have value : (assessment.truncatedContinuationContext (firstSite bounds)
      (fun final => auditedUtility sample deposit final.state owner) 21).value
        (assessment.strategy owner) = 1 := by
    rw [InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
      Profile.update_eq_self, expect_bind_of_finite]
    calc
      _ = expect (assessment.belief owner (firstSite bounds)) (fun _ => (1 : ℝ)) := by
        apply expect_congr_on_support
        intro history _
        exact first_native_response_value bounds assessment.strategy history.1
          (first_information_resources bounds history) true chooses sample authentic deposit
      _ = _ := expect_constant _ _
  refine (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _)
    (fun _ _ => payoffIntegrable_of_finite _ _)).mpr fun alternative _ => ?_
  rw [value, InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
    expect_bind_of_finite]
  apply expect_le_const _ _ (payoffIntegrable_of_finite _ _) 1
  intro history _
  exact expect_le_const _ _ (payoffIntegrable_of_finite _ _) 1
    (fun final _ => (auditedUtility_bounds sample deposit nonnegative final.state owner).2)

/-- Every completed late information fiber is past the only other activation. -/
theorem second_decision_information_resources (bounds : MessageBounds nativeGraph)
    (disclose : Bool)
    (history : (nativeModel bounds).InformationHistory owner
      (some ((secondDecisionExecution disclose).recall owner,
        (secondDecisionExecution disclose).observe app owner))) :
    ∃ execution : app.Execution,
      history.1.state = some ⟨4, some owner, execution⟩ ∧
      execution.environmentRecall.length = 6 ∧
      some (execution.recall owner, execution.observe app owner) =
        some ((secondDecisionExecution disclose).recall owner,
          (secondDecisionExecution disclose).observe app owner) := by
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
        change control.execution.application.clock =
          (secondDecisionExecution disclose).application.clock at actualClock
        rw [second_decision_application] at actualClock
        change control.execution.application.clock = 1 at actualClock
        have traced : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).Trace
            (some control) := current ▸ history.1.trace
        have phase := phase_history
          ((nativeMenu bounds).toRawTrace (initialLaw setup) horizon scheduler traced)
        have position : control.execution.environmentRecall.length = 6 := by
          rcases phase.activation (by rw [active]; rfl) with first | second
          · have clock := phase.clock
            rw [first] at clock
            change control.execution.application.clock = 0 at clock
            omega
          · exact second
        have remaining : control.remaining = 4 := by
          have budget := phase.budget
          rw [position] at budget
          change control.remaining + 6 = 10 at budget
          omega
        refine ⟨control.execution, ?_, position, observed⟩
        cases control
        dsimp only at active remaining ⊢
        rw [active, remaining]
      · cases observed

/-- Once either first decision is recorded, the remaining native menu forces
silence and all whole-policy continuations have identical realized values. -/
theorem second_decision_locally_optimal (bounds : MessageBounds nativeGraph)
    (disclose : Bool) (site : (nativeModel bounds).InformationSite owner)
    (atSite : site.1 = some ((secondDecisionExecution disclose).recall owner,
      (secondDecisionExecution disclose).observe app owner))
    (assessment : (nativeModel bounds).BehavioralAssessment)
    (payoff : app.ProtocolState → ℝ) :
    Context.IsLocallyOptimal
      (assessment.truncatedContinuationContext site (fun final => payoff final.state) 21)
      Set.univ (assessment.strategy owner) := by
  refine (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _)
    (fun _ _ => payoffIntegrable_of_finite _ _)).mpr fun alternative _ => ?_
  apply le_of_eq
  rw [InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
    InformationModel.BehavioralAssessment.truncatedContinuationContext_value,
    Profile.update_eq_self, expect_bind_of_finite, expect_bind_of_finite]
  apply expect_congr_on_support
  intro history _
  let actual : (nativeModel bounds).InformationHistory owner
      (some ((secondDecisionExecution disclose).recall owner,
        (secondDecisionExecution disclose).observe app owner)) :=
    ⟨history.1, history.2.trans atSite⟩
  obtain ⟨execution, current, position, observed⟩ :=
    second_decision_information_resources bounds disclose actual
  have chosen (profile : ∀ who, (nativeModel bounds).BehavioralPolicy who) :
      (profile owner (some (execution.recall owner, execution.observe app owner))).map
        Subtype.val = PMF.pure (some (⟨none⟩ : app.Action)) := by
    rw [observed]
    exact second_decision_choice_law bounds disclose _
  rw [late_native_response_value bounds _ history.1 execution current position ⟨none⟩
      (chosen _) payoff,
    late_native_response_value bounds _ history.1 execution current position ⟨none⟩
      (chosen _) payoff]

end Vegas.LateResolutionService
