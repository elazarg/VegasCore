/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativeSanctions
import VegasTests.MonitoredGuessingNativeSchedule
import Interaction.ReactiveAssessmentEvaluation

/-! # Alice's private initial native decisions

The initial bit remains private information. Each type has its own initial
decision site, and every permitted initial response is silence or one raw
submission subject to the passive monitor.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem native_information_control (who : Player) (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView)
    (history : nativeModel.InformationHistory who (some (past, view))) :
    ∃ control, history.1.state = some control ∧ control.actor = some who ∧
      control.execution.recall who = past ∧ control.execution.observe nativeApp who = view := by
  rcases history with ⟨⟨state, trace⟩, information⟩
  change (nativeMenu.signals nativeInitialLaw nativeHorizon nativeScheduler).infoOf who trace =
    some (past, view) at information
  rw [nativeMenu.info] at information
  cases state with
  | none => cases information
  | some control =>
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at information
        exact ⟨control, rfl, active, congrArg Prod.fst (Option.some.inj information),
          congrArg Prod.snd (Option.some.inj information)⟩
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at information
        cases information

def initialAliceControl (bit : Bool) : nativeApp.Control :=
  ⟨13, some alice, aliceActivated bit⟩

theorem initial_alice_trace (bit : Bool) :
    Nonempty (nativeArena.Trace (some (initialAliceControl bit))) := by
  obtain ⟨initial⟩ := native_initial_trace bit
  exact nativeMenu.trace_environment nativeInitialLaw nativeHorizon nativeScheduler 13
    (nativeStart bit) (aliceActivated bit) (.activate alice) initial (by
      change _ ∈ (FinDist.pure (.activate alice : nativeApp.Command)).support
      exact FinDist.mem_support_pure.mpr rfl) (by
      rw [initial_activation]
      exact FinDist.mem_support_pure.mpr rfl)

def initialAliceSite (bit : Bool) : nativeModel.InformationSite alice := by
  let trace := (initial_alice_trace bit).some
  have information : nativeModel.infoOf alice trace =
      some ([], (aliceActivated bit).observe nativeApp alice) := by
    exact nativeMenu.info nativeInitialLaw nativeHorizon nativeScheduler alice trace
  refine ⟨some ([], (aliceActivated bit).observe nativeApp alice),
    ⟨⟨⟨some (initialAliceControl bit), trace⟩, information⟩, ?_, ?_⟩⟩
  · change ¬ (13 = 0 ∧ (some alice : Option Player) = none)
    simp
  · exact ⟨nativeSilent, nativeSilent, native_silent_available _ _ _, rfl⟩

theorem initial_alice_observed_bit (bit : Bool) :
    observedAliceBit ((aliceActivated bit).observe nativeApp alice) = bit := by
  cases bit <;> rfl

theorem initial_alice_site_injective : Function.Injective initialAliceSite := by
  intro left right equal
  have info := congrArg Subtype.val equal
  have observation := congrArg Prod.snd (Option.some.inj info)
  have bit := congrArg observedAliceBit observation
  simpa only [initial_alice_observed_bit] using bit

def instructionPlayer : ServiceInstruction nativeGraph → Option Player
  | .player who => some who
  | _ => none

theorem native_instruction_actor_eq (history : List nativeApp.EnvironmentEntry)
    (view : nativeApp.EnvironmentView) (instruction : ServiceInstruction nativeGraph)
    (command : nativeApp.Command)
    (supported : command ∈ (nativeRuntime.interactionInstruction nativeLeaks nativeNetwork
      history view instruction).support) :
    command.actor? nativeApp = instructionPlayer instruction := by
  cases instruction with
  | player who | grant event | sample event | tick | expire event =>
      cases FinDist.mem_support_pure.mp supported
      rfl
  | includeLatest event owner =>
      cases FinDist.mem_support_pure.mp supported
      unfold reactiveLatest
      split <;> rfl
  | wire =>
      change command ∈ ((FinDist.pure (match view.network.inputs.getLast? with
        | none => NetworkChoice.wait
        | some input => if input.broadcaster = watcher ∧ input.envelope.sender = alice then
            NetworkChoice.include input.envelope.id else NetworkChoice.wait)).map
              (fun choice => nativeApp.atMostOnceCommand view
                (choice.command nativeRuntime nativeLeaks))).support at supported
      rw [FinDist.map_pure, FinDist.mem_support_pure] at supported
      subst command
      cases last : view.network.inputs.getLast? with
      | none =>
          simp only [NetworkChoice.command, ReactiveApplication.atMostOnceCommand]
          rfl
      | some input =>
          by_cases report : input.broadcaster = watcher ∧ input.envelope.sender = alice
          · simp only [ite_eq_left report, NetworkChoice.command]
            change (if view.Unpublished nativeApp input.envelope.id then
              ReactiveApplication.Command.include input.envelope.id else
                ReactiveApplication.Command.wait).actor? nativeApp = none
            split <;> rfl
          · simp only [ite_eq_right report, NetworkChoice.command,
              ReactiveApplication.atMostOnceCommand]
            rfl

theorem native_alice_activation_positions (history : List nativeApp.EnvironmentEntry)
    (view : nativeApp.EnvironmentView) (command : nativeApp.Command)
    (supported : command ∈ (nativeScheduler history view).support)
    (active : command.actor? nativeApp = some alice) :
    history.length = 0 ∨ history.length = 9 := by
  unfold nativeScheduler at supported
  cases selected : nativePlan[history.length]? with
  | none =>
      simp only [selected, FinDist.mem_support_pure] at supported
      subst command
      cases active
  | some instruction =>
      rw [selected] at supported
      have actor := (native_instruction_actor_eq history view instruction command supported).symm
        |>.trans active
      have bounded : history.length < nativePlan.length :=
        (List.getElem?_eq_some_iff.mp selected).1
      have table : ∀ index : Fin nativePlan.length,
          (nativePlan[index.val]?).bind instructionPlayer = some alice →
            index.val = 0 ∨ index.val = 9 := by decide
      apply table ⟨history.length, bounded⟩
      rw [selected]
      exact actor

theorem native_alice_calendar (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some alice) :
    (control.execution.environmentRecall.length = 1 ∧ control.remaining = 13) ∨
      (control.execution.environmentRecall.length = 10 ∧ control.remaining = 4) := by
  obtain ⟨accounted, supported⟩ := nativeMenu.roundSupported_uniform nativeInitialLaw
    nativeHorizon nativeScheduler trace
  rw [active] at supported
  obtain ⟨count, prior, command, position, priorMem, commandMem, actor, observed⟩ := supported
  have cursor := nativeApp.roundsFrom_recall nativeInitialLaw nativeScheduler
    nativeMenu.uniformResponses count prior priorMem
  have possible := native_alice_activation_positions prior.environmentRecall
    (prior.observeEnvironment nativeApp) command commandMem actor
  rw [cursor] at possible
  rw [native_horizon] at accounted
  rcases possible with initial | final
  · left; constructor <;> omega
  · right; constructor <;> omega

theorem native_rounds_grant (players : Player → nativeApp.Policy)
    (count : Nat) (bounded : count ≤ nativePlan.length)
    (before : List (ServiceInstruction nativeGraph)) (event : nativeGraph.EventId)
    (last : nativePlan.take count = before ++ [.grant event])
    (execution : nativeApp.Execution)
    (supported : execution ∈ (nativeApp.roundsFrom nativeInitialLaw nativeScheduler
      players count).support) : execution.application.serviceGrant = some event := by
  obtain ⟨state, stateMem, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨bit, _, rfl⟩ := FinDist.support_map .. ▸ stateMem
  have law := native_segment_rounds players [] (nativePlan.take count) (nativePlan.drop count)
    (by simp) (nativeStart bit) rfl
  rw [List.length_take_of_le bounded] at law
  change execution ∈ (nativeApp.runRounds nativeScheduler players count (nativeStart bit)).support
    at reached
  rw [law, last, runInteractionPlan_append] at reached
  obtain ⟨previous, _, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  have grantLaw : nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      [.grant event] previous =
        previous.environmentStep nativeApp (.application (.grant event)) := by
    simp only [runInteractionPlan, interactionStep, interactionInstruction,
      FinDist.pure_bind, FinDist.bind_pure, ReactiveApplication.dispatch]
    exact FinDist.bind_pure _
  rw [grantLaw] at moved
  simp only [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
    environmentStep, FinDist.map_pure, FinDist.mem_support_pure] at moved
  subst execution
  rfl

theorem native_alice_final_grant (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some alice)
    (late : control.execution.environmentRecall.length = 10) :
    control.execution.application.serviceGrant = some alicePublication := by
  obtain ⟨_, supported⟩ := nativeMenu.roundSupported_uniform nativeInitialLaw
    nativeHorizon nativeScheduler trace
  rw [active] at supported
  obtain ⟨count, prior, command, position, priorMem, _, actor, observed⟩ := supported
  have counted : count = 9 := by omega
  subst count
  have granted := native_rounds_grant nativeMenu.uniformResponses 9 (by decide)
    (nativePlan.take 8) alicePublication rfl prior priorMem
  have commandEq : command = .activate alice := by
    cases command with
    | activate who => cases Option.some.inj actor; rfl
    | «include» id | application command | wait => cases actor
  subst command
  obtain ⟨next, member, same⟩ := FinDist.support_map .. ▸ observed
  rw [← same]
  obtain ⟨selected, _, sameNext⟩ := FinDist.support_map .. ▸ member
  rw [← sameNext]
  exact granted

theorem native_alice_initial_representation (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some alice)
    (early : control.execution.environmentRecall.length = 1) :
    ∃ bit, control = initialAliceControl bit := by
  obtain ⟨accounted, supported⟩ := nativeMenu.roundSupported_uniform nativeInitialLaw
    nativeHorizon nativeScheduler trace
  rw [active] at supported
  obtain ⟨count, prior, command, position, priorMem, _, actor, observed⟩ := supported
  have counted : count = 0 := by omega
  subst count
  have roots : nativeApp.roundsFrom nativeInitialLaw nativeScheduler
      nativeMenu.uniformResponses 0 =
        (FinDist.uniformOfFintype (α := Bool)).map nativeStart := by
    simp only [ReactiveApplication.roundsFrom, ReactiveApplication.runRounds, nativeInitialLaw,
      ← FinDist.map_eq_bind, FinDist.map_comp]
    rfl
  rw [roots] at priorMem
  obtain ⟨bit, _, same⟩ := FinDist.support_map .. ▸ priorMem
  subst prior
  have commandEq : command = .activate alice := by
    cases command with
    | activate who => cases Option.some.inj actor; rfl
    | «include» id | application command | wait => cases actor
  subst command
  rw [initial_activation, FinDist.mem_support_pure] at observed
  have remaining : control.remaining = 13 := by
    rw [native_horizon] at accounted
    omega
  exact ⟨bit, by cases control; simp_all [initialAliceControl]⟩

theorem initial_alice_information_control (bit : Bool)
    (history : nativeModel.InformationHistory alice (initialAliceSite bit).1) :
    history.1.state = some (initialAliceControl bit) := by
  obtain ⟨control, stateEq, active, _, observed⟩ := native_information_control alice []
    ((aliceActivated bit).observe nativeApp alice) history
  rcases history with ⟨⟨state, trace⟩, information⟩
  change state = some control at stateEq
  subst state
  rcases native_alice_calendar control trace active with early | late
  · obtain ⟨actualBit, same⟩ := native_alice_initial_representation control trace active early.1
    subst control
    have bits := congrArg observedAliceBit observed
    have sameBit : actualBit = bit := by
      simpa only [initialAliceControl, initial_alice_observed_bit] using bits
    subst actualBit
    rfl
  · have granted := native_alice_final_grant control trace active late.1
    have viewed := congrArg (fun view : nativeApp.PlayerView =>
      view.application.publicView.serviceGrant) observed
    change control.execution.application.serviceGrant = none at viewed
    rw [granted] at viewed
    cases viewed

theorem initial_alice_finish (players : Player → nativeApp.Policy) (bit : Bool) :
    nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players
      (some (initialAliceControl bit)) =
      (players alice [] ((aliceActivated bit).observe nativeApp alice)).bind (fun response =>
        (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork nativePlan.tail
          (ambientRespond bit response)).map nativeApp.finished) :=
  native_finish_response players [] nativePlan.tail alice rfl (aliceActivated bit) rfl

def initialResponseValue (deposit : ℝ) (players : Player → nativeApp.Policy)
    (bit : Bool) (response : nativeApp.Action) : ℝ :=
  (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork nativePlan.tail
    (ambientRespond bit response)).expect (nativeExecutionUtility deposit alice)

theorem initial_alice_finish_value (deposit : ℝ) (players : Player → nativeApp.Policy)
    (bit : Bool) :
    (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players
      (some (initialAliceControl bit))).expect (nativeUtility deposit alice) =
      (players alice [] ((aliceActivated bit).observe nativeApp alice)).expect
        (initialResponseValue deposit players bit) := by
  rw [initial_alice_finish, FinDist.expect_bind]
  apply FinDist.expect_congr
  intro response _
  rw [FinDist.expect_map]
  rfl

theorem initial_alice_context_value (deposit : ℝ)
    (assessment : nativeModel.BehavioralAssessment) (bit : Bool)
    (alternative : nativeModel.BehavioralPolicy alice) :
    (assessment.continuationContext (initialAliceSite bit)
      (fun history => nativeUtility deposit alice history.state)
        (2 * nativeHorizon + 1)).value alternative =
      let players := nativeMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler
        (Profile.update (sig := nativeModel.behavioralSignature)
          assessment.strategy alice alternative)
      (players alice [] ((aliceActivated bit).observe nativeApp alice)).expect
        (initialResponseValue deposit players bit) := by
  rw [nativeMenu.context_value_of_known_state nativeInitialLaw nativeHorizon nativeScheduler
    assessment alice (initialAliceSite bit) (nativeUtility deposit alice) alternative
      (some (initialAliceControl bit)) (initial_alice_information_control bit)]
  exact initial_alice_finish_value deposit _ bit

theorem initial_submission_value_le (deposit : ℝ) (nonnegative : 0 ≤ deposit)
    (players : Player → nativeApp.Policy) (reports : players watcher = nativeWatcherPolicy)
    (bit : Bool) (submission : WitnessedSubmission nativeGraph) :
    initialResponseValue deposit players bit (submissionAction submission) ≤ 1 - deposit / 2 := by
  unfold initialResponseValue
  rw [show nativePlan.tail = [.player watcher, .wire] ++ nativePlan.drop 3 from rfl,
    runInteractionPlan_append, monitoring_plan players reports]
  exact submitted_continuation_utility_le bit submission deposit nonnegative players _

theorem initial_submission_value_nonpositive (deposit : ℝ) (sufficient : 2 ≤ deposit)
    (players : Player → nativeApp.Policy) (reports : players watcher = nativeWatcherPolicy)
    (bit : Bool) (submission : WitnessedSubmission nativeGraph) :
    initialResponseValue deposit players bit (submissionAction submission) ≤ 0 := by
  have bound := initial_submission_value_le deposit (by linarith) players reports bit submission
  linarith

theorem native_site_observation (who : Player) (site : nativeModel.InformationSite who) :
    ∃ past view, site.1 = some (past, view) := by
  obtain ⟨history, _, _⟩ := site.2
  have active := InformationModel.InformationSite.active nativeModel site history
  have observed := history.2
  change (nativeMenu.signals nativeInitialLaw nativeHorizon nativeScheduler).infoOf
    who history.1.trace = site.1 at observed
  rw [nativeMenu.info] at observed
  change nativeApp.actor history.1.state = some who at active
  cases stateEq : history.1.state with
  | none => rw [stateEq] at active; cases active
  | some control =>
      change history.1.state.bind ReactiveApplication.Control.actor = some who at active
      rw [stateEq] at active observed
      change control.actor = some who at active
      refine ⟨control.execution.recall who, control.execution.observe nativeApp who, ?_⟩
      simpa only [ReactiveApplication.observe, active, ↓reduceIte] using observed.symm

theorem native_alice_site_cases (site : nativeModel.InformationSite alice) :
    (∃ bit, site = initialAliceSite bit) ∨
      ∃ past view, site.1 = some (past, view) ∧
        view.application.publicView.serviceGrant = some alicePublication := by
  obtain ⟨past, view, viewed⟩ := native_site_observation alice site
  obtain ⟨history, _, _⟩ := site.2
  obtain ⟨control, stateEq, active, recalled, observed⟩ := native_information_control alice
    past view ⟨history.1, history.2.trans viewed⟩
  rcases history with ⟨⟨state, trace⟩, information⟩
  change state = some control at stateEq
  subst state
  rcases native_alice_calendar control trace active with early | late
  · obtain ⟨bit, same⟩ := native_alice_initial_representation control trace active early.1
    subst control
    left
    refine ⟨bit, Subtype.ext ?_⟩
    rw [viewed, ← recalled, ← observed]
    rfl
  · right
    refine ⟨past, view, viewed, ?_⟩
    rw [← observed]
    exact native_alice_final_grant control trace active late.1

end VegasTests.MonitoredGuessing
