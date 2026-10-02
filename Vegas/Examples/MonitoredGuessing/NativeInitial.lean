/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeSanctions
import Vegas.Examples.MonitoredGuessing.NativeSchedule
import Interaction.ReactiveAssessmentEvaluation
import Interaction.ReactiveScheduleClock
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Alice's private initial native decisions

The initial bit remains private information. Each type has its own initial
decision site, and every permitted initial response is silence or one raw
submission subject to the passive monitor.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

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
  ⟨11, some alice, aliceActivated bit⟩

theorem initial_alice_trace (bit : Bool) :
    Nonempty (nativeArena.Trace (some (initialAliceControl bit))) := by
  obtain ⟨initial⟩ := native_initial_trace bit
  exact nativeMenu.trace_environment nativeInitialLaw nativeHorizon nativeScheduler 11
    (nativeStart bit) (aliceActivated bit) (.activate alice) initial (by
      change _ ∈ (PMF.pure (.activate alice : nativeApp.Command)).support
      exact (PMF.mem_support_pure_iff _ _).mpr rfl) (by
      rw [initial_activation]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)

def initialAliceSite (bit : Bool) : nativeModel.InformationSite alice := by
  let trace := (initial_alice_trace bit).some
  have information : nativeModel.infoOf alice trace =
      some ([], (aliceActivated bit).observe nativeApp alice) := by
    exact nativeMenu.info nativeInitialLaw nativeHorizon nativeScheduler alice trace
  refine ⟨some ([], (aliceActivated bit).observe nativeApp alice),
    ⟨⟨⟨some (initialAliceControl bit), trace⟩, information⟩, ?_, ?_⟩⟩
  · change ¬ (11 = 0 ∧ (some alice : Option Player) = none)
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
  | player who | sample event | tick | expire event =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rfl
  | includeLatest event owner =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      unfold reactiveLatest
      split <;> rfl
  | wire =>
      simp only [interactionInstruction, nativeNetwork, PMF.pure_map] at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rfl

theorem native_alice_activation_positions (history : List nativeApp.EnvironmentEntry)
    (view : nativeApp.EnvironmentView) (command : nativeApp.Command)
    (supported : command ∈ (nativeScheduler history view).support)
    (active : command.actor? nativeApp = some alice) :
    history.length = 0 ∨ history.length = 7 := by
  unfold nativeScheduler at supported
  cases selected : nativePlan[history.length]? with
  | none =>
      simp only [selected, PMF.mem_support_pure_iff _ _] at supported
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
            index.val = 0 ∨ index.val = 7 := by decide
      apply table ⟨history.length, bounded⟩
      rw [selected]
      exact actor

theorem native_alice_calendar (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some alice) :
    (control.execution.environmentRecall.length = 1 ∧ control.remaining = 11) ∨
      (control.execution.environmentRecall.length = 8 ∧ control.remaining = 4) := by
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

/-- The scheduler activates exactly the player of the plan instruction at the
current environment position. -/
theorem native_scheduled_actor (history : List nativeApp.EnvironmentEntry)
    (view : nativeApp.EnvironmentView) (command : nativeApp.Command)
    (supported : command ∈ (nativeScheduler history view).support) :
    command.actor? nativeApp = ((nativePlan.map instructionPlayer)[history.length]?).join := by
  unfold nativeScheduler at supported
  rw [List.getElem?_map]
  cases selected : nativePlan[history.length]? with
  | none =>
      rw [selected, PMF.mem_support_pure_iff _ _] at supported
      subst command
      rfl
  | some instruction =>
      rw [selected] at supported
      exact native_instruction_actor_eq history view instruction command supported

/-- Alice's second decision follows her first recorded response: her own recall
distinguishes her two decision sites, with no service announcement. -/
theorem native_alice_final_recall (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some alice)
    (late : control.execution.environmentRecall.length = 8) :
    (control.execution.recall alice).length = 1 := by
  obtain ⟨position, atPosition, _, counts, _⟩ := nativeApp.scheduled_decision_counts
    nativeInitialLaw nativeHorizon nativeScheduler (nativePlan.map instructionPlayer)
    native_scheduled_actor alice control (nativeMenu.toRawTrace _ _ _ trace) active
  have seven : position = 7 := by omega
  subst position
  have counted := counts alice
  have aliceCount : ((nativePlan.map instructionPlayer).take 8).count (some alice) = 2 := by
    decide
  simp only [↓reduceIte, aliceCount] at counted
  omega

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
        (PMF.uniformOfFintype Bool).map nativeStart := by
    simp only [ReactiveApplication.roundsFrom, ReactiveApplication.runRounds, nativeInitialLaw,
      ← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
    rfl
  rw [roots] at priorMem
  obtain ⟨bit, _, same⟩ := PMF.support_map .. ▸ priorMem
  subst prior
  have commandEq : command = .activate alice := by
    cases command with
    | activate who => cases Option.some.inj actor; rfl
    | «include» id | application command | wait => cases actor
  subst command
  rw [initial_activation, PMF.mem_support_pure_iff _ _] at observed
  have remaining : control.remaining = 11 := by
    rw [native_horizon] at accounted
    omega
  exact ⟨bit, by cases control; simp_all [initialAliceControl]⟩

theorem initial_alice_information_control (bit : Bool)
    (history : nativeModel.InformationHistory alice (initialAliceSite bit).1) :
    history.1.state = some (initialAliceControl bit) := by
  obtain ⟨control, stateEq, active, recallEq, observed⟩ := native_information_control alice []
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
  · have recalled := native_alice_final_recall control trace active late.1
    rw [recallEq] at recalled
    cases recalled

theorem initial_alice_finish (players : Player → nativeApp.Policy) (bit : Bool) :
    nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players
      (some (initialAliceControl bit)) =
      (players alice [] ((aliceActivated bit).observe nativeApp alice)).bind (fun response =>
        (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork nativePlan.tail
          (ambientRespond bit response)).map nativeApp.finished) :=
  native_finish_response players [] nativePlan.tail alice rfl (aliceActivated bit) rfl

def initialResponseValue (charge : ℝ) (players : Player → nativeApp.Policy)
    (bit : Bool) (response : nativeApp.Action) : ℝ :=
  expect (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork nativePlan.tail
    (ambientRespond bit response)) (nativeComparisonExecutionUtility charge alice)

theorem initial_alice_finish_value (charge : ℝ) (players : Player → nativeApp.Policy)
    (bit : Bool) :
    expect (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players
      (some (initialAliceControl bit))) (nativeComparisonUtility charge alice) =
      expect (players alice [] ((aliceActivated bit).observe nativeApp alice))
        (initialResponseValue charge players bit) := by
  rw [initial_alice_finish, expect_bind_tower _ _ _
    (payoffIntegrable_of_bounded _ _ (nativeComparisonUtility_abs_le charge alice))]
  apply expect_congr_on_support
  intro response _
  rw [expect_map]
  rfl

theorem initial_alice_context_value (charge : ℝ)
    (assessment : nativeModel.BehavioralAssessment) (bit : Bool)
    (alternative : nativeModel.BehavioralPolicy alice) :
    (assessment.truncatedContinuationContext (initialAliceSite bit)
      (fun history => nativeComparisonUtility charge alice history.state)
        (2 * nativeHorizon + 1)).value alternative =
      let players := nativeMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler
        (Profile.update (sig := nativeModel.behavioralSignature)
          assessment.strategy alice alternative)
      expect (players alice [] ((aliceActivated bit).observe nativeApp alice))
        (initialResponseValue charge players bit) := by
  rw [nativeMenu.context_value_of_known_state nativeInitialLaw nativeHorizon nativeScheduler
    assessment alice (initialAliceSite bit) (nativeComparisonUtility charge alice) alternative
      (some (initialAliceControl bit)) (initial_alice_information_control bit)]
  exact initial_alice_finish_value charge _ bit

theorem initial_submission_value_le (charge : ℝ) (nonnegative : 0 ≤ charge)
    (players : Player → nativeApp.Policy) (reports : players watcher = nativeWatcherPolicy)
    (bit : Bool) (submission : WitnessedSubmission nativeGraph) :
    initialResponseValue charge players bit (submissionAction submission) ≤ 1 - charge / 2 := by
  unfold initialResponseValue
  rw [show nativePlan.tail = [.player watcher, .wire] ++ nativePlan.drop 3 from rfl,
    runInteractionPlan_append, monitoring_plan players reports]
  exact submitted_continuation_utility_le bit submission charge nonnegative players _

theorem initial_submission_value_nonpositive (charge : ℝ) (sufficient : 2 ≤ charge)
    (players : Player → nativeApp.Policy) (reports : players watcher = nativeWatcherPolicy)
    (bit : Bool) (submission : WitnessedSubmission nativeGraph) :
    initialResponseValue charge players bit (submissionAction submission) ≤ 0 := by
  have bound := initial_submission_value_le charge (by linarith) players reports bit submission
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
      ∃ past view, site.1 = some (past, view) ∧ past.length = 1 := by
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
    rw [← recalled]
    exact native_alice_final_recall control trace active late.1

end Vegas.Examples.MonitoredGuessing
