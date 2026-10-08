/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommittedResolutionService
import Vegas.Pending.ReactiveAsyncRefinement
import Vegas.Pending.ReactiveRiskMenu
import Interaction.ReactivePolicyInvariant

/-! # Accepted recovery outside the protected inclusion window

The concrete source fixture admits a deterministic late inclusion scheduler.
Its first late canonical opening is accepted and has a clean final packet
verdict. This is an operational boundary for deriving a positive late-failure
floor from the asynchronous contract; it is not an equilibrium impossibility.
-/

noncomputable section

namespace Vegas.Examples.CommittedResolutionRecovery

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open CommittedResolutionService

/-- Always include the late packet at the fixture's randomized inclusion turn. -/
def scheduler : app.Scheduler := fun past view =>
  if past.length = 5 then
    PMF.pure ((runtime setup).reactiveLatest leaks aliceEvent alice view)
  else CommittedResolutionService.scheduler past view

/-- The controller only removes a supported discretionary wait branch. -/
theorem scheduler_support_subset (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) :
    (scheduler past view).support ⊆ (CommittedResolutionService.scheduler past view).support := by
  intro command selected
  by_cases late : past.length = 5
  · simp only [scheduler, late, ↓reduceIte, PMF.mem_support_pure_iff] at selected
    subst command
    change (runtime setup).reactiveLatest leaks aliceEvent alice view ∈
      (stageChoice past.length view).support
    rw [late]
    exact mem_support_mix_left (3 / 4) (by norm_num) (by norm_num)
      (by norm_num) (by simp)
  · simpa only [scheduler, late, ↓reduceIte] using selected

/-- The concrete all-history service contract survives deterministic recovery. -/
theorem contract :
    AsyncContract (runtime setup) leaks (initialLaw setup)
      CommittedResolutionService.horizon scheduler delay bound :=
  AsyncContract.of_scheduler_support_subset (runtime setup) leaks (initialLaw setup)
    CommittedResolutionService.horizon scheduler CommittedResolutionService.scheduler
      scheduler_support_subset delay bound
      CommittedResolutionService.contract

instance finiteNature : app.FiniteNature (initialLaw setup) scheduler :=
  app.finiteNature_of_scheduler_support_subset (initialLaw setup) scheduler
    CommittedResolutionService.scheduler scheduler_support_subset

private def initialExecution : app.Execution :=
  ReactiveApplication.Execution.initial app
    (State.initial (setup.eventInputs (sourceInitial true)))

private def sampledState : app.State :=
  initialExecution.application.complete sampleEvent (by decide) PUnit.unit true

private def recorded (execution : app.Execution) (command : app.Command)
    (state : app.State) : app.Execution :=
  { execution with application := state, environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, command⟩] }

private theorem sampled_initial :
    EventGraphRuntime.environmentStep (runtime setup) initialExecution.application
      (.executeSample sampleEvent) = PMF.pure sampledState := by
  rw [environmentStep_executeSample_eq (runtime setup) _ sampleEvent (by decide)
    .bool _ rfl rfl rfl]
  rw [Config.step_eq_map_of_eval _ sampleEvent _ _ (PMF.pure true) (by
    change some (RationalLaw.pure true).denote = some (PMF.pure true)
    congr 1
    unfold RationalLaw.denote
    have value : (RationalLaw.pure true).entryValue = fun _ => true := by
      funext index
      fin_cases index
      rfl
    rw [value]
    exact PMF.map_const _ _)]
  simp only [PMF.pure_map]
  rfl

private theorem recorded_application (execution : app.Execution)
    (command : EnvironmentCommand nativeGraph) (state : app.State)
    (moved : EventGraphRuntime.environmentStep (runtime setup) execution.application command =
      PMF.pure state) :
    execution.environmentStep app (.application command) =
      PMF.pure (recorded execution (.application command) state) := by
  simp only [ReactiveApplication.Execution.environmentStep]
  change ((EventGraphRuntime.environmentStep (runtime setup) execution.application command).map
    (fun state => { execution with application := state })).map _ = _
  rw [moved, PMF.pure_map, PMF.pure_map]
  rfl

private theorem recorded_activation (execution : app.Execution) (who : Player) :
    execution.environmentStep app (.activate who) =
      PMF.pure (recorded execution (.activate who) execution.application) := by
  simp only [ReactiveApplication.Execution.environmentStep]
  change ((PMF.pure (∅ : Finset (MessageId Player))).map
    (fun selected => { execution with network := execution.network.learn who selected })).map _ = _
  rw [PMF.pure_map, PMF.pure_map, MessageNetwork.learn_empty]
  rfl

private theorem recorded_wait (execution : app.Execution) :
    execution.environmentStep app .wait =
      PMF.pure (recorded execution .wait execution.application) := by
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  rfl

private theorem fixed_round (players : Player → app.Policy)
    (execution next : app.Execution) (position : Nat) (command : app.Command)
    (cursor : execution.environmentRecall.length = position) (notLate : position ≠ 5)
    (chosen : stageChoice position (execution.observeEnvironment app) = PMF.pure command)
    (moved : execution.environmentStep app command = PMF.pure next) :
    app.round scheduler players execution = app.resume players (command.actor? app) next := by
  rw [ReactiveApplication.round, scheduler, cursor, ite_eq_right notLate,
    CommittedResolutionService.scheduler, cursor, chosen, PMF.pure_bind,
    ReactiveApplication.dispatch, moved, PMF.pure_bind]

/-- The second Alice activation, following one silent response and one clock tick. -/
def lateExecution : app.Execution :=
  let sampled := recorded initialExecution (.application (.executeSample sampleEvent)) sampledState
  let first := recorded sampled (.activate alice) sampled.application
  let silent := first.respond app alice ⟨none⟩
  let waited := recorded silent .wait silent.application
  let ticked := recorded waited (.application .advanceClock)
    { waited.application with clock := 1 }
  recorded ticked (.activate alice) ticked.application

private def candidate : Handle nativeGraph := (alice, .initial ⟨0, by decide⟩)

/-- The ordinary certified opening of Alice's immutable initial binding. -/
def opening : WitnessedSubmission nativeGraph :=
  disclosureSubmission (.opening aliceEvent candidate ⟨.bool, true⟩)

/-- The packet that this actual submission emits. -/
def openingMessage : Message Player (WitnessedPacket nativeGraph) :=
  ⟨(alice, 0), ⟨.opening aliceEvent candidate ⟨.bool, true⟩,
    some ⟨candidate, ⟨.bool, true⟩⟩, some ⟨aliceEvent⟩⟩⟩

/-- Alice waits at her first activation, sends at her second, and then remains silent. -/
def latePlayers : Player → app.Policy := fun who past _ =>
  PMF.pure (if who = alice ∧ past.length = 1 then ⟨some opening⟩ else ⟨none⟩)

/-- The late response is reached from the fixture's genuine initialized source state. -/
theorem late_response_reached :
    app.runRounds scheduler latePlayers 5 initialExecution =
      PMF.pure (lateExecution.respond app alice ⟨some opening⟩) := by
  let e0 := initialExecution
  let e1 := recorded e0 (.application (.executeSample sampleEvent)) sampledState
  let p0 := recorded e1 (.activate alice) e1.application
  let e2 := p0.respond app alice ⟨none⟩
  let e3 := recorded e2 .wait e2.application
  let e4 := recorded e3 (.application .advanceClock) { e3.application with clock := 1 }
  have s0 : app.round scheduler latePlayers e0 = PMF.pure e1 := by
    rw [fixed_round latePlayers e0 e1 0 (.application (.executeSample sampleEvent))
      rfl (by decide) rfl (recorded_application e0 _ _ sampled_initial)]
    rfl
  have s1 : app.round scheduler latePlayers e1 = PMF.pure e2 := by
    rw [fixed_round latePlayers e1 p0 1 (.activate alice) rfl (by decide) rfl
      (recorded_activation e1 alice)]
    simp only [ReactiveApplication.resume, ReactiveApplication.invoke, latePlayers,
      PMF.pure_map]
    rfl
  have s2 : app.round scheduler latePlayers e2 = PMF.pure e3 := by
    rw [fixed_round latePlayers e2 e3 2 .wait rfl (by decide) rfl (recorded_wait e2)]
    rfl
  have s3 : app.round scheduler latePlayers e3 = PMF.pure e4 := by
    rw [fixed_round latePlayers e3 e4 3 (.application .advanceClock) rfl (by decide) rfl
      (recorded_application e3 _ _ rfl)]
    rfl
  have s4 : app.round scheduler latePlayers e4 =
      PMF.pure (lateExecution.respond app alice ⟨some opening⟩) := by
    rw [fixed_round latePlayers e4 lateExecution 4 (.activate alice) rfl (by decide) rfl
      (recorded_activation e4 alice)]
    simp only [ReactiveApplication.resume, ReactiveApplication.invoke, latePlayers,
      PMF.pure_map]
    rfl
  change app.runRounds scheduler latePlayers 5 e0 = _
  simp only [ReactiveApplication.runRounds, s0, s1, s2, s3, s4, PMF.pure_bind]

/-- Inclusion is still legal, although its promised bound no longer fits. -/
theorem late_window :
    lateExecution.application.publicView.WithinDeadline (runtime setup) aliceEvent ∧
      ¬ lateExecution.application.publicView.InclusionFitsDeadline (runtime setup) bound
        aliceEvent := by
  constructor
  · change 1 - 0 < 2
    decide
  · change ¬ (1 - 0 + 1 < 2)
    decide

/-- The standard source disclosure response is precisely the late opening. -/
theorem canonical_late_response :
    (runtime setup).canonicalServiceDecision leaks alice (lateExecution.recall alice)
      (lateExecution.observe app alice) aliceEvent true = ⟨some opening⟩ := by
  let binding : FieldRef nativeGraph.layout (.binding alice .bool) := ⟨.inl ⟨0, by decide⟩, rfl⟩
  have fixed : lateExecution.application.candidates.lookup candidate = .openable ⟨.bool, true⟩ := by
    change (State.initial (setup.eventInputs (sourceInitial true))).candidates.lookup candidate = _
    exact State.initial_candidate_binding_success (graph := nativeGraph) _ _ alice .bool
      rfl true rfl
  have associated : lateExecution.application.accepted binding.field = some candidate := rfl
  have resolved : EventCode.resolveOutput? binding [] true
      lateExecution.application.config.store = some (.success true) := rfl
  rw [canonicalServiceDecision_eq_of_not_bind (runtime setup) leaks alice _ _ aliceEvent true
    (by intro owner payload outputEq codeEq; cases outputEq)]
  have result := (runtime setup).serviceDecision_successful_opening leaks lateExecution
    (by intro who; fin_cases who <;> rfl) alice aliceEvent .bool binding [] rfl rfl rfl
      candidate true associated rfl fixed resolved
  change (runtime setup).serviceDecision leaks alice (lateExecution.recall alice)
    (lateExecution.observe app alice) aliceEvent true = _ at result
  rw [result]
  change (⟨some (WitnessedSubmission.normalizeReactive alice
    (app.observePlayer lateExecution.application alice) []
    (disclosureSubmission (.opening aliceEvent candidate ⟨.bool, true⟩)))⟩ : app.Action) = _
  have localFixed : (app.observePlayer lateExecution.application alice).candidates candidate.2 =
      .openable ⟨.bool, true⟩ := fixed
  rw [disclosureSubmission_normalize_opening alice _ aliceEvent candidate ⟨.bool, true⟩
    rfl localFixed]
  rfl

/-- Emission preserves the authentic bit and the event-only readiness token. -/
theorem late_emission :
    app.packet (lateExecution.respond app alice ⟨some opening⟩).application alice
      (lateExecution.network.known alice) opening = openingMessage.payload := by
  change opening.emit lateExecution.application alice [] = _
  have fixed : lateExecution.application.candidates.lookup candidate = .openable ⟨.bool, true⟩ := by
    change (State.initial (setup.eventInputs (sourceInitial true))).candidates.lookup candidate = _
    exact State.initial_candidate_binding_success (graph := nativeGraph) _ _ alice .bool
      rfl true rfl
  have verified := (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr fixed
  have token : lateExecution.application.publicView.tokenFor
      (.opening aliceEvent candidate ⟨.bool, true⟩) = some ⟨aliceEvent⟩ :=
    lateExecution.application.publicView_tokenFor_of_ready _ aliceEvent rfl (by decide)
  simp only [opening, disclosureSubmission, WitnessedSubmission.emit, verified, token]
  rfl

/-- The late response remains first-submission conformant under the actual packet rule. -/
theorem late_conformant :
    (runtime setup).ConformantResponse leaks alice (lateExecution.recall alice)
      (lateExecution.observe app alice) ⟨some opening⟩ := by
  refine ⟨opening, rfl, ?_, ?_⟩
  · rw [← canonical_late_response]
    exact (runtime setup).canonicalServiceDecision_firstSubmission leaks alice
      (lateExecution.recall alice) (lateExecution.observe app alice) aliceEvent true rfl
  · have emitted := late_emission
    change opening.emit lateExecution.application alice [] = openingMessage.payload at emitted
    have envelope : (runtime setup).localEnvelope leaks alice (lateExecution.recall alice)
        (lateExecution.observe app alice) opening = openingMessage := by
      change (⟨(alice, 0), opening.emit lateExecution.application alice []⟩ :
        Message Player (WitnessedPacket nativeGraph)) = _
      rw [emitted]
      rfl
    rw [envelope]
    let binding : FieldRef nativeGraph.layout (.binding alice .bool) := ⟨.inl ⟨0, by decide⟩, rfl⟩
    change (runtime setup).freshServiceEnvelope lateExecution.application.publicView
      openingMessage
    apply ((runtime setup).freshServiceEnvelope_opening_iff
      lateExecution.application.publicView (alice, 0) aliceEvent alice .bool binding []
        rfl rfl rfl candidate ⟨.bool, true⟩ (some ⟨candidate, ⟨.bool, true⟩⟩)
          (some ⟨aliceEvent⟩)).mpr
    refine ⟨by decide, by change 1 - 0 < 2; decide,
      by simp [certifiedOpening], ?_, rfl, rfl, rfl, rfl, rfl⟩
    exact (lateExecution.application.publicView.openingGuardsAccepted_iff alice aliceEvent
      .bool binding [] rfl rfl rfl candidate ⟨.bool, true⟩
        (some ⟨candidate, ⟨.bool, true⟩⟩)).mpr ⟨true, rfl, rfl⟩

/-- Bounded effective coverage retains this opening even though its guaranteed
inclusion window has closed. No protected-delivery gate is added. -/
theorem late_risk_retained (bounds : MessageBounds nativeGraph)
    (available : (⟨some opening⟩ : app.Action) ∈
      (bounds.menu (runtime setup) leaks).actions alice (lateExecution.recall alice)
        (lateExecution.observe app alice)) :
    (⟨some opening⟩ : app.Action) ∈
      (bounds.riskMenu (runtime setup) leaks bound).actions alice (lateExecution.recall alice)
        (lateExecution.observe app alice) := by
  classical
  change _ ∈ bounds.riskActions (runtime setup) leaks bound alice _ _
  by_cases risky : (runtime setup).serviceRisk leaks bound alice (lateExecution.recall alice)
      (lateExecution.observe app alice) = true
  · rw [bounds.riskActions_of_risk (runtime setup) leaks bound _ _ _ risky]
    exact available
  · have clear : (runtime setup).serviceRisk leaks bound alice (lateExecution.recall alice)
        (lateExecution.observe app alice) = false := Bool.eq_false_iff.mpr risky
    rw [bounds.riskActions_of_clear (runtime setup) leaks bound _ _ _ clear]
    apply Finset.mem_union_right
    exact (bounds.mem_conformantActions (runtime setup) leaks alice _ _ _).mpr
      ⟨available, late_conformant⟩

/-- The actual handler accepts the late opening before expiry. -/
theorem late_handle :
    app.handle (lateExecution.respond app alice ⟨some opening⟩).application openingMessage =
      some (lateExecution.application.complete aliceEvent (by decide) true (.success true)) := by
  let binding : FieldRef nativeGraph.layout (.binding alice .bool) := ⟨.inl ⟨0, by decide⟩, rfl⟩
  have fixed : lateExecution.application.candidates.lookup candidate = .openable ⟨.bool, true⟩ := by
    change (State.initial (setup.eventInputs (sourceInitial true))).candidates.lookup candidate = _
    exact State.initial_candidate_binding_success (graph := nativeGraph) _ _ alice .bool
      rfl true rfl
  rw [reactiveApplication_handle_of_tokenValid (runtime setup) leaks _ _ (by rfl)]
  exact (runtime setup).handle_opening_eq lateExecution.application _ aliceEvent candidate alice
    .bool binding [] rfl rfl rfl (by decide) (by change 1 - 0 < 2; decide)
    rfl rfl (by rfl) true fixed (by rfl) (.success true) (by rfl)

/-- The execution immediately after the scheduler accepts Alice's late opening. -/
def acceptedExecution : app.Execution :=
  let submitted := lateExecution.respond app alice ⟨some opening⟩
  { submitted.includePending app (alice, 0) with environmentRecall :=
      submitted.environmentRecall ++ [⟨submitted.observeEnvironment app, .include (alice, 0)⟩] }

/-- The controller's actual next round accepts the late packet with certainty. -/
theorem late_inclusion (players : Player → app.Policy) :
    app.round scheduler players (lateExecution.respond app alice ⟨some opening⟩) =
        PMF.pure acceptedExecution ∧
      acceptedExecution.application.config.store (.inr aliceEvent) = some (.success true) ∧
      (openingMessage.id, true) ∈ acceptedExecution.receipts ∧
      acceptedExecution.network.inputs = [openingMessage] := by
  let submitted := lateExecution.respond app alice ⟨some opening⟩
  have chosen : scheduler submitted.environmentRecall (submitted.observeEnvironment app) =
      PMF.pure (.include (alice, 0)) := by
    change (if 5 = 5 then _ else _) = _
    simp only [↓reduceIte]
    congr 1
  have included : (submitted.includePending app (alice, 0)).application =
      lateExecution.application.complete aliceEvent (by decide) true (.success true) := by
    change Option.getD (app.handle submitted.application ⟨(alice, 0),
      app.packet submitted.application alice (lateExecution.network.known alice) opening⟩)
      submitted.application = _
    rw [late_emission]
    change (app.handle submitted.application openingMessage).getD submitted.application = _
    rw [late_handle]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ReactiveApplication.round, chosen, PMF.pure_bind, ReactiveApplication.dispatch]
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.pure_bind, ReactiveApplication.Command.actor?, ReactiveApplication.resume]
    rfl
  · change (submitted.includePending app (alice, 0)).application.config.store _ = _
    rw [included]
    rfl
  · change (openingMessage.id, true) ∈ (submitted.includePending app (alice, 0)).receipts
    change (openingMessage.id, true) ∈ [(openingMessage.id, (app.handle submitted.application
      ⟨(alice, 0), app.packet submitted.application alice
        (lateExecution.network.known alice) opening⟩).isSome)]
    rw [late_emission]
    change (openingMessage.id, true) ∈
      [(openingMessage.id, (app.handle submitted.application openingMessage).isSome)]
    rw [late_handle]
    simp
  · change (submitted.includePending app (alice, 0)).network.inputs = _
    change submitted.network.inputs = _
    change ([⟨(alice, 0), app.packet submitted.application alice
      (lateExecution.network.known alice) opening⟩] : List (Message Player app.Payload)) = _
    rw [late_emission]
    rfl

/-- Empty guards make this packet's content permitted at every settled record. -/
theorem late_content (record : SettledRecord nativeGraph) :
    record.SettledContent openingMessage := by
  let binding : FieldRef nativeGraph.layout (.binding alice .bool) := ⟨.inl ⟨0, by decide⟩, rfl⟩
  refine ⟨by simp [openingMessage, certifiedOpening], ?_⟩
  exact (record.view.openingGuardsAccepted_iff alice aliceEvent .bool binding []
    rfl rfl rfl candidate ⟨.bool, true⟩ (some ⟨candidate, ⟨.bool, true⟩⟩)).mpr
      ⟨true, rfl, rfl⟩

/-- Acceptance suffices for final permission; the closed protected window is not read. -/
theorem late_permitted (record : SettledRecord nativeGraph)
    (accepted : (openingMessage.id, true) ∈ record.receipts) :
    record.permits openingMessage = true :=
  SettledRecord.permits_of_accepted record openingMessage aliceEvent rfl accepted
    (late_content record)

private def CleanRecovery (execution : app.Execution) : Prop :=
  2 ≤ (execution.recall alice).length ∧
    execution.network.inputs = [openingMessage] ∧
    (openingMessage.id, true) ∈ execution.receipts

private theorem recovery_invariant : app.PolicyInvariant latePlayers CleanRecovery where
  respond execution who action valid supported := by
    have never : ¬ (who = alice ∧ (execution.recall who).length = 1) := by
      rintro ⟨rfl, length⟩
      have enough := valid.1
      omega
    have silent : action = ⟨none⟩ := by
      simpa only [latePlayers, ite_eq_right never, PMF.mem_support_pure_iff] using supported
    subst action
    refine ⟨?_, valid.2.1, valid.2.2⟩
    by_cases same : alice = who
    · subst who
      change 2 ≤ (execution.recall alice ++ [_]).length
      simp only [List.length_append, List.length_singleton]
      have enough := valid.1
      omega
    · rw [app.respond_recall_other execution who alice same]
      exact valid.1
  environment execution next command valid reached := by
    refine ⟨?_, ?_, ?_⟩
    · rw [app.environmentStep_recall execution next command reached]
      exact valid.1
    · rw [app.environmentStep_inputs execution next command reached]
      exact valid.2.1
    · exact (app.environmentStep_receipts_prefix execution next command reached).subset valid.2.2

/-- The only envelope throughout the terminal continuation is Alice's accepted late opening. -/
theorem recovery_record (execution : app.Execution)
    (reached : execution ∈ (app.runRounds scheduler latePlayers
      CommittedResolutionService.horizon initialExecution).support) :
    execution.network.inputs = [openingMessage] ∧
      (openingMessage.id, true) ∈ execution.receipts := by
  have firstSix : app.runRounds scheduler latePlayers 6 initialExecution =
      PMF.pure acceptedExecution := by
    change app.runRounds scheduler latePlayers (5 + 1) initialExecution = _
    rw [app.runRounds_add, late_response_reached, PMF.pure_bind]
    simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using (late_inclusion latePlayers).1
  change execution ∈ (app.runRounds scheduler latePlayers (6 + 10) initialExecution).support
    at reached
  rw [app.runRounds_add, firstSix, PMF.pure_bind] at reached
  have beginning : CleanRecovery acceptedExecution :=
    ⟨by decide, (late_inclusion latePlayers).2.2.2, (late_inclusion latePlayers).2.2.1⟩
  have final := recovery_invariant.runRounds scheduler 10 acceptedExecution execution
    beginning reached
  exact final.2

/-- No continuation of the specified policy adds another envelope or loses the receipt. -/
theorem recovery_packets_clean (execution : app.Execution)
    (reached : execution ∈ (app.runRounds scheduler latePlayers
      CommittedResolutionService.horizon initialExecution).support) :
    ∀ input ∈ execution.network.inputs,
      ((runtime setup).settledRecord leaks execution).permits input = true := by
  have final := recovery_record execution reached
  intro input member
  rw [final.1, List.mem_singleton] at member
  subst input
  exact late_permitted _ final.2

private theorem initialized_true : initialExecution.application ∈ (initialLaw setup).support := by
  rw [initialLaw, serviceInitialLaw, PMF.support_map]
  refine ⟨sourceInitial true, ?_, rfl⟩
  exact mem_support_mix_left (1 / 4) (by norm_num) (by norm_num)
    (by norm_num) (by simp)

/-- Authentic audit sampling collects nothing after the actual accepted late opening,
regardless of the escrow size or the game's base utility. -/
theorem recovery_settlement (execution : app.Execution)
    (reached : execution ∈ (app.runRounds scheduler latePlayers
      CommittedResolutionService.horizon initialExecution).support)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (base : app.ProtocolState → Player → ℝ) (deposit : Player → ℝ) :
    TerminalAudit.settlement base ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) deposit (some ⟨0, none, execution⟩) =
        PMF.pure (base (some ⟨0, none, execution⟩)) := by
  have physical : execution ∈ (app.roundsFrom (initialLaw setup) scheduler latePlayers
      CommittedResolutionService.horizon).support := by
    rw [ReactiveApplication.roundsFrom, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨initialExecution.application, initialized_true, reached⟩
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup)
    CommittedResolutionService.horizon scheduler latePlayers
      CommittedResolutionService.horizon le_rfl execution physical
  simp only [Nat.sub_self] at trace
  apply TerminalAudit.settlement_clean
  intro who
  have noOmission := execution.application.publicView.missedBindingBy_of_publications
    (by
      intro event owner payload
      fin_cases event <;> intro incompatible <;> cases incompatible) who
  unfold sourceServiceAudit serviceSourceAudit
  rw [(runtime setup).serviceAudit_charge, noOmission]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply app.sampledTrafficAudit_sound
  · exact authentic _
  · intro record member _
    have inputs := app.stateTraffic_inputs (initialLaw setup)
      CommittedResolutionService.horizon scheduler trace
    change (app.executionTraffic execution).map ReactiveApplication.TrafficRecord.envelope =
      execution.network.inputs at inputs
    have present : record.envelope ∈ execution.network.inputs := by
      rw [← inputs]
      exact List.mem_map.mpr ⟨record, member, rfl⟩
    exact recovery_packets_clean execution reached record.envelope present

/-- The accepted late submission has an actual initialized terminal continuation,
and every authentic audit backend leaves its entire payoff vector unchanged. -/
theorem initialized_clean_recovery :
    ∃ execution ∈ (app.roundsFrom (initialLaw setup) scheduler latePlayers
      CommittedResolutionService.horizon).support,
      execution.network.inputs = [openingMessage] ∧
        (openingMessage.id, true) ∈ execution.receipts ∧
      ∀ (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup))),
        (∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) →
        ∀ (base : app.ProtocolState → Player → ℝ) (deposit : Player → ℝ),
          TerminalAudit.settlement base ((runtime setup).serviceAuditObservation leaks)
            (sourceServiceAudit setup leaks sample) deposit (some ⟨0, none, execution⟩) =
              PMF.pure (base (some ⟨0, none, execution⟩)) := by
  obtain ⟨execution, reached⟩ := (app.runRounds scheduler latePlayers
    CommittedResolutionService.horizon initialExecution).support_nonempty
  refine ⟨execution, ?_, (recovery_record execution reached).1,
    (recovery_record execution reached).2, fun sample authentic base deposit =>
    recovery_settlement execution reached sample authentic base deposit⟩
  rw [ReactiveApplication.roundsFrom, PMF.support_bind]
  exact Set.mem_iUnion₂.mpr ⟨initialExecution.application, initialized_true, reached⟩

end Vegas.Examples.CommittedResolutionRecovery
