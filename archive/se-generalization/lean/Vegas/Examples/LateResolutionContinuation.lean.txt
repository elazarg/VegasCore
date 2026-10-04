/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateResolutionService
import Vegas.Game.SourceServiceResolutionInclusionFactorization
import Vegas.Game.SourceServiceAudit
import Interaction.ReactiveRawRoundTrace
import Vegas.Game.SourceServiceReadout
import Vegas.Compile.EventGraphParameterReadout
import Vegas.Game.SourceServiceCanonicalSlots

/-! # Audited continuation values at a reachable late resolution

The initialized public service reaches a second owner turn after an earlier
silent response. Its authentic true opening and silence both remain unresolved
until public expiry, collecting the one-time escrow. Evidence-free withholding
is accepted and is uncharged by every authentic partial traffic audit.

The terminal typed utility is the source program's declared payoff. Every
turn-timing policy is forced silent at this late input by its protected gate,
so lawful withholding strictly improves its actual continuation for positive
escrow. This is a policy-completion obstruction; it does not establish a native
sequential-equilibrium counterexample or a failure of preservation.
-/

noncomputable section

namespace Vegas.LateResolutionService

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

theorem silent_resume_application (actor : Option Player) (execution next : app.Execution)
    (supported : next ∈ (app.resume (fun _ => app.silentPolicy) actor execution).support) :
    next.application = execution.application := by
  cases actor with
  | none =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rfl
  | some who =>
      obtain ⟨response, chosen, rfl⟩ := PMF.support_map .. ▸ supported
      have responseEq := app.silentPolicy_cases _ _ response chosen
      rw [responseEq]
      rfl

theorem silent_empty_network : app.PolicyInvariant (fun _ => app.silentPolicy)
    (fun execution => execution.network = .empty) where
  respond execution who response empty supported := by
    have responseEq := app.silentPolicy_cases _ _ response supported
    rw [responseEq]
    exact empty
  environment execution next command empty moved := by
    cases command with
    | application command =>
        obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
        obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ supported
        exact empty
    | wait =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
        cases (PMF.mem_support_pure_iff _ _).mp moved
        exact empty
    | «include» id =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
        cases (PMF.mem_support_pure_iff _ _).mp moved
        rw [app.includePending_network, empty]
        rfl
    | activate who =>
        obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
        obtain ⟨selected, chosen, rfl⟩ := PMF.support_map .. ▸ supported
        have selectedEq : selected = ∅ := (PMF.mem_support_pure_iff _ _).mp chosen
        change execution.network.learn who selected = .empty
        rw [selectedEq, MessageNetwork.learn_empty]
        exact empty

theorem silent_rounds_empty_network (count : Nat) (execution : app.Execution)
    (supported : execution ∈
      (app.roundsFrom (initialLaw setup) scheduler (fun _ => app.silentPolicy) count).support) :
    execution.network = .empty := by
  obtain ⟨state, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  exact silent_empty_network.runRounds scheduler count _ execution rfl reached

theorem sample_preserves_resolution_unfinished (before after : app.State)
    (event : nativeGraph.EventId) (different : event ≠ resolution)
    (unfinished : resolution ∉ before.config.cut.completed)
    (supported : after ∈ (environmentStep (runtime setup) before (.executeSample event)).support) :
    resolution ∉ after.config.cut.completed := by
  obtain ⟨_, effect⟩ :=
    environmentStep_executeSample_config_activated (runtime setup) before after event supported
  rcases effect with ⟨same, _⟩ | ⟨ready, action, reached, _⟩
  · simpa only [same] using unfinished
  · rw [before.config.step_cut event ready action after.config reached]
    simpa only [EventOrder.Cut.completed_complete, Finset.mem_insert, not_or] using
      And.intro (Ne.symm different) unfinished

theorem silent_rounds_unfinished (count : Nat) (bounded : count ≤ 5) (execution : app.Execution)
    (supported : execution ∈
      (app.roundsFrom (initialLaw setup) scheduler (fun _ => app.silentPolicy) count).support) :
    resolution ∉ execution.application.config.cut.completed := by
  induction count generalizing execution with
  | zero =>
      obtain ⟨state, stateMem, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      cases (PMF.mem_support_pure_iff _ _).mp reached
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ stateMem
      change resolution ∉ (∅ : Finset nativeGraph.EventId)
      simp
  | succ count ih =>
      rw [app.roundsFrom_succ (initialLaw setup) scheduler (fun _ => app.silentPolicy) count]
        at supported
      obtain ⟨before, prior, stepped⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      have unfinished := ih (by omega) before prior
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler
        (fun _ => app.silentPolicy) count (by dsimp [horizon]; omega) before prior
      have phase : Phase ⟨horizon - count, none, before⟩ := phase_history trace
      have position : before.environmentRecall.length = count := by
        have budget := phase.budget
        change (10 - count) + before.environmentRecall.length = 10 at budget
        omega
      obtain ⟨command, selected, dispatched⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ stepped)
      obtain ⟨middle, moved, resumed⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
      have chosen : command = stageCommand count (before.observeEnvironment app) := by
        have actual := (PMF.mem_support_pure_iff _ _).mp selected
        simpa only [position] using actual
      have applicationEq := silent_resume_application (command.actor? app) middle execution resumed
      rw [applicationEq]
      have small : count ≤ 4 := by omega
      interval_cases count
      · rw [chosen] at moved
        exact sample_preserves_resolution_unfinished before.application middle.application sample0
          (by decide) unfinished (applicationStep_facts before middle _ moved).1
      · rw [chosen] at moved
        exact sample_preserves_resolution_unfinished before.application middle.application sample1
          (by decide) unfinished (applicationStep_facts before middle _ moved).1
      · rw [chosen] at moved
        obtain ⟨updated, chosen, rfl⟩ := PMF.support_map .. ▸ moved
        obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ chosen
        exact unfinished
      · have empty := silent_rounds_empty_network 3 before prior
        have wait : command = .wait := by
          rw [chosen]
          change latest (before.observeEnvironment app) = .wait
          unfold latest reactiveLatest
          simp only [ReactiveApplication.Execution.observeEnvironment, MessageNetwork.publicView,
            empty, MessageNetwork.empty, List.reverse_nil, List.find?_nil]
        rw [wait] at moved
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
        cases (PMF.mem_support_pure_iff _ _).mp moved
        exact unfinished
      · rw [chosen] at moved
        have physical := (applicationStep_facts before middle _ moved).1
        simp only [environmentStep, PMF.mem_support_pure_iff _ _] at physical
        rw [physical]
        exact unfinished

/-- The initialized raw protocol actually reaches a second owner activation
with the same resolution still ready at clock one. Both authentic decisions
can subsequently be compared at this same information state. -/
theorem exists_late_turn :
    ∃ execution : app.Execution,
      Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨4, some owner, execution⟩)) ∧
      execution.environmentRecall.length = 6 ∧ execution.application.clock = 1 ∧
      execution.application.config.cut.Ready resolution ∧
      execution.application.activatedAt resolution = some 0 ∧
      execution.network = .empty := by
  obtain ⟨before, supported⟩ :=
    (app.roundsFrom (initialLaw setup) scheduler (fun _ => app.silentPolicy) 5).support_nonempty
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler
    (fun _ => app.silentPolicy) 5 (by decide) before supported
  have phase : Phase ⟨5, none, before⟩ := phase_history trace
  have position : before.environmentRecall.length = 5 := by
    have budget := phase.budget
    change 5 + before.environmentRecall.length = 10 at budget
    omega
  have unfinished := silent_rounds_unfinished 5 (by rfl) before supported
  have current : before.application.config.cut.IsPrefix 2 := by
    rcases phase.laterPrefix (by dsimp only; omega) with current | complete
    · exact current
    · exact (unfinished ((complete.2 resolution).mpr (by decide))).elim
  have ready := (ready_iff_rank setup _ 2 current resolution).mpr rfl
  have empty := silent_rounds_empty_network 5 before supported
  obtain ⟨after, moved⟩ := (before.environmentStep app (.activate owner)).support_nonempty
  have selected : (.activate owner : app.Command) ∈
      (scheduler before.environmentRecall (before.observeEnvironment app)).support := by
    simp only [scheduler, position, stageCommand, PMF.mem_support_pure_iff _ _]
  obtain ⟨afterTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler 4 before
    after (.activate owner) trace selected moved
  obtain ⟨updated, chosen, afterEq⟩ := PMF.support_map .. ▸ moved
  obtain ⟨sampled, sampleMem, updateEq⟩ := PMF.support_map .. ▸ chosen
  have sampledEq : sampled = ∅ := (PMF.mem_support_pure_iff _ _).mp sampleMem
  have applicationEq : after.application = before.application := by
    rw [← afterEq, ← updateEq]
  have nextPosition : after.environmentRecall.length = 6 := by
    rw [environmentStep_recall_append before after _ moved, List.length_append,
      List.length_singleton, position]
  refine ⟨after, ⟨afterTrace⟩, nextPosition, ?_, applicationEq ▸ ready,
    applicationEq ▸ phase.entered current, ?_⟩
  · rw [applicationEq, phase.clock]
    change stageClock before.environmentRecall.length = 1
    rw [position]
    rfl
  · rw [← afterEq, ← updateEq]
    change before.network.learn owner sampled = .empty
    rw [sampledEq, MessageNetwork.learn_empty]
    exact empty

abbrev initialBinding : EventGraph.FieldRef nativeGraph.layout (.binding owner .bool) :=
  ⟨.inl ⟨0, by decide⟩, rfl⟩

theorem resolution_output : nativeGraph.outputLayout resolution = .publication .bool := rfl

theorem resolution_code :
    cast (congrArg (EventCode (L := simpleExpr) nativeGraph.layout) resolution_output)
      (nativeGraph.nodes resolution) =
        .resolve (L := simpleExpr) owner BaseTy.bool initialBinding [] := rfl

theorem resolution_node : nodeView nativeGraph resolution =
    .resolve owner .bool initialBinding [] resolution_output resolution_code :=
  nodeView_eq_resolve resolution_output resolution_code

/-- The initial authentic typed commitment survives every legal raw history. -/
theorem initial_binding_stored (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control)) :
    initialBinding.get? control.execution.application.config.store = some (.success true) := by
  have stored := ((runtime setup).reactiveStoreInvariant leaks initialBinding.field
    (.success true)).history (initialLaw setup) horizon scheduler (by
      intro state supported
      obtain ⟨initial, chosen, stateEq⟩ := PMF.support_map .. ▸ supported
      have initialEq : initial = sourceInitial := (PMF.mem_support_pure_iff _ _).mp chosen
      rw [← stateEq, initialEq]
      rfl) trace
  exact stored

theorem initial_binding_openable (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control)) :
    ∃ candidate : Handle nativeGraph,
      control.execution.application.accepted initialBinding.field = some candidate ∧
      candidate.1 = owner ∧
      control.execution.application.candidates.lookup candidate = .openable ⟨.bool, true⟩ :=
  (legalFacts setup leaks horizon scheduler control trace).binding.success_provenance
    initialBinding true (initial_binding_stored control trace)

def lateResponse (candidate : Handle nativeGraph) (disclose : Bool) : app.Action :=
  ⟨some (disclosureSubmission (if disclose then
    .opening resolution candidate ⟨.bool, true⟩ else .withhold resolution))⟩

theorem late_response_application (execution : app.Execution) (candidate : Handle nativeGraph)
    (disclose : Bool) :
    (execution.respond app owner (lateResponse candidate disclose)).application =
      execution.application := by
  cases disclose <;> rfl

theorem late_response_command (execution : app.Execution) (candidate : Handle nativeGraph)
    (disclose : Bool) (empty : execution.network = .empty) :
    latestWithhold
        ((execution.respond app owner (lateResponse candidate disclose)).observeEnvironment app) =
      if disclose then .wait else .include (owner, 0) := by
  have packetCall (state : app.State) (known : List (Message Player (WitnessedPacket nativeGraph)))
      (submission : app.Submission) :
      (app.packet state owner known submission).call = submission.call.packet := rfl
  cases disclose <;>
    simp [latestWithhold, ReactiveApplication.Execution.observeEnvironment,
      ReactiveApplication.Execution.respond, lateResponse, disclosureSubmission,
      MessageNetwork.submit, empty, MessageNetwork.empty, MessageNetwork.publicView,
      ReactiveApplication.EnvironmentView.Unpublished, packetCall, Message.sender]

def sourceUtility (source : Vegas.State simpleExpr setup.program.terminalCtx)
    (_who : Player) : ℝ := if (source.get .here).isSuccess then 1 else 0

theorem baseUtility_failure (control : app.Control)
    (failed : control.execution.application.config.store (.inr resolution) = some .failure) :
    baseUtility setup leaks sourceUtility (some control) owner = 0 := by
  unfold baseUtility
  rw [sourceReadout_eq_decode]
  cases decoded : decodeState? (terminalRefs setup.program)
      control.execution.application.config.store with
  | none => rfl
  | some source =>
      have agree : (terminalRefs setup.program).Agrees source
          control.execution.application.config.store :=
        decodeState?_agrees (terminalRefs setup.program)
          control.execution.application.config.store source decoded
      have result := agree (name := 3) .here
      change control.execution.application.config.store (.inr resolution) =
        some (source.get .here) at result
      have value : source.get .here = .failure := by simpa only [failed, Option.some.injEq] using
        result.symm
      simp [sourceUtility, value, PublicationResult.isSuccess]

def tickExecution (execution : app.Execution) : app.Execution :=
  { execution with
    application := { execution.application with clock := execution.application.clock + 1 }
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .application .advanceClock⟩] }

def waitExecution (execution : app.Execution) : app.Execution :=
  { execution with
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .wait⟩] }

def includeExecution (execution : app.Execution) (id : MessageId Player) : app.Execution :=
  { execution.includePending app id with
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .include id⟩] }

private theorem round_of_command (execution : app.Execution) (stage : Nat)
    (position : execution.environmentRecall.length = stage) (command : app.Command)
    (selected : stageCommand stage (execution.observeEnvironment app) = command)
    (passive : command.actor? app = none) :
    app.round scheduler (fun _ => app.silentPolicy) execution =
      execution.environmentStep app command := by
  simp only [ReactiveApplication.round, scheduler, position, selected, PMF.pure_bind,
    ReactiveApplication.dispatch, passive]
  change (execution.environmentStep app command).bind PMF.pure = _
  exact PMF.bind_pure _

theorem tick_environment (execution : app.Execution) :
    execution.environmentStep app (.application .advanceClock) =
      PMF.pure (tickExecution execution) := by
  change ((PMF.pure { execution.application with clock := execution.application.clock + 1 }).map
    (fun state => { execution with application := state })).map _ = _
  simp only [PMF.pure_map]
  rfl

theorem wait_environment (execution : app.Execution) :
    execution.environmentStep app .wait = PMF.pure (waitExecution execution) := by
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  rfl

theorem include_environment (execution : app.Execution) (id : MessageId Player) :
    execution.environmentStep app (.include id) = PMF.pure (includeExecution execution id) := by
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  rfl

theorem ticks_before_expiry (execution : app.Execution)
    (position : execution.environmentRecall.length = 7) :
    app.runRounds scheduler (fun _ => app.silentPolicy) 3 execution =
      (tickExecution (tickExecution execution)).environmentStep app
        (.application (.expire resolution)) := by
  have first := round_of_command execution 7 position (.application .advanceClock) rfl rfl
  have second := round_of_command (tickExecution execution) 8 (by
    simp only [tickExecution, List.length_append, List.length_singleton, position])
      (.application .advanceClock) rfl rfl
  have third := round_of_command (tickExecution (tickExecution execution)) 9 (by
    simp only [tickExecution, List.length_append, List.length_singleton, position])
      (.application (.expire resolution)) rfl rfl
  simp only [ReactiveApplication.runRounds, first, tick_environment, PMF.pure_bind,
    second, third, PMF.bind_pure]

def failureState (execution : app.Execution)
    (ready : execution.application.config.cut.Ready resolution) : app.State :=
  execution.application.complete resolution ready false .failure

def expiryExecution (execution : app.Execution)
    (ready : execution.application.config.cut.Ready resolution) : app.Execution :=
  { execution with
    application := (failureState execution ready).markMissed resolution
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .application (.expire resolution)⟩] }

def completedExpiryExecution (execution : app.Execution) : app.Execution :=
  { execution with
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .application (.expire resolution)⟩] }

theorem expiry_environment_ready (execution : app.Execution)
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 3) :
    execution.environmentStep app (.application (.expire resolution)) =
      PMF.pure (expiryExecution execution ready) := by
  have expired := environmentStep_expire_resolve_eq (runtime setup) execution.application
    resolution ready 0 entered (by rw [clock]; decide) owner .bool initialBinding []
    resolution_output resolution_code resolution_node
  change ((environmentStep (runtime setup) execution.application (.expire resolution)).map
    (fun state => { execution with application := state })).map _ = _
  rw [expired]
  simp only [PMF.pure_map]
  rfl

theorem expiry_environment_completed (execution : app.Execution)
    (completed : resolution ∈ execution.application.config.cut.completed) :
    execution.environmentStep app (.application (.expire resolution)) =
      PMF.pure (completedExpiryExecution execution) := by
  have inactive : ¬ execution.application.config.cut.Ready resolution :=
    fun ready => ready.1 completed
  change ((environmentStep (runtime setup) execution.application (.expire resolution)).map
    (fun state => { execution with application := state })).map _ = _
  rw [environmentStep_expire_of_not_ready (runtime setup) execution.application resolution inactive]
  simp only [PMF.pure_map]
  rfl

theorem late_withhold_included (execution : app.Execution) (candidate : Handle nativeGraph)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, execution⟩))
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1) (empty : execution.network = .empty) :
    ((execution.respond app owner (lateResponse candidate false)).includePending app
        (owner, 0)).application = failureState execution ready ∧
      ((owner, 0), true) ∈
        ((execution.respond app owner (lateResponse candidate false)).includePending app
          (owner, 0)).receipts := by
  have facts := legalFacts setup leaks horizon scheduler ⟨4, some owner, execution⟩ trace
  have looked := (runtime setup).respond_submit_lookup_of_ready leaks execution owner
    ⟨.withhold resolution, none⟩ facts.serials resolution rfl ready
  have serial : execution.network.nextSerial owner = 0 := by rw [empty]; rfl
  rw [serial] at looked
  change (execution.respond app owner (lateResponse candidate false)).network.lookup (owner, 0) =
    some ⟨(owner, 0), ⟨.withhold resolution, none, some ⟨resolution⟩⟩⟩ at looked
  have timely : execution.application.WithinDeadline (runtime setup) resolution := by
    simp only [EventGraphRuntime.State.WithinDeadline, entered, clock]
    decide
  have handled := handle_withhold_unremembered_eq (runtime setup) execution.application
    (owner, 0) resolution owner .bool initialBinding [] resolution_output resolution_code
    resolution_node ready timely rfl (congrFun facts.remembered resolution)
  have physical : app.handle execution.application
      ⟨(owner, 0), ⟨.withhold resolution, none, some ⟨resolution⟩⟩⟩ =
        some (failureState execution ready) := by
    rw [(runtime setup).reactiveApplication_handle_of_tokenValid leaks]
    · exact handled
    · rfl
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  rw [looked]
  dsimp only
  rw [late_response_application, physical]
  exact ⟨rfl, List.mem_append_right _ (List.mem_singleton_self _)⟩

def lateEndpoint (execution : app.Execution) (candidate : Handle nativeGraph)
    (ready : execution.application.config.cut.Ready resolution) (disclose : Bool) : app.Execution :=
  if disclose then
    expiryExecution
      (tickExecution (tickExecution (waitExecution
        (execution.respond app owner (lateResponse candidate true))))) ready
  else
    completedExpiryExecution
      (tickExecution (tickExecution (includeExecution
        (execution.respond app owner (lateResponse candidate false)) (owner, 0))))

/-- The actual remaining scheduler kernel, including the two ticks and expiry,
is deterministic for either physical disclosure response at this late turn. -/
theorem late_suffix (execution : app.Execution) (candidate : Handle nativeGraph)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, execution⟩))
    (position : execution.environmentRecall.length = 6)
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1) (empty : execution.network = .empty)
    (disclose : Bool) :
    app.runRounds scheduler (fun _ => app.silentPolicy) 4
        (execution.respond app owner (lateResponse candidate disclose)) =
      PMF.pure (lateEndpoint execution candidate ready disclose) := by
  have postPosition : ((execution.respond app owner
      (lateResponse candidate disclose)).environmentRecall).length = 6 := by
    cases disclose <;> exact position
  have selected := late_response_command execution candidate disclose empty
  cases disclose with
  | false =>
      have first := round_of_command _ 6 postPosition (.include (owner, 0)) selected rfl
      let next := includeExecution (execution.respond app owner (lateResponse candidate false))
        (owner, 0)
      have nextPosition : next.environmentRecall.length = 7 := by
        change (execution.environmentRecall ++ [_]).length = 7
        rw [List.length_append, List.length_singleton, position]
      have accepted := late_withhold_included execution candidate trace ready entered clock empty
      have nextApplication : next.application = failureState execution ready := accepted.1
      have completed : resolution ∈
          (tickExecution (tickExecution next)).application.config.cut.completed := by
        change resolution ∈ next.application.config.cut.completed
        rw [nextApplication]
        change resolution ∈
          (execution.application.config.cut.complete resolution ready).completed
        simp only [EventOrder.Cut.completed_complete, Finset.mem_insert_self]
      rw [ReactiveApplication.runRounds, first, include_environment, PMF.pure_bind,
        ticks_before_expiry _ nextPosition, expiry_environment_completed _ completed]
      rfl
  | true =>
      have first := round_of_command _ 6 postPosition .wait selected rfl
      let next := waitExecution (execution.respond app owner (lateResponse candidate true))
      have nextPosition : next.environmentRecall.length = 7 := by
        change (execution.environmentRecall ++ [_]).length = 7
        rw [List.length_append, List.length_singleton, position]
      rw [ReactiveApplication.runRounds, first, wait_environment, PMF.pure_bind,
        ticks_before_expiry _ nextPosition]
      rw [expiry_environment_ready (tickExecution (tickExecution (waitExecution
        (execution.respond app owner (lateResponse candidate true))))) ready entered (by
        change execution.application.clock + 1 + 1 = 3
        rw [clock])]
      rfl

theorem late_endpoint_trace (execution : app.Execution) (candidate : Handle nativeGraph)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, execution⟩))
    (position : execution.environmentRecall.length = 6)
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1) (empty : execution.network = .empty)
    (disclose : Bool) :
    Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨0, none, lateEndpoint execution candidate ready disclose⟩)) := by
  obtain ⟨responded⟩ := app.raw_trace_respond (initialLaw setup) horizon scheduler 4 execution
    owner (lateResponse candidate disclose) trace
  apply app.raw_trace_runRounds (initialLaw setup) horizon scheduler
    (fun _ => app.silentPolicy) 0 4 _ _ responded
  rw [late_suffix execution candidate trace position ready entered clock empty disclose]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem late_endpoint_terminal (execution : app.Execution) (candidate : Handle nativeGraph)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, execution⟩))
    (position : execution.environmentRecall.length = 6)
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1) (empty : execution.network = .empty)
    (disclose : Bool) :
    (lateEndpoint execution candidate ready disclose).application.config.cut.Terminal := by
  obtain ⟨ended⟩ := late_endpoint_trace execution candidate trace position ready entered clock empty
    disclose
  exact completesPlay _ ended ⟨rfl, rfl⟩

theorem late_endpoint_failed (execution : app.Execution) (candidate : Handle nativeGraph)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, execution⟩))
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1) (empty : execution.network = .empty)
    (disclose : Bool) :
    (lateEndpoint execution candidate ready disclose).application.config.store (.inr resolution) =
      some .failure := by
  cases disclose with
  | false =>
      have accepted := late_withhold_included execution candidate trace ready entered clock empty
      change ((execution.respond app owner (lateResponse candidate false)).includePending app
        (owner, 0)).application.config.store (.inr resolution) = some .failure
      rw [accepted.1]
      exact execution.application.config.complete_output_same resolution ready false .failure
  | true =>
      exact execution.application.config.complete_output_same resolution ready false .failure

theorem late_prefix_unmarked (execution : app.Execution)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, execution⟩))
    (ready : execution.application.config.cut.Ready resolution) :
    execution.application.missedEvents = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro event marked
  have facts := (legalFacts setup leaks horizon scheduler ⟨4, some owner, execution⟩ trace).misses
    event marked
  have eventEq : event = resolution := by
    cases actual : nativeGraph.actor? event with
    | none => exact (facts.2 actual).elim
    | some who => exact owned_event event who actual
  exact ready.1 (eventEq ▸ facts.1)

theorem late_endpoint_missed (execution : app.Execution) (candidate : Handle nativeGraph)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, execution⟩))
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1) (empty : execution.network = .empty)
    (disclose : Bool) :
    (lateEndpoint execution candidate ready disclose).application.publicView.missedDecisionBy
      owner = disclose := by
  cases disclose with
  | false =>
      have accepted := late_withhold_included execution candidate trace ready entered clock empty
      have unmarked := late_prefix_unmarked execution trace ready
      apply PublicView.missedDecisionBy_clear
      change ((execution.respond app owner (lateResponse candidate false)).includePending app
        (owner, 0)).application.missedEvents = ∅
      rw [accepted.1]
      exact unmarked
  | true =>
      apply PublicView.missedDecisionBy_of_event _ owner resolution resolution_actor
      exact Finset.mem_insert_self _ _

def withholdMessage (execution : app.Execution) : Message Player (WitnessedPacket nativeGraph) :=
  ⟨(owner, 0), ⟨.withhold resolution, none,
    execution.application.publicView.tokenFor (.withhold resolution)⟩⟩

private theorem include_inputs (execution : app.Execution) (id : MessageId Player) :
    (execution.includePending app id).network.inputs = execution.network.inputs := by
  rw [app.includePending_network]
  unfold MessageNetwork.includePending
  cases execution.network.lookup id <;> rfl

theorem late_withhold_inputs (execution : app.Execution) (candidate : Handle nativeGraph)
    (ready : execution.application.config.cut.Ready resolution)
    (empty : execution.network = .empty) :
    (lateEndpoint execution candidate ready false).network.inputs =
      [withholdMessage execution] := by
  change ((execution.respond app owner (lateResponse candidate false)).includePending app
    (owner, 0)).network.inputs = [withholdMessage execution]
  rw [include_inputs]
  have packet (known : List (Message Player (WitnessedPacket nativeGraph))) :
      app.packet
        (app.submit execution.application owner (disclosureSubmission (.withhold resolution)))
        owner known (disclosureSubmission (.withhold resolution)) =
          (withholdMessage execution).payload := rfl
  simp only [ReactiveApplication.Execution.respond, lateResponse, Bool.false_eq_true, ↓reduceIte,
    packet]
  simp only [MessageNetwork.submit, empty, MessageNetwork.empty, List.nil_append]
  rfl

theorem late_withhold_permitted (execution : app.Execution) (candidate : Handle nativeGraph)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, execution⟩))
    (position : execution.environmentRecall.length = 6)
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1) (empty : execution.network = .empty)
    (record : app.TrafficRecord)
    (present : record ∈ app.executionTraffic (lateEndpoint execution candidate ready false)) :
    ((runtime setup).settledRecord leaks (lateEndpoint execution candidate ready false)).permits
      record.envelope = true := by
  obtain ⟨ended⟩ := late_endpoint_trace execution candidate trace position ready entered clock empty
    false
  have inputs := app.stateTraffic_inputs (initialLaw setup) horizon scheduler ended
  change (app.executionTraffic (lateEndpoint execution candidate ready false)).map
    ReactiveApplication.TrafficRecord.envelope =
      (lateEndpoint execution candidate ready false).network.inputs at inputs
  have member : record.envelope ∈ [withholdMessage execution] := by
    rw [← late_withhold_inputs execution candidate ready empty, ← inputs]
    exact List.mem_map.mpr ⟨record, present, rfl⟩
  have recordEq : record.envelope = withholdMessage execution := List.mem_singleton.mp member
  rw [recordEq]
  apply SettledRecord.permits_of_accepted _ _ resolution rfl
  · exact (late_withhold_included execution candidate trace ready entered clock empty).2
  · rfl

/-- Every authentic sampler, including an uncertain watcher, yields exactly
zero charge for the accepted withholding and unit charge for the public miss. -/
theorem late_audit_charge (execution : app.Execution) (candidate : Handle nativeGraph)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, execution⟩))
    (position : execution.environmentRecall.length = 6)
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1) (empty : execution.network = .empty)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (disclose : Bool) :
    GameTheory.Enforcement.TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
        (sourceServiceAudit setup leaks sample)
        (some ⟨0, none, lateEndpoint execution candidate ready disclose⟩) owner =
      if disclose then 1 else 0 := by
  unfold sourceServiceAudit
  rw [(runtime setup).serviceAudit_charge,
    late_endpoint_missed execution candidate trace ready entered clock empty disclose]
  cases disclose with
  | true => rfl
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply app.sampledTrafficAudit_sound
      · exact authentic _
      · intro record member _
        exact late_withhold_permitted execution candidate trace position ready entered clock empty
          record member

def auditedUtility (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : ℝ) : app.ProtocolState → Player → ℝ :=
  GameTheory.Enforcement.TerminalAudit.utility (baseUtility setup leaks sourceUtility)
    ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
    (fun _ => deposit)

/-- These are the actual terminal typed utility and collected audit, rather
than rewards assigned directly to the chosen response. -/
theorem late_terminal_utility (execution : app.Execution) (candidate : Handle nativeGraph)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, execution⟩))
    (position : execution.environmentRecall.length = 6)
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1) (empty : execution.network = .empty)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) (disclose : Bool) :
    auditedUtility sample deposit (app.finished (lateEndpoint execution candidate ready disclose))
      owner = if disclose then -deposit else 0 := by
  unfold auditedUtility GameTheory.Enforcement.TerminalAudit.utility ReactiveApplication.finished
  rw [baseUtility_failure _
    (late_endpoint_failed execution candidate trace ready entered clock empty disclose)]
  rw [late_audit_charge execution candidate trace position ready entered clock empty sample
    authentic]
  cases disclose <;> simp

theorem late_continuation_value (execution : app.Execution) (candidate : Handle nativeGraph)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, execution⟩))
    (position : execution.environmentRecall.length = 6)
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1) (empty : execution.network = .empty)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) (disclose : Bool) :
    expect ((app.runRounds scheduler (fun _ => app.silentPolicy) 4
        (execution.respond app owner (lateResponse candidate disclose))).map app.finished)
        (fun state => auditedUtility sample deposit state owner) =
      if disclose then -deposit else 0 := by
  rw [late_suffix execution candidate trace position ready entered clock empty disclose,
    PMF.pure_map, expect_pure]
  exact late_terminal_utility execution candidate trace position ready entered clock empty sample
    authentic deposit disclose

/-- At an initialized legal late information state with authentic opening
material, withholding strictly improves the actual continuation utility over
opening, for every positive escrow and every authentic partial audit. This
does not rule out an equilibrium which opens at the protected first turn and
chooses withholding freely at this later turn. -/
theorem exists_late_opening_regret
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) (positive : 0 < deposit) :
    ∃ (execution : app.Execution) (candidate : Handle nativeGraph),
      Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨4, some owner, execution⟩)) ∧
      candidate.1 = owner ∧
      execution.application.accepted initialBinding.field = some candidate ∧
      execution.application.candidates.lookup candidate = .openable ⟨.bool, true⟩ ∧
      expect ((app.runRounds scheduler (fun _ => app.silentPolicy) 4
        (execution.respond app owner (lateResponse candidate true))).map app.finished)
        (fun state => auditedUtility sample deposit state owner) <
      expect ((app.runRounds scheduler (fun _ => app.silentPolicy) 4
        (execution.respond app owner (lateResponse candidate false))).map app.finished)
        (fun state => auditedUtility sample deposit state owner) := by
  obtain ⟨execution, ⟨trace⟩, position, clock, ready, entered, empty⟩ := exists_late_turn
  obtain ⟨candidate, accepted, owned, verified⟩ := initial_binding_openable _ trace
  refine ⟨execution, candidate, ⟨trace⟩, owned, accepted, verified, ?_⟩
  rw [late_continuation_value execution candidate trace position ready entered clock empty sample
    authentic deposit true,
    late_continuation_value execution candidate trace position ready entered clock empty sample
      authentic deposit false]
  simpa using neg_neg_of_pos positive

def lateSilentEndpoint (execution : app.Execution)
    (ready : execution.application.config.cut.Ready resolution) : app.Execution :=
  expiryExecution (tickExecution (tickExecution
    (waitExecution (execution.respond app owner ⟨none⟩)))) ready

theorem late_silence_suffix (execution : app.Execution)
    (position : execution.environmentRecall.length = 6)
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1) (empty : execution.network = .empty) :
    app.runRounds scheduler (fun _ => app.silentPolicy) 4 (execution.respond app owner ⟨none⟩) =
      PMF.pure (lateSilentEndpoint execution ready) := by
  have selected : latestWithhold ((execution.respond app owner ⟨none⟩).observeEnvironment app) =
      .wait := by
    change latestWithhold (execution.observeEnvironment app) = .wait
    simp only [latestWithhold, ReactiveApplication.Execution.observeEnvironment,
      MessageNetwork.publicView, empty, MessageNetwork.empty, List.reverse_nil, List.find?_nil]
  have first := round_of_command (execution.respond app owner ⟨none⟩) 6 position .wait selected rfl
  let next := waitExecution (execution.respond app owner ⟨none⟩)
  have nextPosition : next.environmentRecall.length = 7 := by
    change (execution.environmentRecall ++ [_]).length = 7
    rw [List.length_append, List.length_singleton, position]
  rw [ReactiveApplication.runRounds, first, wait_environment, PMF.pure_bind,
    ticks_before_expiry _ nextPosition,
    expiry_environment_ready (tickExecution (tickExecution
      (waitExecution (execution.respond app owner ⟨none⟩)))) ready entered (by
      change execution.application.clock + 1 + 1 = 3
      rw [clock])]
  rfl

theorem late_silence_value (execution : app.Execution)
    (position : execution.environmentRecall.length = 6)
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1) (empty : execution.network = .empty)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : ℝ) :
    expect ((app.runRounds scheduler (fun _ => app.silentPolicy) 4
        (execution.respond app owner ⟨none⟩)).map app.finished)
        (fun state => auditedUtility sample deposit state owner) = -deposit := by
  rw [late_silence_suffix execution position ready entered clock empty, PMF.pure_map, expect_pure]
  unfold auditedUtility GameTheory.Enforcement.TerminalAudit.utility ReactiveApplication.finished
  have failed : (lateSilentEndpoint execution ready).application.config.store (.inr resolution) =
      some .failure :=
    execution.application.config.complete_output_same resolution ready false .failure
  rw [baseUtility_failure _ failed]
  unfold sourceServiceAudit
  rw [(runtime setup).serviceAudit_charge_of_miss leaks _ _ owner resolution resolution_actor
    (Finset.mem_insert_self _ _)]
  simp

/-- Protection, rather than mere timeliness, closes the current prescribed
policy's gate. Thus every timing lottery is silent at this actual late input. -/
theorem late_turnPolicy_silent (execution : app.Execution)
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1) (turns : Nat)
    (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program) :
    sourceServiceTurnPolicy setup leaks bound turns timing profile owner
      (execution.recall owner) (execution.observe app owner) = PMF.pure ⟨none⟩ := by
  have turn := ownTurn?_of_ready setup execution.application ready resolution_actor
  have closed : ¬ execution.application.publicView.InclusionFitsDeadline (runtime setup) bound
      resolution := by
    change ¬ match execution.application.activatedAt resolution with
      | none => False
      | some entered => execution.application.clock - entered + 2 < 3
    rw [entered, clock]
    decide
  let law := sourceServiceTurnPolicy setup leaks bound turns timing profile owner
    (execution.recall owner) (execution.observe app owner)
  have onlySilent (response : app.Action) (chosen : response ∈ law.support) :
      response = ⟨none⟩ := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some material =>
        obtain ⟨event, _action, current, _, fits, _⟩ :=
          sourceServiceTurnPolicy_submission chosen rfl
        have eventEq : event = resolution := Option.some.inj (current.symm.trans turn)
        subst event
        exact (closed fits).elim
  calc
    law = law.map id := (PMF.map_id _).symm
    _ = law.map (fun _ => (⟨none⟩ : app.Action)) :=
      map_congr_on_support _ onlySilent
    _ = PMF.pure ⟨none⟩ := PMF.map_const _ _

/-- The current prescribed waiting law, integrated through the actual last
four service commands, incurs the public miss. No later owner turn can repair
this continuation because this concrete service has no further activation. -/
theorem late_prescription_value (execution : app.Execution)
    (position : execution.environmentRecall.length = 6)
    (ready : execution.application.config.cut.Ready resolution)
    (entered : execution.application.activatedAt resolution = some 0)
    (clock : execution.application.clock = 1) (empty : execution.network = .empty)
    (turns : Nat) (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : ℝ) :
    expect (((app.invoke
        (sourceServiceTurnPolicy setup leaks bound turns timing profile) owner execution).bind
        (app.runRounds scheduler (fun _ => app.silentPolicy) 4)).map app.finished)
        (fun state => auditedUtility sample deposit state owner) = -deposit := by
  unfold ReactiveApplication.invoke
  rw [late_turnPolicy_silent execution ready entered clock turns timing profile,
    PMF.pure_map, PMF.pure_bind]
  exact late_silence_value execution position ready entered clock empty sample deposit

/-- The existing protected-gate timing policy has a strictly worse actual
continuation than lawful withholding at this reachable late turn. This is a
policy-completion obstruction, not a failure of equilibrium preservation. -/
theorem exists_late_wait_regret (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) (positive : 0 < deposit) :
    ∃ (execution : app.Execution) (candidate : Handle nativeGraph),
      Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨4, some owner, execution⟩)) ∧
      expect (((app.invoke
          (sourceServiceTurnPolicy setup leaks bound turns timing profile) owner execution).bind
          (app.runRounds scheduler (fun _ => app.silentPolicy) 4)).map app.finished)
          (fun state => auditedUtility sample deposit state owner) <
      expect ((app.runRounds scheduler (fun _ => app.silentPolicy) 4
          (execution.respond app owner (lateResponse candidate false))).map app.finished)
          (fun state => auditedUtility sample deposit state owner) := by
  obtain ⟨execution, ⟨trace⟩, position, clock, ready, entered, empty⟩ := exists_late_turn
  obtain ⟨candidate, _, _, _⟩ := initial_binding_openable _ trace
  refine ⟨execution, candidate, ⟨trace⟩, ?_⟩
  rw [late_prescription_value execution position ready entered clock empty turns timing profile
    sample deposit,
    late_continuation_value execution candidate trace position ready entered clock empty sample
      authentic deposit false]
  simpa using neg_neg_of_pos positive

theorem late_opening_evidence (execution : app.Execution) (candidate : Handle nativeGraph)
    (owned : candidate.1 = owner)
    (verified : execution.application.candidates.lookup candidate = .openable ⟨.bool, true⟩)
    (known : List (Message Player (WitnessedPacket nativeGraph))) :
    (app.packet
      (app.submit execution.application owner
        (disclosureSubmission (.opening resolution candidate ⟨.bool, true⟩))) owner known
      (disclosureSubmission (.opening resolution candidate ⟨.bool, true⟩))).evidence =
        some ⟨candidate, ⟨.bool, true⟩⟩ := by
  exact WitnessedSubmission.emit_owned _ execution.application owner known
    ⟨candidate, ⟨.bool, true⟩⟩ owned verified

/-- The typed utility used above is precisely the source program's declared
integer payoff, embedded into the real-valued analysis utility. -/
theorem source_payoffs (source : Vegas.State simpleExpr setup.program.terminalCtx) :
    (program.evaluatePayoffs source).map (fun payoff => (payoff.1, (payoff.2 : ℝ))) =
      [(owner, sourceUtility source owner)] := by
  change [(owner, (evalExpr
    (.ite (.isSuccess (.var 3 .here)) (.constInt 1) (.constInt 0))
      (sourcePublicEnv source) : ℝ))] = _
  have value : (sourcePublicEnv source).get .here = source.get .here := rfl
  simp only [evalExpr, value, sourceUtility]
  cases (source.get .here).isSuccess <;> simp

end Vegas.LateResolutionService
