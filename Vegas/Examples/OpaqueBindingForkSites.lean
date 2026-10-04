/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.OpaqueBindingForkService
import Vegas.Game.AsyncServiceSourceSites
import Vegas.Game.SourceServiceRetainedPolicy
import Interaction.ReactiveRoundTrace
import Interaction.ScheduledOpening
import Vegas.Pending.ReactiveServiceMarkers

/-! # Source-compatible and privately risky paths through the same Bob input -/

noncomputable section

namespace Vegas.OpaqueBindingFork

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

open Classical in
def baseBounds : MessageBounds nativeGraph := ⟨5, {⟨.bool, false⟩, ⟨.bool, true⟩}⟩

def bounds : MessageBounds nativeGraph :=
  baseBounds.withInitialValues ((setup.initialLaw.map setup.eventInputs).map State.initial)

theorem bindingValues : bounds.CoversBindingValues := by
  intro event
  change Fin 5 at event
  fin_cases event
  all_goals try trivial
  intro value
  apply baseBounds.withInitialValues_preserves_values
  change Bool at value
  cases value <;> simp [baseBounds]

theorem initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state := by
  intro state supported
  rw [initialLaw_eq_inputs] at supported
  obtain ⟨input, present, rfl⟩ := PMF.support_map .. ▸ supported
  exact baseBounds.candidateValues_initial (setup.initialLaw.map setup.eventInputs)
    (by change ((PMF.pure sourceInitial).map setup.eventInputs).support.Finite; simp)
    input present

def service : AsyncServiceSpec Player simpleExpr where
  setup := setup
  leaks := leaks
  bounds := bounds
  values := bindingValues
  initialValues := initialValues
  capacity := by change 5 ≤ 5; rfl
  horizon := horizon
  scheduler := scheduler
  delay := delay
  bound := bound
  contract := contract
  timely := timely
  initialFinite := ⟨by change (PMF.pure sourceInitial).support.Finite; simp⟩
  leaksFinite := ⟨by intro who pending; simp [leaks]⟩
  schedulerFinite := by
    intro past view
    unfold scheduler
    split
    · exact (Set.Finite.union (by simp) (by simp)).subset
        (support_mix_subset _ _ _ _ _)
    · simp

def sourcePolicy (who : Player) : BehavioralPolicy who setup.program :=
  (fun _ _ => PMF.pure (.success true),
    (fun _ _ => PMF.pure false, (fun _ _ => PMF.pure false, PUnit.unit)))

def sourceProfile : BehavioralProfile setup.program := sourcePolicy

theorem source_admitted (who : Player) :
    (sourceProfile who).Admitted setup.program (CommitmentInterface.values setup.program) := by
  dsimp only [sourceProfile, sourcePolicy, BehavioralPolicy.Admitted,
    CommitmentInterface.values, setup, program]
  refine ⟨?_, trivial⟩
  intro own view choice supported
  cases (PMF.mem_support_pure_iff _ _).mp supported
  trivial

theorem source_effective (who : Player) :
    (sourceProfile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context) := by
  refine ⟨?_, ?_, trivial⟩
  all_goals intro own view disclose supported
  all_goals cases (PMF.mem_support_pure_iff _ _).mp supported
  all_goals simp [effectiveDisclosureView]

/-- Alice's binding is selected at her second own turn. Other owned events
are selected at their first turn. -/
def timing : TurnTiming setup 1 := fun event _ _ => PMF.pure
  (if event = binding then 1 else 0)

def sourcePlayers : Player → app.Policy :=
  sourceServiceTurnPolicy setup leaks bound 1 timing sourceProfile

abbrev canonicalMenu := bounds.canonicalMenu (runtime setup) leaks
abbrev riskMenu := bounds.riskMenu (runtime setup) leaks bound

theorem sourcePlayers_admissible (who : Player) :
    canonicalMenu.Admissible (initialLaw setup) horizon scheduler who (sourcePlayers who) := by
  intro control trace _active response selected
  exact sourceServiceTurnPolicy_retained bounds bindingValues initialValues
    (by change 5 ≤ 5; rfl) bound 1 timing sourceProfile who (source_admitted who)
    control trace response selected

def initialState : app.State := State.initial (setup.eventInputs sourceInitial)

theorem sample0_ready : initialState.config.cut.Ready sample0 := by decide

def sampled0State : app.State := initialState.complete sample0 sample0_ready PUnit.unit true

theorem sample1_ready : sampled0State.config.cut.Ready sample1 := by decide

def sampled1State : app.State := sampled0State.complete sample1 sample1_ready PUnit.unit true

def initialExecution : app.Execution := ReactiveApplication.Execution.initial app initialState

def sampled0Execution : app.Execution :=
  { initialExecution with
    application := sampled0State
    environmentRecall := [⟨initialExecution.observeEnvironment app,
      .application (.executeSample sample0)⟩] }

def sampled1Execution : app.Execution :=
  { sampled0Execution with
    application := sampled1State
    environmentRecall := sampled0Execution.environmentRecall ++
      [⟨sampled0Execution.observeEnvironment app, .application (.executeSample sample1)⟩] }

def firstAliceExecution : app.Execution :=
  WaitRiskConfounding.activate (runtime setup) leaks sampled1Execution alice

def waitedExecution : app.Execution := firstAliceExecution.respond app alice ⟨none⟩

def emptyIncludeExecution : app.Execution :=
  { waitedExecution with environmentRecall := waitedExecution.environmentRecall ++
      [⟨waitedExecution.observeEnvironment app, .wait⟩] }

private theorem sample_environment (state : app.State) (event : nativeGraph.EventId)
    (ready : state.config.cut.Ready event)
    (outputEq : nativeGraph.outputLayout event = .publicData BaseTy.bool)
    (law : PublicDist (L := simpleExpr) nativeGraph.layout BaseTy.bool)
    (codeEq : cast (congrArg (EventCode (L := simpleExpr) nativeGraph.layout) outputEq)
      (nativeGraph.nodes event) = EventCode.sample (L := simpleExpr) BaseTy.bool law)
    (evaluated : (nativeGraph.nodes event).eval?
      (cast (congrArg EventField.Action outputEq.symm) PUnit.unit) state.config.store =
      some ((PMF.pure true).map (cast (congrArg EventField.Value outputEq.symm)))) :
    environmentStep (runtime setup) state (.executeSample event) =
      PMF.pure (state.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventField.Value outputEq.symm) true)) := by
  rw [environmentStep_executeSample_eq (runtime setup) state event ready BaseTy.bool law
    outputEq codeEq (nodeView_eq_sample outputEq codeEq),
    state.config.step_eq_map_of_eval event ready _ _ evaluated,
    PMF.pure_map, PMF.pure_map, PMF.pure_map]
  rfl

theorem sampled0_environment :
    initialExecution.environmentStep app (.application (.executeSample sample0)) =
      PMF.pure sampled0Execution := by
  have sampled := sample_environment initialState sample0 sample0_ready rfl
    (compilePublicDist (ContextRefs.initial setup.context (outputLayout setup.program))
      (.weighted (.pure true))) rfl (by
        simp only [PMF.pure_map]
        change some (RationalLaw.pure true).denote = some (PMF.pure true)
        exact congrArg some (RationalLaw.denote_pure true))
  change ((environmentStep (runtime setup) initialState (.executeSample sample0)).map _).map _ = _
  rw [sampled, PMF.pure_map, PMF.pure_map]
  rfl

theorem sampled1_environment :
    sampled0Execution.environmentStep app (.application (.executeSample sample1)) =
      PMF.pure sampled1Execution := by
  have sampled := sample_environment sampled0State sample1 sample1_ready rfl
    (compilePublicDist (ContextRefs.cons (name := 1) (cell := .publicData BaseTy.bool)
      ((outputEmbedding setup.program).ref sample0)
      (ContextRefs.initial setup.context (outputLayout setup.program)))
        (.weighted (.pure true))) rfl (by
          simp only [PMF.pure_map]
          change some (RationalLaw.pure true).denote = some (PMF.pure true)
          exact congrArg some (RationalLaw.denote_pure true))
  change ((environmentStep (runtime setup) sampled0State (.executeSample sample1)).map _).map _ = _
  rw [sampled, PMF.pure_map, PMF.pure_map]
  rfl

theorem binding_ready : sampled1Execution.application.config.cut.Ready binding := by decide

theorem binding_turn : sampled1Execution.application.publicView.ownTurn? alice = some binding :=
  ownTurn?_of_ready setup sampled1Execution.application binding_ready binding_actor

def bindingRefs : ContextRefs nativeGraph.layout
    [(2, .publicData BaseTy.bool), (1, .publicData BaseTy.bool),
      (0, .commitment bob BaseTy.bool)] :=
  ContextRefs.cons ((outputEmbedding setup.program).ref sample1)
    (ContextRefs.cons ((outputEmbedding setup.program).ref sample0)
      (ContextRefs.initial setup.context (outputLayout setup.program)))

theorem compiled_binding_true :
    (compileEventProfile setup.program sourceProfile) alice binding binding_actor
      (setup.eventGraph.fromModeObservation .sequential alice
        ((graph setup).playerObserve alice sampled1Execution.application.config)) =
      PMF.pure (.success true) := by
  change (match decodeObservation? alice bindingRefs
    ((graph setup).playerStore alice sampled1Execution.application.config.store) with
    | some _ => PMF.pure (PublicationResult.success true)
    | none => PMF.pure PublicationResult.failure) = _
  have decoded : (decodeObservation? alice bindingRefs
      ((graph setup).playerStore alice sampled1Execution.application.config.store)).isSome = true :=
    by decide
  obtain ⟨observation, same⟩ := Option.isSome_iff_exists.mp decoded
  rw [same]

private theorem pure_mixture (policies : Fin 2 → app.Policy) (slot : Fin 2)
    (past : List app.PlayerEntry) (view : app.PlayerView) :
    (app.policyMixture (PMF.pure slot) policies).policy past view = policies slot past view := by
  have fixed := app.policyMixture_posterior_pure_append
    (PMF.pure slot) policies [] past slot rfl
  simp only [List.nil_append] at fixed
  rw [app.policyMixture_policy, fixed, PMF.pure_bind]

theorem firstAlice_wait : sourcePlayers alice (firstAliceExecution.recall alice)
    (firstAliceExecution.observe app alice) = PMF.pure ⟨none⟩ := by
  have turn : firstAliceExecution.application.publicView.ownTurn? alice = some binding :=
    binding_turn
  rw [sourcePlayers, sourceServiceTurnPolicy_turn setup leaks bound 1 timing sourceProfile alice
    _ _ binding binding_actor turn]
  change (app.policyMixture (PMF.pure (1 : Fin 2))
    (sourceServiceTurnFamily setup leaks bound sourceProfile alice binding 1)).policy _ _ = _
  rw [pure_mixture]
  have zero : sourceServiceTurn setup leaks alice binding (firstAliceExecution.recall alice)
      (firstAliceExecution.observe app alice) = some 0 := by
    simp only [sourceServiceTurn]
    rfl
  simp only [sourceServiceTurnFamily, ReactiveApplication.turnScheduledPolicy, zero,
    Fin.val_one, Option.some.injEq, Nat.zero_ne_one, ite_false]
  rfl

private theorem next_round_support (count : Nat) (before after : app.Execution)
    (prior : before ∈ (app.roundsFrom (initialLaw setup) scheduler sourcePlayers count).support)
    (command : app.Command)
    (selected : command ∈
      (scheduler before.environmentRecall (before.observeEnvironment app)).support)
    (dispatched : after ∈ (app.dispatch sourcePlayers command before).support) :
    after ∈ (app.roundsFrom (initialLaw setup) scheduler sourcePlayers (count + 1)).support := by
  rw [app.roundsFrom_succ, PMF.support_bind]
  apply Set.mem_iUnion₂.mpr
  refine ⟨before, prior, ?_⟩
  rw [ReactiveApplication.round, PMF.support_bind]
  exact Set.mem_iUnion₂.mpr ⟨command, selected, dispatched⟩

theorem initial_supported :
    initialExecution ∈ (app.roundsFrom (initialLaw setup) scheduler sourcePlayers 0).support := by
  change initialExecution ∈ ((initialLaw setup).bind _).support
  have initialized : initialLaw setup = PMF.pure initialState := by
    change (PMF.pure sourceInitial).map _ = _
    rw [PMF.pure_map]
    rfl
  rw [initialized, PMF.pure_bind]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem sampled0_supported :
    sampled0Execution ∈ (app.roundsFrom (initialLaw setup) scheduler sourcePlayers 1).support := by
  apply next_round_support 0 initialExecution sampled0Execution initial_supported
    (.application (.executeSample sample0))
  · change _ ∈ (PMF.pure (.application (.executeSample sample0) : app.Command)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · change _ ∈ ((initialExecution.environmentStep app _).bind _).support
    rw [sampled0_environment, PMF.pure_bind]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem sampled1_supported :
    sampled1Execution ∈ (app.roundsFrom (initialLaw setup) scheduler sourcePlayers 2).support := by
  apply next_round_support 1 sampled0Execution sampled1Execution sampled0_supported
    (.application (.executeSample sample1))
  · change _ ∈ (PMF.pure (.application (.executeSample sample1) : app.Command)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · change _ ∈ ((sampled0Execution.environmentStep app _).bind _).support
    rw [sampled1_environment, PMF.pure_bind]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem waited_supported :
    waitedExecution ∈ (app.roundsFrom (initialLaw setup) scheduler sourcePlayers 3).support := by
  apply next_round_support 2 sampled1Execution waitedExecution sampled1_supported (.activate alice)
  · change _ ∈ (PMF.pure (.activate alice : app.Command)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [ReactiveApplication.dispatch,
      WaitRiskConfounding.activate_empty_law (runtime setup) leaks _ alice rfl, PMF.pure_bind]
    change _ ∈ ((sourcePlayers alice (firstAliceExecution.recall alice)
      (firstAliceExecution.observe app alice)).map _).support
    rw [firstAlice_wait, PMF.pure_map]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem emptyInclude_supported :
    emptyIncludeExecution ∈
      (app.roundsFrom (initialLaw setup) scheduler sourcePlayers 4).support := by
  apply next_round_support 3 waitedExecution emptyIncludeExecution waited_supported .wait
  · have latest : (runtime setup).reactiveLatest leaks binding alice
        (waitedExecution.observeEnvironment app) = .wait := rfl
    change _ ∈ (PMF.pure ((runtime setup).reactiveLatest leaks binding alice
      (waitedExecution.observeEnvironment app))).support
    rw [latest]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · change _ ∈ ((waitedExecution.environmentStep app .wait).bind _).support
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

def secondAliceExecution : app.Execution :=
  WaitRiskConfounding.activate (runtime setup) leaks emptyIncludeExecution alice

def bindingResponse : app.Action :=
  (runtime setup).reactiveBinding leaks alice binding .bool (.success true) 0

theorem binding_output : nativeGraph.outputLayout binding = .binding alice BaseTy.bool := rfl

theorem binding_code :
    cast (congrArg (EventCode (L := simpleExpr) nativeGraph.layout) binding_output)
    (nativeGraph.nodes binding) =
      EventCode.bind (L := simpleExpr) (layout := nativeGraph.layout) alice BaseTy.bool := rfl

theorem binding_node : nodeView nativeGraph binding =
    .bind alice BaseTy.bool binding_output binding_code :=
  nodeView_eq_bind binding_output binding_code

theorem secondAlice_turn : secondAliceExecution.application.publicView.ownTurn? alice =
    some binding := binding_turn

theorem secondAlice_canonical :
    (runtime setup).canonicalServiceDecision leaks alice (secondAliceExecution.recall alice)
      (secondAliceExecution.observe app alice) binding (.success true) = bindingResponse := by
  apply (runtime setup).canonicalServiceDecision_binding leaks alice _ _ binding .bool
    binding_output binding_code binding_node 0
  have counted : (secondAliceExecution.observe app alice).application.publicView.bindingCount
      alice = 0 := by decide
  rw [← counted]
  exact canonicalFreshSlot_canonical alice _ (by rfl)

theorem secondAlice_canonical_law :
    sourceServiceCanonicalPolicy setup leaks sourceProfile alice (secondAliceExecution.recall alice)
      (secondAliceExecution.observe app alice) = PMF.pure bindingResponse := by
  rw [sourceServiceCanonicalPolicy_at_event setup leaks sourceProfile alice secondAliceExecution
    binding secondAlice_turn binding_actor]
  have same : secondAliceExecution.application.config = sampled1Execution.application.config := rfl
  rw [same, compiled_binding_true, PMF.pure_map]
  exact congrArg PMF.pure secondAlice_canonical

theorem secondAlice_opportunity_law :
    sourceServiceCanonicalOpportunity setup leaks bound sourceProfile alice binding
      (secondAliceExecution.recall alice) (secondAliceExecution.observe app alice) =
        PMF.pure bindingResponse := by
  have unrecorded : (runtime setup).eventRecorded leaks (secondAliceExecution.recall alice)
      binding = false := rfl
  have fits : (secondAliceExecution.observe app alice).application.publicView.InclusionFitsDeadline
      (runtime setup) bound binding := by change 0 - 0 + 2 < 3; decide
  simp only [sourceServiceCanonicalOpportunity, unrecorded, Bool.false_eq_true, ite_false,
    ite_eq_left fits, secondAlice_canonical_law, PMF.pure_bind]
  rfl

theorem secondAlice_response : sourcePlayers alice (secondAliceExecution.recall alice)
    (secondAliceExecution.observe app alice) = PMF.pure bindingResponse := by
  rw [sourcePlayers, sourceServiceTurnPolicy_turn setup leaks bound 1 timing sourceProfile alice
    _ _ binding binding_actor secondAlice_turn]
  change (app.policyMixture (PMF.pure (1 : Fin 2))
    (sourceServiceTurnFamily setup leaks bound sourceProfile alice binding 1)).policy _ _ = _
  rw [pure_mixture]
  have one : sourceServiceTurn setup leaks alice binding (secondAliceExecution.recall alice)
      (secondAliceExecution.observe app alice) = some 1 := by
    simp only [sourceServiceTurn]
    rfl
  simp only [sourceServiceTurnFamily, ReactiveApplication.turnScheduledPolicy, one,
    Fin.val_one, ite_true]
  exact secondAlice_opportunity_law

def cleanSubmitted : app.Execution := secondAliceExecution.respond app alice bindingResponse

def cleanTicked : app.Execution :=
  WaitRiskConfounding.advance (runtime setup) leaks cleanSubmitted

def includedExecution (execution : app.Execution) : app.Execution :=
  { execution.includePending app (alice, 0) with
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .include (alice, 0)⟩] }

def cleanAccepted : app.Execution := includedExecution cleanTicked

def riskySecondAlice : app.Execution :=
  WaitRiskConfounding.activate (runtime setup) leaks
    (WaitRiskConfounding.advance (runtime setup) leaks emptyIncludeExecution) alice

def riskySubmitted : app.Execution := riskySecondAlice.respond app alice bindingResponse

def riskyAccepted : app.Execution := includedExecution riskySubmitted

theorem cleanSubmitted_supported :
    cleanSubmitted ∈ (app.roundsFrom (initialLaw setup) scheduler sourcePlayers 5).support := by
  apply next_round_support 4 emptyIncludeExecution cleanSubmitted emptyInclude_supported
    (.activate alice)
  · change _ ∈ (mix (1 / 2) (by norm_num) (by norm_num)
      (PMF.pure (.activate alice)) (PMF.pure (.application .advanceClock : app.Command))).support
    exact mem_support_mix_left _ _ _ (by norm_num) ((PMF.mem_support_pure_iff _ _).mpr rfl)
  · rw [ReactiveApplication.dispatch,
      WaitRiskConfounding.activate_empty_law (runtime setup) leaks _ alice rfl, PMF.pure_bind]
    change _ ∈ ((sourcePlayers alice (secondAliceExecution.recall alice)
      (secondAliceExecution.observe app alice)).map _).support
    rw [secondAlice_response, PMF.pure_map]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem cleanTicked_supported :
    cleanTicked ∈ (app.roundsFrom (initialLaw setup) scheduler sourcePlayers 6).support := by
  apply next_round_support 5 cleanSubmitted cleanTicked cleanSubmitted_supported
    (.application .advanceClock)
  · change _ ∈ (PMF.pure (.application .advanceClock : app.Command)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [ReactiveApplication.dispatch,
      WaitRiskConfounding.advance_law (runtime setup) leaks, PMF.pure_bind]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem cleanAccepted_supported :
    cleanAccepted ∈ (app.roundsFrom (initialLaw setup) scheduler sourcePlayers 7).support := by
  apply next_round_support 6 cleanTicked cleanAccepted cleanTicked_supported (.include (alice, 0))
  · have latest : (runtime setup).reactiveLatest leaks binding alice
        (cleanTicked.observeEnvironment app) = .include (alice, 0) := by
      unfold reactiveLatest
      rfl
    change _ ∈ (PMF.pure ((runtime setup).reactiveLatest leaks binding alice
      (cleanTicked.observeEnvironment app))).support
    rw [latest]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · change _ ∈ ((cleanTicked.environmentStep app (.include (alice, 0))).bind _).support
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem riskyAccepted_config : riskyAccepted.application.config =
    sampled1State.config.complete binding binding_ready
      (cast (congrArg EventField.Action binding_output.symm) (.success true))
      (cast (congrArg EventField.Value binding_output.symm) (.success true)) := by
  have unused : riskySecondAlice.application.HandleUnused (alice, .prepared 0) := by
    intro field associated
    change initialState.accepted field = some (alice, .prepared 0) at associated
    obtain ⟨input, owner, payload, _, _, same⟩ :=
      State.initial_accepted_eq_some (graph := nativeGraph) (setup.eventInputs sourceInitial) field
        (alice, .prepared 0) associated
    cases congrArg Prod.snd same
  let players : Player → app.Policy := fun _ => app.silentPolicy
  let network : (runtime setup).NetworkPolicy leaks := fun _ _ => PMF.pure .wait
  have realized := (runtime setup).rawBinding_reserved_config leaks riskySecondAlice alice
    binding .bool binding_output binding_code binding_node 0 (some ⟨.bool, true⟩)
    binding_ready (by change 1 - 0 < 3; decide) rfl rfl unused
    MessageNetwork.SerialsBeforeNext.empty players network
  dsimp only at realized
  rw [(runtime setup).rawBinding_reserved_selection leaks riskySecondAlice alice binding 0
    (some ⟨.bool, true⟩) MessageNetwork.SerialsBeforeNext.empty players network] at realized
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at realized
  have endpoint := congrArg PMF.support realized
  simp only [PMF.support_pure] at endpoint
  exact congrArg Prod.fst (Set.singleton_injective endpoint)

theorem accepted_application_eq : cleanAccepted.application = riskyAccepted.application := by
  obtain ⟨applicationEq, networkEq, receiptsEq⟩ :=
    WaitRiskConfounding.response_advance_fields (runtime setup) leaks
      emptyIncludeExecution alice bindingResponse
  change cleanTicked.application = riskySubmitted.application at applicationEq
  change cleanTicked.network = riskySubmitted.network at networkEq
  dsimp only [cleanAccepted, riskyAccepted, includedExecution,
    ReactiveApplication.Execution.includePending]
  rw [applicationEq, networkEq]
  split <;> rfl

theorem cleanAccepted_binding_completed :
    binding ∈ cleanAccepted.application.config.cut.completed := by
  rw [accepted_application_eq, riskyAccepted_config]
  rw [Config.complete_cut]
  exact (EventOrder.Cut.mem_complete _ binding binding_ready binding).mpr (Or.inl rfl)

theorem cleanAccepted_bob_ready : cleanAccepted.application.config.cut.Ready bobResolution := by
  rw [accepted_application_eq, riskyAccepted_config]
  decide

theorem cleanAccepted_clock : cleanAccepted.application.clock = 1 := by
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler sourcePlayers
    6 (by decide) cleanTicked cleanTicked_supported
  obtain ⟨inputs, invariant⟩ := (roster_trace_facts setup leaks horizon scheduler trace).1
  have progress := (runtime setup).reactive_include_progress leaks inputs cleanTicked
    (alice, 0) invariant
  exact progress.clock.trans (by rfl)

theorem cleanAccepted_missedEvents : cleanAccepted.application.missedEvents = ∅ := by
  have moved : cleanAccepted ∈
      (cleanTicked.environmentStep app (.include (alice, 0))).support := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have markers := (runtime setup).reactive_environmentStep_missedEvents_eq leaks cleanTicked
    cleanAccepted (.include (alice, 0)) (by intro event; simp) moved
  exact markers.trans rfl

def cleanTick1 : app.Execution := WaitRiskConfounding.advance (runtime setup) leaks cleanAccepted

def cleanBeforeExpiry : app.Execution :=
  WaitRiskConfounding.advance (runtime setup) leaks cleanTick1

def expiredExecution (execution : app.Execution) : app.Execution :=
  { execution with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .application (.expire binding)⟩] }

def cleanAfterExpiry : app.Execution := expiredExecution cleanBeforeExpiry

def cleanBob : app.Execution :=
  WaitRiskConfounding.activate (runtime setup) leaks cleanAfterExpiry bob

theorem cleanTick1_supported :
    cleanTick1 ∈ (app.roundsFrom (initialLaw setup) scheduler sourcePlayers 8).support := by
  apply next_round_support 7 cleanAccepted cleanTick1 cleanAccepted_supported
    (.application .advanceClock)
  · change _ ∈ (PMF.pure (.application .advanceClock : app.Command)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [ReactiveApplication.dispatch,
      WaitRiskConfounding.advance_law (runtime setup) leaks, PMF.pure_bind]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem cleanBeforeExpiry_supported : cleanBeforeExpiry ∈
    (app.roundsFrom (initialLaw setup) scheduler sourcePlayers 9).support := by
  apply next_round_support 8 cleanTick1 cleanBeforeExpiry cleanTick1_supported
    (.application .advanceClock)
  · change _ ∈ (PMF.pure (.application .advanceClock : app.Command)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [ReactiveApplication.dispatch,
      WaitRiskConfounding.advance_law (runtime setup) leaks, PMF.pure_bind]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem cleanAfterExpiry_environment :
    cleanBeforeExpiry.environmentStep app (.application (.expire binding)) =
      PMF.pure cleanAfterExpiry := by
  have notReady : ¬cleanBeforeExpiry.application.config.cut.Ready binding :=
    fun ready => ready.1 cleanAccepted_binding_completed
  change ((environmentStep (runtime setup) cleanBeforeExpiry.application (.expire binding)).map
    _).map _ = _
  rw [environmentStep_expire_of_not_ready (runtime setup) _ binding notReady,
    PMF.pure_map, PMF.pure_map]
  rfl

theorem cleanAfterExpiry_supported : cleanAfterExpiry ∈
    (app.roundsFrom (initialLaw setup) scheduler sourcePlayers 10).support := by
  apply next_round_support 9 cleanBeforeExpiry cleanAfterExpiry cleanBeforeExpiry_supported
    (.application (.expire binding))
  · change _ ∈ (PMF.pure (.application (.expire binding) : app.Command)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [ReactiveApplication.dispatch, cleanAfterExpiry_environment, PMF.pure_bind]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem cleanBob_environment : cleanAfterExpiry.environmentStep app (.activate bob) =
    PMF.pure cleanBob :=
  WaitRiskConfounding.activate_empty_law (runtime setup) leaks _ bob rfl

theorem cleanBob_roundSupported : app.RoundSupported (initialLaw setup) horizon scheduler
    sourcePlayers (some ⟨14, some bob, cleanBob⟩) := by
  refine ⟨by change 11 + 14 = 25; rfl, 10, cleanAfterExpiry, .activate bob, rfl,
    cleanAfterExpiry_supported, ?_, rfl, ?_⟩
  · change _ ∈ (PMF.pure (.activate bob : app.Command)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [cleanBob_environment]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem cleanBob_turn : cleanBob.application.publicView.ownTurn? bob = some bobResolution := by
  apply cleanBob.application.publicView.ownTurn?_of_ownTurn bob bobResolution
  apply cleanBob.application.ownTurn_of_ready setup.eventGraph.sequentialize_barrierOrdered
  · exact (cleanBob.application.publicView_eventReady bobResolution).mpr cleanAccepted_bob_ready
  · rfl

theorem cleanBob_missedEvents : cleanBob.application.missedEvents = ∅ :=
  cleanAccepted_missedEvents

theorem cleanBob_recalledSubmission_clear (who : Player) :
    (runtime setup).recalledSubmissionRisk leaks bound who (cleanBob.recall who) = false := by
  fin_cases who <;> decide

theorem cleanBob_recalledOpportunity_clear (who : Player) :
    (runtime setup).recalledOpportunityRisk leaks bound who (cleanBob.recall who) = false := by
  fin_cases who <;> decide

theorem cleanBob_persistent_clear (who : Player) :
    (runtime setup).persistentServiceRisk leaks bound who (cleanBob.recall who)
      (cleanBob.observe app who) = false := by
  rw [(runtime setup).persistentServiceRisk_clear_iff]
  exact ⟨⟨(cleanBob.observe app who).application.publicView.missedDecisionBy_clear
    cleanBob_missedEvents who, cleanBob_recalledSubmission_clear who⟩,
      cleanBob_recalledOpportunity_clear who⟩

theorem cleanBob_canonical_trace : Nonempty ((canonicalMenu.protocol (initialLaw setup)
    horizon scheduler).Trace (some ⟨14, some bob, cleanBob⟩)) := by
  obtain ⟨prior⟩ := canonicalMenu.trace_roundsFrom_of_admissible (initialLaw setup) horizon
    scheduler sourcePlayers sourcePlayers_admissible 10 (by decide) cleanAfterExpiry
      cleanAfterExpiry_supported
  apply canonicalMenu.trace_environment (initialLaw setup) horizon scheduler 14
    cleanAfterExpiry cleanBob (.activate bob) prior
  · change _ ∈ (PMF.pure (.activate bob : app.Command)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [cleanBob_environment]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem cleanBob_clock : cleanBob.application.clock = 3 := by
  change cleanAccepted.application.clock + 1 + 1 = 3
  rw [cleanAccepted_clock]

theorem cleanBob_fits : cleanBob.application.publicView.InclusionFitsDeadline
    (runtime setup) bound bobResolution := by
  obtain ⟨trace⟩ := cleanBob_canonical_trace
  obtain ⟨inputs, invariant⟩ := (roster_trace_facts setup leaks horizon scheduler
    (canonicalMenu.toRawTrace (initialLaw setup) horizon scheduler trace)).1
  obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor bobResolution
    cleanAccepted_bob_ready rfl
  change (match cleanBob.application.activatedAt bobResolution with
    | none => False
    | some started => cleanBob.application.clock - started + 0 < 4)
  rw [activated, cleanBob_clock]
  omega

theorem cleanBob_clear : (runtime setup).serviceRisk leaks bound bob (cleanBob.recall bob)
    (cleanBob.observe app bob) = false := by
  apply (runtime setup).serviceRisk_clear leaks bound bob _ _ (cleanBob_persistent_clear bob)
  exact (runtime setup).firstUnprotectedOpportunity_protected leaks bound bob _ _ bobResolution
    cleanBob_turn cleanBob_fits

/-- The same local information admits an initialized protected source witness
whose Alice commitment was delayed once without opening service risk. -/
theorem cleanBob_sourceCompatible : service.sourceCompatibleInfo bob
    (some (cleanBob.recall bob, cleanBob.observe app bob)) := by
  obtain ⟨trace⟩ := cleanBob_canonical_trace
  let included := bounds.canonicalMenu_in_risk (runtime setup) leaks bound
  let history : (riskMenu.protocol (initialLaw setup) horizon scheduler).History :=
    ⟨some ⟨14, some bob, cleanBob⟩, included.trace (initialLaw setup) horizon scheduler trace⟩
  refine ⟨sourceProfile, 1, timing, source_admitted, source_effective,
    history, 14, cleanBob, rfl, ?_, cleanBob_roundSupported,
      cleanBob_persistent_clear, cleanBob_clear⟩
  have observed := riskMenu.info (initialLaw setup) horizon scheduler bob history.trace
  exact observed.trans (by simp only [history, ReactiveApplication.observe, ite_true])

theorem riskySecondAlice_turn : riskySecondAlice.application.publicView.ownTurn? alice =
    some binding := binding_turn

theorem riskySecondAlice_canonical :
    (runtime setup).canonicalServiceDecision leaks alice (riskySecondAlice.recall alice)
      (riskySecondAlice.observe app alice) binding (.success true) = bindingResponse := by
  apply (runtime setup).canonicalServiceDecision_binding leaks alice _ _ binding .bool
    binding_output binding_code binding_node 0
  have counted : (riskySecondAlice.observe app alice).application.publicView.bindingCount
      alice = 0 := by decide
  rw [← counted]
  exact canonicalFreshSlot_canonical alice _ (by rfl)

theorem riskyResponse_canonical : bindingResponse ∈ canonicalMenu.actions alice
    (riskySecondAlice.recall alice) (riskySecondAlice.observe app alice) := by
  have counted : (riskySecondAlice.observe app alice).application.publicView.bindingCount
      alice = 0 := by decide
  have selected : canonicalFreshSlot alice (riskySecondAlice.observe app alice).application =
      some 0 := by
    rw [← counted]
    exact canonicalFreshSlot_canonical alice _ (by rfl)
  have included : (⟨.bool, true⟩ : Raw simpleExpr) ∈ bounds.values := by
    apply baseBounds.withInitialValues_preserves_values
    simp [baseBounds]
  rw [← riskySecondAlice_canonical]
  exact bounds.canonical_binding_value_retained (runtime setup) leaks alice _ _ binding .bool
    binding_output binding_code binding_node riskySecondAlice_turn binding_actor
    ((riskySecondAlice.application.publicView_eventReady binding).mpr binding_ready)
    (by change 1 - 0 < 3; decide) rfl 0 selected (by change 0 < 5; decide) true included

/-- The late manual call is legal even though the literal protected turn policy
would wait at this opportunity. -/
theorem riskySecondAlice_canonical_trace : Nonempty ((canonicalMenu.protocol (initialLaw setup)
    horizon scheduler).Trace (some ⟨19, some alice, riskySecondAlice⟩)) := by
  obtain ⟨prior⟩ := canonicalMenu.trace_roundsFrom_of_admissible (initialLaw setup) horizon
    scheduler sourcePlayers sourcePlayers_admissible 4 (by decide) emptyIncludeExecution
      emptyInclude_supported
  have selected : (.application .advanceClock : app.Command) ∈
      (scheduler emptyIncludeExecution.environmentRecall
        (emptyIncludeExecution.observeEnvironment app)).support := by
    change _ ∈ (mix (1 / 2) (by norm_num) (by norm_num)
      (PMF.pure (.activate alice)) (PMF.pure (.application .advanceClock : app.Command))).support
    exact mem_support_mix_right _ _ _ (by norm_num) ((PMF.mem_support_pure_iff _ _).mpr rfl)
  have moved : WaitRiskConfounding.advance (runtime setup) leaks emptyIncludeExecution ∈
      (emptyIncludeExecution.environmentStep app (.application .advanceClock)).support := by
    rw [WaitRiskConfounding.advance_law (runtime setup) leaks]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨ticked⟩ := canonicalMenu.trace_environment (initialLaw setup) horizon scheduler 20
    emptyIncludeExecution (WaitRiskConfounding.advance (runtime setup) leaks emptyIncludeExecution)
      (.application .advanceClock) prior selected moved
  apply canonicalMenu.trace_environment (initialLaw setup) horizon scheduler 19 _
    riskySecondAlice (.activate alice) ticked
  · change _ ∈ (PMF.pure (.activate alice : app.Command)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [WaitRiskConfounding.activate_empty_law (runtime setup) leaks _ alice rfl]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem riskySubmitted_canonical_trace : Nonempty ((canonicalMenu.protocol (initialLaw setup)
    horizon scheduler).Trace (some ⟨19, none, riskySubmitted⟩)) := by
  obtain ⟨trace⟩ := riskySecondAlice_canonical_trace
  exact canonicalMenu.trace_respond (initialLaw setup) horizon scheduler 19 riskySecondAlice
    alice bindingResponse trace riskyResponse_canonical

theorem riskyAccepted_canonical_trace : Nonempty ((canonicalMenu.protocol (initialLaw setup)
    horizon scheduler).Trace (some ⟨18, none, riskyAccepted⟩)) := by
  obtain ⟨trace⟩ := riskySubmitted_canonical_trace
  apply canonicalMenu.trace_environment (initialLaw setup) horizon scheduler 18 riskySubmitted
    riskyAccepted (.include (alice, 0)) trace
  · have latest : (runtime setup).reactiveLatest leaks binding alice
        (riskySubmitted.observeEnvironment app) = .include (alice, 0) := by
      unfold reactiveLatest
      rfl
    change _ ∈ (PMF.pure ((runtime setup).reactiveLatest leaks binding alice
      (riskySubmitted.observeEnvironment app))).support
    rw [latest]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

def riskyTick1 : app.Execution := WaitRiskConfounding.advance (runtime setup) leaks riskyAccepted

def riskyBeforeExpiry : app.Execution :=
  WaitRiskConfounding.advance (runtime setup) leaks riskyTick1

def riskyAfterExpiry : app.Execution := expiredExecution riskyBeforeExpiry

def riskyBob : app.Execution :=
  WaitRiskConfounding.activate (runtime setup) leaks riskyAfterExpiry bob

theorem riskyBob_canonical_trace : Nonempty ((canonicalMenu.protocol (initialLaw setup)
    horizon scheduler).Trace (some ⟨14, some bob, riskyBob⟩)) := by
  obtain ⟨accepted⟩ := riskyAccepted_canonical_trace
  have firstSelected : (.application .advanceClock : app.Command) ∈
      (scheduler riskyAccepted.environmentRecall (riskyAccepted.observeEnvironment app)).support :=
    by
    change _ ∈ (PMF.pure (.application .advanceClock : app.Command)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have firstMoved : riskyTick1 ∈
      (riskyAccepted.environmentStep app (.application .advanceClock)).support := by
    rw [WaitRiskConfounding.advance_law (runtime setup) leaks]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨tick1⟩ := canonicalMenu.trace_environment (initialLaw setup) horizon scheduler 17
    riskyAccepted riskyTick1 (.application .advanceClock) accepted firstSelected firstMoved
  have secondSelected : (.application .advanceClock : app.Command) ∈
      (scheduler riskyTick1.environmentRecall (riskyTick1.observeEnvironment app)).support := by
    change _ ∈ (PMF.pure (.application .advanceClock : app.Command)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have secondMoved : riskyBeforeExpiry ∈
      (riskyTick1.environmentStep app (.application .advanceClock)).support := by
    rw [WaitRiskConfounding.advance_law (runtime setup) leaks]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨tick2⟩ := canonicalMenu.trace_environment (initialLaw setup) horizon scheduler 16
    riskyTick1 riskyBeforeExpiry (.application .advanceClock) tick1 secondSelected secondMoved
  have expirySelected : (.application (.expire binding) : app.Command) ∈
      (scheduler riskyBeforeExpiry.environmentRecall
        (riskyBeforeExpiry.observeEnvironment app)).support := by
    change _ ∈ (PMF.pure (.application (.expire binding) : app.Command)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have expiryMoved : riskyAfterExpiry ∈
      (riskyBeforeExpiry.environmentStep app (.application (.expire binding))).support := by
    have notReady : ¬riskyBeforeExpiry.application.config.cut.Ready binding := by
      intro ready
      have completed : binding ∈ riskyAccepted.application.config.cut.completed := by
        rw [← accepted_application_eq]
        exact cleanAccepted_binding_completed
      exact ready.1 completed
    change _ ∈ (((environmentStep (runtime setup) riskyBeforeExpiry.application
      (.expire binding)).map _).map _).support
    rw [environmentStep_expire_of_not_ready (runtime setup) _ binding notReady,
      PMF.pure_map, PMF.pure_map]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨expired⟩ := canonicalMenu.trace_environment (initialLaw setup) horizon scheduler 15
    riskyBeforeExpiry riskyAfterExpiry (.application (.expire binding)) tick2
      expirySelected expiryMoved
  apply canonicalMenu.trace_environment (initialLaw setup) horizon scheduler 14 riskyAfterExpiry
    riskyBob (.activate bob) expired
  · change _ ∈ (PMF.pure (.activate bob : app.Command)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [WaitRiskConfounding.activate_empty_law (runtime setup) leaks _ bob rfl]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem accepted_fields_eq : cleanAccepted.application = riskyAccepted.application ∧
    cleanAccepted.network = riskyAccepted.network ∧
      cleanAccepted.receipts = riskyAccepted.receipts := by
  obtain ⟨applicationEq, networkEq, receiptsEq⟩ :=
    WaitRiskConfounding.response_advance_fields (runtime setup) leaks
      emptyIncludeExecution alice bindingResponse
  change cleanTicked.application = riskySubmitted.application at applicationEq
  change cleanTicked.network = riskySubmitted.network at networkEq
  change cleanTicked.receipts = riskySubmitted.receipts at receiptsEq
  dsimp only [cleanAccepted, riskyAccepted, includedExecution,
    ReactiveApplication.Execution.includePending]
  rw [applicationEq, networkEq, receiptsEq]
  split <;> exact ⟨rfl, rfl, rfl⟩

theorem accepted_bob_input_eq : (cleanAccepted.recall bob, cleanAccepted.observe app bob) =
    (riskyAccepted.recall bob, riskyAccepted.observe app bob) :=
  WaitRiskConfounding.response_advance_foreign_input (runtime setup) leaks emptyIncludeExecution
    alice bob (by decide) bindingResponse (alice, 0)

/-- Bob observes the full same local input after either actual accepted branch,
including public state, his message sample, receipts and own response recall. -/
theorem bob_input_eq : (cleanBob.recall bob, cleanBob.observe app bob) =
    (riskyBob.recall bob, riskyBob.observe app bob) := by
  obtain ⟨applicationEq, networkEq, receiptsEq⟩ := accepted_fields_eq
  have recallEq := congrArg Prod.fst accepted_bob_input_eq
  change cleanAccepted.recall bob = riskyAccepted.recall bob at recallEq
  dsimp only [cleanBob, riskyBob, cleanAfterExpiry, riskyAfterExpiry, expiredExecution,
    cleanBeforeExpiry, riskyBeforeExpiry, cleanTick1, riskyTick1,
    WaitRiskConfounding.advance, WaitRiskConfounding.activate,
    ReactiveApplication.Execution.observe]
  rw [applicationEq, networkEq, receiptsEq, recallEq]

theorem riskyBob_submission_risk : (runtime setup).recalledSubmissionRisk leaks bound alice
    (riskyBob.recall alice) = true := by decide

theorem riskyBob_persistent_risk : (runtime setup).persistentServiceRisk leaks bound alice
    (riskyBob.recall alice) (riskyBob.observe app alice) = true :=
  (runtime setup).persistentServiceRisk_of_recalled leaks bound alice _ _ riskyBob_submission_risk

/-- A privately risky legal history inhabits this actual prescribed Bob site. -/
theorem riskyBob_sourceCompatible : service.sourceCompatibleInfo bob
    (some (riskyBob.recall bob, riskyBob.observe app bob)) := by
  rw [← bob_input_eq]
  exact cleanBob_sourceCompatible

private theorem cleanSecond_canonical_trace : Nonempty ((canonicalMenu.protocol (initialLaw setup)
    horizon scheduler).Trace (some ⟨20, some alice, secondAliceExecution⟩)) := by
  obtain ⟨prior⟩ := canonicalMenu.trace_roundsFrom_of_admissible (initialLaw setup) horizon
    scheduler sourcePlayers sourcePlayers_admissible 4 (by decide) emptyIncludeExecution
      emptyInclude_supported
  apply canonicalMenu.trace_environment (initialLaw setup) horizon scheduler 20
    emptyIncludeExecution secondAliceExecution (.activate alice) prior
  · change _ ∈ (mix (1 / 2) (by norm_num) (by norm_num)
      (PMF.pure (.activate alice)) (PMF.pure (.application .advanceClock : app.Command))).support
    exact mem_support_mix_left _ _ _ (by norm_num) ((PMF.mem_support_pure_iff _ _).mpr rfl)
  · rw [WaitRiskConfounding.activate_empty_law (runtime setup) leaks _ alice rfl]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem secondAlice_response_canonical : bindingResponse ∈ canonicalMenu.actions alice
    (secondAliceExecution.recall alice) (secondAliceExecution.observe app alice) := by
  obtain ⟨trace⟩ := cleanSecond_canonical_trace
  apply sourcePlayers_admissible alice ⟨20, some alice, secondAliceExecution⟩ trace rfl
  rw [secondAlice_response]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

end Vegas.OpaqueBindingFork
