/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeResolutionTail
import Vegas.Examples.MonitoredGuessing.NativeSanctions
import Vegas.Pending.ReactiveSelectionObservation

/-! # The final response has an owner-local binary game result

Reserved inclusion and the remaining clock steps are deterministic. Their game
result depends on Alice's information and response, including for raw preparation
and evidence requests. This does not identify public packet transcripts: a
rejected response can additionally incur a charge.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

private theorem final_maintenance_pure (execution : nativeApp.Execution)
    (command : EnvironmentCommand nativeGraph)
    (maintenance : ∀ event, command ≠ .executeSample event) :
    ∃ next, execution.environmentStep nativeApp (.application command) = FinDist.pure next := by
  have statePure : ∃ state, environmentStep nativeRuntime execution.application command =
      FinDist.pure state := by
    cases command with
    | executeSample event => exact (maintenance event rfl).elim
    | grant event => exact ⟨_, rfl⟩
    | advanceClock => exact ⟨_, rfl⟩
    | expire event => exact ⟨_, rfl⟩
  obtain ⟨state, pureLaw⟩ := statePure
  simp only [ReactiveApplication.Execution.environmentStep]
  change ∃ next, ((environmentStep nativeRuntime execution.application command).map _).map _ =
    FinDist.pure next
  rw [pureLaw, FinDist.map_pure, FinDist.map_pure]
  exact ⟨_, rfl⟩

private theorem final_maintenance_step (players : Player → nativeApp.Policy)
    (execution : nativeApp.Execution) (command : EnvironmentCommand nativeGraph) :
    nativeApp.dispatch players (.application command) execution =
      execution.environmentStep nativeApp (.application command) := by
  exact FinDist.bind_pure _

/-- No policy or observation is consulted after this response. -/
theorem final_response_pure (execution : nativeApp.Execution) (response : nativeApp.Action) :
    ∃ final, ∀ players : Player → nativeApp.Policy,
      nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork resolutionTail
        (execution.respond nativeApp alice response) = FinDist.pure final := by
  obtain ⟨included, reserved⟩ := nativeRuntime.reactiveLatest_step_pure nativeLeaks alice
    alicePublication (execution.respond nativeApp alice response)
  obtain ⟨first, tickOne⟩ := final_maintenance_pure included .advanceClock (by
    intro event impossible; cases impossible)
  obtain ⟨second, tickTwo⟩ := final_maintenance_pure first .advanceClock (by
    intro event impossible; cases impossible)
  obtain ⟨final, expired⟩ := final_maintenance_pure second (.expire alicePublication) (by
    intro event impossible; cases impossible)
  refine ⟨final, ?_⟩
  intro players
  simp only [resolutionTail, runInteractionPlan, FinDist.bind_pure,
    nativeRuntime.interaction_includeLatest_environment, reserved, FinDist.pure_bind]
  simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
    final_maintenance_step, tickOne, tickTwo, expired, FinDist.pure_bind]

def finalResponseExecution (execution : nativeApp.Execution) (response : nativeApp.Action) :
    nativeApp.Execution := (final_response_pure execution response).choose

theorem final_response_law (players : Player → nativeApp.Policy)
    (execution : nativeApp.Execution) (response : nativeApp.Action) :
    nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork resolutionTail
      (execution.respond nativeApp alice response) =
        FinDist.pure (finalResponseExecution execution response) :=
  (final_response_pure execution response).choose_spec players

def finalResponseChoice (execution : nativeApp.Execution) (response : nativeApp.Action) : Bool :=
  (nativeResults (finalResponseExecution execution response).application.config).alice.isSuccess

/-- Every raw response still publishes only the initialized bit or failure. -/
theorem final_response_result (execution : nativeApp.Execution) (response : nativeApp.Action)
    (bit : Bool) (guess : PublicationResult Bool)
    (valid : NativeFixed bit execution.application)
    (stored : bobPublicationRef.get? execution.application.config.store = some guess) :
    nativeResults (finalResponseExecution execution response).application.config =
      ⟨if finalResponseChoice execution response then .success bit else .failure, guess⟩ := by
  let players : Player → nativeApp.Policy := fun _ _ _ => FinDist.pure nativeSilent
  have supported : finalResponseExecution execution response ∈
      (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork resolutionTail
        (execution.respond nativeApp alice response)).support := by
    rw [final_response_law]
    exact FinDist.mem_support_pure.mpr rfl
  have fixed := resolution_plan_invariant players _ (native_fixed_invariant bit) resolutionTail
    _ _ ((native_fixed_invariant bit).respond execution alice response valid) supported
  have bobInvariant := nativeRuntime.reactiveStoreInvariant nativeLeaks (.inr bobPublication)
    guess
  have bobStored := resolution_plan_invariant players _ bobInvariant resolutionTail _ _
    (bobInvariant.respond execution alice response stored) supported
  change bobPublicationRef.get?
    (finalResponseExecution execution response).application.config.store = some guess at bobStored
  change Results.mk _ _ = Results.mk _ _
  congr 1
  · rcases fixed.alice_results with failed | opened
    · simp only [finalResponseChoice, failed, PublicationResult.isSuccess, Bool.false_eq_true,
        ↓reduceIte]
      exact failed
    · simp only [finalResponseChoice, opened, PublicationResult.isSuccess, ↓reduceIte]
      exact opened
  · simp only [bobStored, Option.getD_some]

/-- Transport facts already supplied by actual native histories. The unique
output premise is satisfied when Alice's earlier activation was silent. -/
structure FinalResponseLocal (execution : nativeApp.Execution) : Prop where
  origins : execution.Provenance nativeApp
  recalled : execution.InputRecall nativeApp
  retained : execution.network.PendingOrPublished
  unique : nativeRuntime.UniqueEventOutput nativeLeaks alice alicePublication
    (execution.recall alice)
  serials : execution.network.SerialsBeforeNext
  remembered : execution.application.remembered = fun _ => none
  audit : ∀ response, (execution.respond nativeApp alice response).SubmissionAudit
    nativeApp ReactivePlayerView.publicView

theorem final_history_local (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some alice)
    (unique : nativeRuntime.UniqueEventOutput nativeLeaks alice alicePublication
      (control.execution.recall alice)) : FinalResponseLocal control.execution := by
  have raw := nativeMenu.toRawTrace nativeInitialLaw nativeHorizon nativeScheduler trace
  have audit := nativeApp.submissionAudit_history ReactivePlayerView.publicView
    (fun _ _ => rfl) nativeInitialLaw nativeHorizon nativeScheduler raw
  refine ⟨nativeApp.history_provenance nativeInitialLaw nativeHorizon nativeScheduler raw,
    nativeApp.history_inputRecall nativeInitialLaw nativeHorizon nativeScheduler raw,
    nativeApp.pendingOrPublished_history nativeScheduler nativeInitialLaw nativeHorizon raw,
    unique,
    nativeApp.serialsBeforeNext_history nativeScheduler nativeInitialLaw nativeHorizon raw, ?_, ?_⟩
  · apply (nativeRuntime.reactiveRememberedInvariant nativeLeaks
      (fun memory => memory = fun _ => none)).history
      nativeInitialLaw nativeHorizon nativeScheduler ?_ raw
    intro state supported
    obtain ⟨bit, _, rfl⟩ := FinDist.support_map .. ▸ supported
    rfl
  · intro response
    exact nativeApp.submissionAudit_respond ReactivePlayerView.publicView (fun _ _ => rfl)
      control.execution alice response audit.1
      (nativeApp.submissionOrigin_next_none_history nativeInitialLaw nativeHorizon
        nativeScheduler _ raw alice) (audit.2 alice active)

private theorem final_maintenance_local (left right nextLeft nextRight : nativeApp.Execution)
    (command : EnvironmentCommand nativeGraph)
    (maintenance : ∀ event, command ≠ .executeSample event)
    (views : left.application.playerView alice = right.application.playerView alice)
    (leftMem : nextLeft ∈ (left.environmentStep nativeApp (.application command)).support)
    (rightMem : nextRight ∈ (right.environmentStep nativeApp (.application command)).support) :
    nextLeft.application.playerView alice = nextRight.application.playerView alice := by
  have law := nativeRuntime.maintenance_playerView_congr left.application right.application alice
    command maintenance views
  have pureStep (execution : nativeApp.Execution) :
      ∃ state, environmentStep nativeRuntime execution.application command =
        FinDist.pure state := by
    cases command with
    | executeSample event => exact (maintenance event rfl).elim
    | grant event => exact ⟨_, rfl⟩
    | advanceClock => exact ⟨_, rfl⟩
    | expire event => exact ⟨_, rfl⟩
  obtain ⟨leftState, leftPure⟩ := pureStep left
  obtain ⟨rightState, rightPure⟩ := pureStep right
  have step (execution : nativeApp.Execution) (state : EventGraphRuntime.State nativeGraph)
      (pureLaw : environmentStep nativeRuntime execution.application command = FinDist.pure state)
      (next : nativeApp.Execution)
      (supported : next ∈ (execution.environmentStep nativeApp (.application command)).support) :
      next.application = state := by
    obtain ⟨updated, moved, rfl⟩ := FinDist.support_map .. ▸ supported
    obtain ⟨result, resultMem, rfl⟩ := FinDist.support_map .. ▸ moved
    change result ∈ (environmentStep nativeRuntime execution.application command).support
      at resultMem
    rw [pureLaw] at resultMem
    exact FinDist.mem_support_pure.mp resultMem
  rw [step left leftState leftPure nextLeft leftMem,
    step right rightState rightPure nextRight rightMem]
  rw [leftPure, rightPure, FinDist.map_pure, FinDist.map_pure] at law
  exact FinDist.mem_support_pure.mp (law ▸ FinDist.mem_support_pure.mpr rfl)

/-- Hidden pending messages and the other players' catalogues do not choose
Alice's final result. Her full native view and own action recall suffice. -/
theorem final_response_owner_local (left right : nativeApp.Execution)
    (response : nativeApp.Action) (leftLocal : FinalResponseLocal left)
    (rightLocal : FinalResponseLocal right)
    (recalls : left.recall alice = right.recall alice)
    (observations : left.observe nativeApp alice = right.observe nativeApp alice) :
    (finalResponseExecution left response).application.playerView alice =
      (finalResponseExecution right response).application.playerView alice := by
  let players : Player → nativeApp.Policy := fun _ _ _ => FinDist.pure nativeSilent
  have views := nativeRuntime.reactive_playerView_congr nativeLeaks left.application
    right.application alice (congrArg ReactiveApplication.PlayerView.application observations)
    (leftLocal.remembered.trans rightLocal.remembered.symm)
  have ledgers : left.network.ledger = right.network.ledger :=
    congrArg (fun view : nativeApp.PlayerView => view.messages.ledger) observations
  have reserved := nativeRuntime.reactive_reserved_playerView_congr nativeLeaks alice
    alicePublication left right response views recalls ledgers leftLocal.origins rightLocal.origins
    leftLocal.recalled rightLocal.recalled leftLocal.retained rightLocal.retained leftLocal.unique
    rightLocal.unique leftLocal.serials rightLocal.serials (leftLocal.audit response)
    (rightLocal.audit response)
  obtain ⟨leftReserved, leftPure⟩ := nativeRuntime.reactiveLatest_step_pure nativeLeaks alice
    alicePublication (left.respond nativeApp alice response)
  obtain ⟨rightReserved, rightPure⟩ := nativeRuntime.reactiveLatest_step_pure nativeLeaks alice
    alicePublication (right.respond nativeApp alice response)
  dsimp only at reserved
  rw [leftPure, rightPure, FinDist.map_pure, FinDist.map_pure] at reserved
  have reservedViews : leftReserved.application.playerView alice =
      rightReserved.application.playerView alice :=
    FinDist.mem_support_pure.mp (reserved ▸ FinDist.mem_support_pure.mpr rfl)
  have support (execution : nativeApp.Execution) : finalResponseExecution execution response ∈
      (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork resolutionTail
        (execution.respond nativeApp alice response)).support := by
    rw [final_response_law]
    exact FinDist.mem_support_pure.mpr rfl
  have leftMem := support left
  have rightMem := support right
  simp only [resolutionTail, runInteractionPlan, FinDist.bind_pure,
    nativeRuntime.interaction_includeLatest_environment, leftPure, rightPure,
    FinDist.pure_bind] at leftMem rightMem
  obtain ⟨leftFirst, leftTickOne, leftRest⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ leftMem)
  obtain ⟨rightFirst, rightTickOne, rightRest⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ rightMem)
  obtain ⟨leftSecond, leftTickTwo, leftExpire⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ leftRest)
  obtain ⟨rightSecond, rightTickTwo, rightExpire⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ rightRest)
  simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
    final_maintenance_step]
    at leftTickOne rightTickOne leftTickTwo rightTickTwo leftExpire rightExpire
  have firstViews := final_maintenance_local leftReserved rightReserved leftFirst rightFirst
    .advanceClock (by intro event impossible; cases impossible) reservedViews leftTickOne
      rightTickOne
  have secondViews := final_maintenance_local leftFirst rightFirst leftSecond rightSecond
    .advanceClock (by intro event impossible; cases impossible) firstViews leftTickTwo rightTickTwo
  exact final_maintenance_local leftSecond rightSecond _ _ (.expire alicePublication)
    (by intro event impossible; cases impossible) secondViews leftExpire rightExpire

theorem final_response_choice_local (left right : nativeApp.Execution)
    (response : nativeApp.Action) (leftLocal : FinalResponseLocal left)
    (rightLocal : FinalResponseLocal right)
    (recalls : left.recall alice = right.recall alice)
    (observations : left.observe nativeApp alice = right.observe nativeApp alice) :
    finalResponseChoice left response = finalResponseChoice right response := by
  have views := final_response_owner_local left right response leftLocal rightLocal recalls
    observations
  have stored := congrArg (fun view : PlayerView nativeGraph =>
    alicePublicationRef.get? view.observation.store) views
  change alicePublicationRef.get? (nativeGraph.playerStore alice
    (finalResponseExecution left response).application.config.store) =
      alicePublicationRef.get? (nativeGraph.playerStore alice
        (finalResponseExecution right response).application.config.store) at stored
  rw [alicePublicationRef.get?_playerStore alice _ trivial,
    alicePublicationRef.get?_playerStore alice _ trivial] at stored
  exact congrArg (fun value => (value.getD .failure).isSuccess) stored

open Classical in
/-- A proof-level comparator indexed only by the acting player's information.
The chosen representative cannot affect its result, by owner locality. -/
def finalChoiceAt (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView)
    (response : nativeApp.Action) : Bool :=
  if witness : ∃ execution : nativeApp.Execution, FinalResponseLocal execution ∧
      execution.recall alice = past ∧ execution.observe nativeApp alice = view then
    finalResponseChoice witness.choose response
  else false

theorem final_choice_at_execution (execution : nativeApp.Execution)
    (response : nativeApp.Action) (transport : FinalResponseLocal execution) :
    finalChoiceAt (execution.recall alice) (execution.observe nativeApp alice) response =
      finalResponseChoice execution response := by
  classical
  have witness : ∃ other : nativeApp.Execution, FinalResponseLocal other ∧
      other.recall alice = execution.recall alice ∧
      other.observe nativeApp alice = execution.observe nativeApp alice :=
    ⟨execution, transport, rfl, rfl⟩
  rw [finalChoiceAt, dite_eq_left witness]
  exact final_response_choice_local witness.choose execution response witness.choose_spec.1
    transport witness.choose_spec.2.1 witness.choose_spec.2.2

theorem final_response_result_at (execution : nativeApp.Execution) (response : nativeApp.Action)
    (transport : FinalResponseLocal execution) (bit : Bool) (guess : PublicationResult Bool)
    (valid : NativeFixed bit execution.application)
    (stored : bobPublicationRef.get? execution.application.config.store = some guess) :
    nativeResults (finalResponseExecution execution response).application.config =
      ⟨if finalChoiceAt (execution.recall alice) (execution.observe nativeApp alice) response
        then .success bit else .failure, guess⟩ := by
  rw [final_choice_at_execution execution response transport]
  exact final_response_result execution response bit guess valid stored

/-- An arbitrary declared result table is retained. A rejected extra response
can only increase the separate, nonnegative runtime charge. -/
theorem final_response_payoff_le (payoff : Results → ℝ) (charge : ℝ)
    (nonnegative : 0 ≤ charge) (players : Player → nativeApp.Policy)
    (execution : nativeApp.Execution) (response : nativeApp.Action)
    (transport : FinalResponseLocal execution) (bit : Bool) (guess : PublicationResult Bool)
    (valid : NativeFixed bit execution.application)
    (stored : bobPublicationRef.get? execution.application.config.store = some guess) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork resolutionTail
      (execution.respond nativeApp alice response)).expect
        (fun final => payoff (nativeResults final.application.config) -
          if rejectedAlice final.receipts then charge else 0) ≤
      payoff ⟨if finalChoiceAt (execution.recall alice) (execution.observe nativeApp alice) response
        then .success bit else .failure, guess⟩ -
          if rejectedAlice execution.receipts then charge else 0 := by
  have supported : finalResponseExecution execution response ∈
      (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork resolutionTail
        (execution.respond nativeApp alice response)).support := by
    rw [final_response_law]
    exact FinDist.mem_support_pure.mpr rfl
  have receipts := native_plan_receipts_prefix players resolutionTail _ _ supported
  rw [nativeApp.respond_receipts] at receipts
  have penalty := resolution_charge_mono charge nonnegative execution
    (finalResponseExecution execution response) receipts
  rw [final_response_law, FinDist.expect_pure,
    final_response_result_at execution response transport bit guess valid stored]
  exact sub_le_sub_left penalty _

end Vegas.Examples.MonitoredGuessing
