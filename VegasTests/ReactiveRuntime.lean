/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Expr.Simple
import Vegas.Pending.ReactivePolicyFacts
import Vegas.Pending.ReactiveService
import Vegas.Pending.ReactiveSafety
import Vegas.Pending.ReactiveBinding
import Interaction.ReactiveFiniteAssessment
import Interaction.ReactiveReplayMenu
import Interaction.ReactiveResponseEmbedding

/-! # Binding and private recall in the one-message protocol -/

noncomputable section

namespace VegasTests.ReactiveRuntime

open GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime

private abbrev order : EventOrder where
  eventCount := 1
  predecessors _ := ∅
  predecessor_lt := by simp

private abbrev inputs : Fin 0 → EventGraph.EventField Bool simpleExpr := Fin.elim0
private abbrev outputs : Fin 1 → EventGraph.EventField Bool simpleExpr :=
  fun _ => .binding false .bool

private abbrev graph : EventGraph Bool simpleExpr where
  inputCount := 0
  order := order
  inputLayout := inputs
  outputLayout := outputs
  nodes _ := EventGraph.EventCode.bind
    (layout := EventGraph.fieldLayout inputs outputs) false .bool
  reads_available := by
    intro event field member
    exact False.elim (Finset.notMem_empty field member)
  payoffs := []

private def runtime : EventGraphRuntime graph where
  deadline _ := 2

private def leaks : MessageNetwork.ObservationRule Bool (Payload graph) :=
  fun _ _ => FinDist.pure ∅

private abbrev app := runtime.reactiveApplication leaks
private abbrev candidate : Handle graph := (false, .prepared 0)

private def initial : app.Execution :=
  ReactiveApplication.Execution.initial app
    (State.initial (graph := graph) (fun input => nomatch input))

private def submitted (bit : Bool) : app.Execution :=
  initial.respond app false (runtime.reactiveBinding leaks false 0 .bool (.success bit) 0)

/-- An explicit finite instance for this binding experiment. It includes
silence, either Boolean meaning, unopenable candidates, compiled decisions,
and every known replay. Other raw responses remain
outside this test instance; no equivalence to the full response space is claimed. -/
private def bindingMenu : app.ResponseMenu := by
  classical
  exact ReactiveApplication.ResponseMenu.withKnownReplays {
    actions := fun who _ view =>
      {⟨none⟩, runtime.reactiveBinding leaks who 0 .bool (.success false) 0,
        runtime.reactiveBinding leaks who 0 .bool (.success true) 0,
        runtime.reactiveBinding leaks who 0 .bool .failure 0,
        runtime.reactiveDecision leaks who 0 (.success false) view.application,
        runtime.reactiveDecision leaks who 0 (.success true) view.application,
        runtime.reactiveDecision leaks who 0 .failure view.application}
    nonempty := fun _ _ _ => ⟨⟨none⟩, by simp⟩ }

theorem finite_binding_histories (horizon : Nat) (scheduler : app.Scheduler) :
    Finite (bindingMenu.protocol (FinDist.pure initial.application) horizon scheduler).History :=
  inferInstance

theorem binding_menu_all_meanings (who : Bool) (past : List app.PlayerEntry)
    (view : app.PlayerView) (result : PublicationResult Bool) :
    runtime.reactiveBinding leaks who 0 .bool result 0 ∈ bindingMenu.actions who past view := by
  classical
  apply ReactiveApplication.ResponseMenu.base_available
  cases result with
  | failure => simp
  | success bit => cases bit <;> simp

theorem binding_menu_compiled_decision (who : Bool) (past : List app.PlayerEntry)
    (view : app.PlayerView) (result : PublicationResult Bool) :
    runtime.reactiveDecision leaks who 0 result view.application ∈
      bindingMenu.actions who past view := by
  classical
  apply ReactiveApplication.ResponseMenu.base_available
  cases result with
  | failure => simp
  | success bit => cases bit <;> simp

/-- An existing replay is available even after earlier submissions and leaks;
there is no extra numeric envelope-identifier bound. -/
theorem binding_menu_known_replay (execution : app.Execution) (who : Bool)
    (valid : execution.InputRecall app) (message : Message Bool app.Payload)
    (known : message ∈ execution.network.known who) :
    (⟨some (.replay message.id)⟩ : app.Action) ∈
      bindingMenu.actions who (execution.recall who) (execution.observe app who) := by
  classical
  exact ReactiveApplication.ResponseMenu.native_replay_available _ execution who valid message known

/-- The actual commitment adapter admits the canonical finite assessment.
This asserts consistency; no source compilation or nonzero-utility optimality
is assumed in this test. -/
theorem binding_assessment_consistent (horizon : Nat) (scheduler : app.Scheduler) :
    GameTheory.Protocol.InformationModel.BehavioralAssessment.IsSequentiallyConsistent
      (bindingMenu.bayesAssessment (FinDist.pure initial.application) horizon scheduler)
      (bindingMenu.decisionInformationAntichain (FinDist.pure initial.application)
        horizon scheduler) :=
  bindingMenu.bayesAssessment_consistent _ _ _

/-- One decision both fixes the hidden meaning and emits the public envelope. -/
theorem single_activation (bit : Bool) :
    (submitted bit).application.bindingResult candidate .bool = .success bit ∧
      (submitted bit).network.pending = [⟨(false, 0), .commitment 0 candidate⟩] ∧
      ((submitted bit).recall false).length = 1 ∧
      (submitted bit).environmentRecall = [] ∧
      (submitted bit).application.remembered 0 = none := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  exact runtime.reactiveBinding_result leaks false 0 .bool (.success bit) 0 initial rfl

/-- Reading a packet later cannot make a submitted handle mutable. -/
theorem replacement_fails (bit replacement : Bool) :
    ((submitted bit).respond app false
      (runtime.reactiveBinding leaks false 0 .bool (.success replacement)
        0)).application.bindingResult
        candidate .bool = .success bit := by
  cases bit <;> cases replacement <;> rfl

/-- Omitting opening material is irrevocable for that handle. -/
theorem late_opening_fails :
    let failed := initial.respond app false (runtime.reactiveBinding leaks false 0 .bool
      .failure 0)
    let next := failed.respond app false (runtime.reactiveBinding leaks false 0 .bool
      (.success true) 0)
    next.application.candidates.lookup candidate = .unopenable := rfl

/-- Neither the private bit nor its own recall becomes a scheduler observation. -/
theorem binding_hidden :
    (submitted false).observeEnvironment app = (submitted true).observeEnvironment app :=
  runtime.reactiveBinding_observation leaks false 0 .bool (.success false) (.success true)
    0 initial

private def granted : app.Execution :=
  { initial with application := { initial.application with serviceGrant := some 0 } }

private def chooseBit (law : FinDist Bool) : graph.BehavioralPolicy false :=
  fun _ _ _ => law.map PublicationResult.success

/-- The actual graph-policy compiler consumes the source random law at the
first activation and returns a complete submission action. -/
theorem compiler_samples_on_activation (law : FinDist Bool) :
    runtime.compileReactivePolicy leaks false (chooseBit law) [] (granted.observe app false) =
      law.map (fun bit => runtime.reactiveDecision leaks false 0 (.success bit)
        (granted.observe app false).application) := by
  rw [compileReactivePolicy, ReactiveApplication.Policy.recover_eq _ _ _ _ .nil]
  have actor : graph.actor? 0 = some false := rfl
  rw [prescribedReactivePolicy_apply]
  simp [prescribedReactiveResponse, reactiveAlreadySubmitted, granted, initial,
    ReactiveApplication.Execution.initial, ReactiveApplication.Execution.observe,
    app, reactiveApplication, State.publicView, PublicView.EventReady, State.initial,
    EventGraph.Config.initial, EventGraph.normalizePolicy, chooseBit,
    FinDist.map_comp, Function.comp_def, actor]

/-- The finite instance admits every possible compiled first response, for
every source distribution on Boolean values. -/
theorem compiled_first_response_available (law : FinDist Bool) (action : app.Action)
    (supported : action ∈ (runtime.compileReactivePolicy leaks false (chooseBit law)
      [] (granted.observe app false)).support) :
    action ∈ bindingMenu.actions false [] (granted.observe app false) := by
  rw [compiler_samples_on_activation, FinDist.support_map] at supported
  obtain ⟨bit, _, rfl⟩ := supported
  exact binding_menu_compiled_decision false [] _ (.success bit)

private theorem first_slot :
    reactiveFreshSlot (granted.observe app false).application = some 0 := by
  unfold reactiveFreshSlot
  split
  · congr 1
    exact (Nat.find_eq_zero _).mpr rfl
  · rename_i impossible
    exact False.elim (impossible ⟨0, rfl⟩)

private def firstAction (bit : Bool) : app.Action :=
  runtime.reactiveDecision leaks false 0 (.success bit) (granted.observe app false).application

private def firstResponse (bit : Bool) : app.Execution :=
  granted.respond app false (firstAction bit)

private theorem first_action (bit : Bool) : firstAction bit =
    ⟨some (.submit ⟨.commitment 0 candidate, some ⟨.bool, bit⟩⟩)⟩ := by
  change ReactiveApplication.Action.mk (app := app)
    ((reactiveFreshSlot (granted.observe app false).application).map _) = _
  rw [first_slot]
  rfl

/-- The compiled action fixes the sampled meaning and emits one binding packet,
with no application scratch-table writes or response-memory field. -/
theorem compiler_sends_and_binds (bit : Bool) :
    (firstResponse bit).application.bindingResult candidate .bool = .success bit ∧
      (firstResponse bit).network.pending = [⟨(false, 0), .commitment 0 candidate⟩] ∧
      (firstResponse bit).application.remembered 0 = none := by
  unfold firstResponse
  rw [first_action]
  cases bit <;> exact ⟨rfl, rfl, rfl⟩

private theorem first_consistent (bit : Bool) (law : FinDist Bool)
    (supported : bit ∈ law.support) :
    (runtime.prescribedReactivePolicy leaks false (chooseBit law)).Consistent
      ((firstResponse bit).recall false) := by
  have chosen : firstAction bit ∈ (runtime.compileReactivePolicy leaks false (chooseBit law)
      [] (granted.observe app false)).support := by
    rw [compiler_samples_on_activation, FinDist.support_map]
    exact ⟨bit, supported, rfl⟩
  rw [compileReactivePolicy, ReactiveApplication.Policy.recover_eq _ _ _ _ .nil] at chosen
  unfold firstResponse
  rw [first_action] at chosen ⊢
  simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
  exact .snoc _ .nil chosen

/-- Re-activating an owner that followed the policy does not resample or send
a competing commitment. Unsupported earlier choices instead trigger recovery. -/
theorem compiler_does_not_resample (bit : Bool) (law : FinDist Bool)
    (supported : bit ∈ law.support) :
    runtime.compileReactivePolicy leaks false (chooseBit law) ((firstResponse bit).recall false)
      ((firstResponse bit).observe app false) = FinDist.pure ⟨none⟩ := by
  have sent : runtime.reactiveAlreadySubmitted leaks ((firstResponse bit).recall false) 0
    = true := by
    unfold firstResponse
    rw [first_action]
    rfl
  have grant : ((firstResponse bit).observe app false).application.publicView.serviceGrant =
      some 0 := by
    unfold firstResponse
    rw [first_action]
    rfl
  rw [compileReactivePolicy, ReactiveApplication.Policy.recover_eq _ _ _ _
    (first_consistent bit law supported)]
  rw [prescribedReactivePolicy_apply]
  simp only [prescribedReactiveResponse, grant, sent, ↓reduceIte, FinDist.map_pure,
    FinDist.bind_const]

private theorem wrong_response_inconsistent :
    ¬ (runtime.prescribedReactivePolicy leaks false (chooseBit (FinDist.pure true))).Consistent
      ((firstResponse false).recall false) := by
  intro consistent
  have recalled : (firstResponse false).recall false = [] ++
      [⟨granted.observe app false, firstAction false,
        some ⟨(false, 0), .commitment 0 candidate⟩⟩] := by
    unfold firstResponse
    rw [first_action]
    rfl
  rw [recalled] at consistent
  have chosen := (ReactiveApplication.Policy.consistent_snoc_iff
    (runtime.prescribedReactivePolicy leaks false (chooseBit (FinDist.pure true))) []
    ⟨granted.observe app false, firstAction false,
      some ⟨(false, 0), .commitment 0 candidate⟩⟩).mp consistent
  have law := compiler_samples_on_activation (FinDist.pure true)
  rw [compileReactivePolicy, ReactiveApplication.Policy.recover_eq _ _ _ _ .nil] at law
  have same : firstAction false = firstAction true := by
    simpa only [law, FinDist.map_pure, FinDist.mem_support_pure, firstAction] using chosen.2
  rw [first_action, first_action] at same
  have sent := congrArg ReactiveApplication.Action.transmission same
  have material := ReactiveApplication.Transmission.submit.inj (Option.some.inj sent)
  have opening := congrArg Submission.opening material
  have raw := Option.some.inj opening
  have value := congrArg (fun raw : Raw simpleExpr => raw.as? .bool) raw
  cases value

/-- A wrong earlier binding does not suppress the desired submission. The
source policy is deterministic here; the rejected cached choice is false. -/
theorem compiler_recovers_wrong_choice :
    runtime.compileReactivePolicy leaks false (chooseBit (FinDist.pure true))
      ((firstResponse false).recall false) ((firstResponse false).observe app false) =
      FinDist.pure (runtime.reactiveDecision leaks false 0 (.success true)
        ((firstResponse false).observe app false).application) := by
  rw [compileReactivePolicy, ReactiveApplication.Policy.recover_eq_recovery _ _ _ _
    wrong_response_inconsistent]
  have actor : graph.actor? 0 = some false := rfl
  rw [recoverReactivePolicy_apply]
  simp [recoverReactiveResponse, firstResponse, first_action, reactiveRecoveryLaw_pure,
    granted, initial, ReactiveApplication.Execution.respond,
    ReactiveApplication.Execution.initial, ReactiveApplication.Execution.observe,
    app, reactiveApplication, State.publicView, PublicView.EventReady, State.initial,
    EventGraph.Config.initial, EventGraph.normalizePolicy, chooseBit, actor,
    submitStep, Submission.register, FinDist.map_pure]

/-- Binding recall follows the actual completion, even when an earlier
submitted candidate remembered the opposite intention. -/
theorem binding_recall_uses_completion :
    runtime.reactiveOriginal leaks false ((firstResponse false).recall false)
      [some ⟨0, .success false⟩]
      [((false, 1), true)] ⟨0, .success true⟩ = ⟨0, .success true⟩ := rfl

/-- Reserved service gives the owner one activation. Additional activations
are choices of the network policy at its ordinary opportunities. -/
example : interactionVisit (graph := graph) 2 0 =
    [.grant 0, .player false, .wire, .wire, .includeLatest 0 false, .sample 0] := rfl

example (who : Bool) : (NetworkChoice.activate who).command runtime leaks = .activate who := rfl

/-- Real partial-leak activation and an arbitrary response occur before inclusion.
Even a competing submission by Alice cannot change the first envelope's meaning.
This checks the inclusion premises rather than assuming an unchanged application. -/
theorem binding_after_passive_reaction
    (observationRule : MessageNetwork.ObservationRule Bool (Payload graph))
    (players : Bool → (runtime.reactiveApplication observationRule).Policy)
    (observer : Bool) (result : PublicationResult Bool) :
    let reactive := runtime.reactiveApplication observationRule
    let start := ReactiveApplication.Execution.initial reactive
      (State.initial (graph := graph) (fun input => nomatch input))
    let sent := start.respond reactive false
      (runtime.reactiveBinding observationRule false 0 .bool result 0)
    ((reactive.dispatch players (.activate observer) sent).map fun next =>
      (next.includePending reactive (false, 0)).application.config.outputs 0) =
        FinDist.pure (some result) := by
  dsimp only
  let reactive := runtime.reactiveApplication observationRule
  let start := ReactiveApplication.Execution.initial reactive
    (State.initial (graph := graph) (fun input => nomatch input))
  let sent := start.respond reactive false
    (runtime.reactiveBinding observationRule false 0 .bool result 0)
  apply FinDist.eq_pure_of_support_subset_singleton
  intro output member
  obtain ⟨next, supported, rfl⟩ := FinDist.support_map .. ▸ member
  have reached : next ∈ (reactive.runRounds (fun _ _ => FinDist.pure (.activate observer))
      players 1 sent).support := by
    simpa only [ReactiveApplication.runRounds, ReactiveApplication.round, FinDist.pure_bind,
      FinDist.bind_pure] using supported
  obtain ⟨observed, activated, response⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  have observedFacts : observed.application = sent.application ∧
      observed.network.pending = sent.network.pending := by
    simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_comp] at activated
    obtain ⟨read, _, rfl⟩ := FinDist.support_map .. ▸ activated
    exact ⟨rfl, rfl⟩
  dsimp only [ReactiveApplication.resume, ReactiveApplication.Command.actor?,
    ReactiveApplication.invoke] at response
  obtain ⟨action, _, rfl⟩ := FinDist.support_map .. ▸ response
  have facts := runtime.reactive_respond_application observationRule observed observer action
  have configEq : _ = start.application.config := facts.1.trans
    ((congrArg (fun state => state.config) observedFacts.1).trans
      (runtime.reactive_respond_application observationRule start false
        (runtime.reactiveBinding observationRule false 0 .bool result 0)).1)
  have publicEq : _ = start.application.publicView := facts.2.trans
    ((congrArg (fun state => state.publicView) observedFacts.1).trans
      (runtime.reactive_respond_application observationRule start false
        (runtime.reactiveBinding observationRule false 0 .bool result 0)).2)
  have observedPending : observed.network.lookup (false, 0) =
      some ⟨(false, 0), .commitment 0 candidate⟩ := by
    unfold MessageNetwork.lookup
    rw [observedFacts.2]
    rfl
  have pending : (observed.respond reactive observer action).network.lookup
      (false, 0) = some ⟨(false, 0), .commitment 0 candidate⟩ := by
    rcases action with ⟨transmission⟩
    cases transmission with
    | none => exact observedPending
    | some transmission =>
        cases transmission with
        | submit material =>
            change (_ ++ [_]).find? _ = _
            rw [List.find?_append]
            change (observed.network.lookup (false, 0)).or _ = _
            rw [observedPending, Option.some_or]
        | replay id =>
            simp only [ReactiveApplication.Execution.respond]
            unfold MessageNetwork.replay
            split
            · exact observedPending
            · change (_ ++ [_]).find? _ = _
              rw [List.find?_append]
              change (observed.network.lookup (false, 0)).or _ = _
              rw [observedPending, Option.some_or]
  have ready : start.application.config.cut.Ready 0 := by
    change initial.application.config.cut.Ready 0
    decide
  have timely : start.application.WithinDeadline runtime 0 := by
    change 0 < 2
    decide
  have nextReady := configEq.symm ▸ ready
  have nextTimely : (ReactiveApplication.Execution.respond reactive observed observer
      action).application.WithinDeadline runtime 0 := by
    have clocks : (observed.respond reactive observer action).application.clock =
        start.application.clock := congrArg PublicView.clock publicEq
    have activated : (observed.respond reactive observer action).application.activatedAt =
        start.application.activatedAt := congrArg PublicView.activatedAt publicEq
    simpa only [State.WithinDeadline, clocks, activated] using timely
  have acceptedEq : (observed.respond reactive observer action).application.accepted =
      start.application.accepted := congrArg PublicView.accepted publicEq
  have nextVacant := congrFun acceptedEq (.inr 0)
  have nextUnused : (ReactiveApplication.Execution.respond reactive observed observer
      action).application.HandleUnused candidate := by
    intro field associated
    change (observed.respond reactive observer action).application.accepted field =
      some candidate at associated
    rw [acceptedEq] at associated
    cases field with
    | inl input => exact Fin.elim0 input
    | inr event => cases associated
  obtain ⟨included, _⟩ := runtime.reactiveBinding_continuation_include observationRule false 0
    .bool rfl rfl rfl result 0 0 start (observed.respond reactive observer action) rfl
    (fun _ _ => FinDist.pure (.activate observer)) players 1 reached pending nextReady nextTimely
    nextVacant nextUnused
  change ((observed.respond reactive observer action).includePending reactive
    (false, 0)).application.config.outputs 0 = some result
  rw [included]
  exact EventGraph.Config.complete_output_same ..

end VegasTests.ReactiveRuntime
