/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ValueSwapPairs
import Vegas.Pending.PhaseReactiveValueSwap
import Vegas.Pending.PhaseTraffic
import Interaction.ReactiveRecallInvariant

/-! # Immutable ordinary private inputs in actual physical phase operations

Only ordinary private-input fields are transposed. Program output values,
program actions and every commitment candidate are fixed. This distinction is
essential: an initial binding with failure is not an ordinary private input.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace HiddenSwap

open Classical in
/-- Transpose two supplied values at every ordinary private input; every
program output and every non-private input retains its value. -/
def privateInputPairs (first second : graph.Inputs) : graph.SwapPairs where
  pair field := match field with
    | .inl input => if ∃ owner payload, graph.inputLayout input = .privateInput owner payload then
        some (first input, second input) else none
    | .inr _ => none
  public_none field visible := by
    cases field with
    | inl input =>
      dsimp only
      split
      · rename_i ordinary
        obtain ⟨owner, payload, kind⟩ := ordinary
        change (graph.inputLayout input).IsPublic at visible
        rw [kind] at visible
        exact visible.elim
      · rfl
    | inr event => rfl
  binding_success _ _ _ _ _ _ impossible := by cases impossible

/-- Initial ordinary private values have no candidate handles. The physical
candidate table and all raw responses therefore remain unchanged. -/
def privateInputs (first second : graph.Inputs) : HiddenSwap graph :=
  HiddenSwap.ofPairs (privateInputPairs first second) (fun _ => none)

variable (first second : graph.Inputs)

theorem privateInputs_raw (candidate : Handle graph) :
    (privateInputs first second).raw candidate = id := rfl

theorem privateInputs_output (event : graph.EventId) :
    (privateInputs first second).values.value (.inr event) = id := rfl

theorem privateInputs_binding (field : graph.Field) (owner : Player) (payload : L.Ty)
    (binding : graph.layout field = .binding owner payload) :
    (privateInputs first second).values.value field = id := by
  classical
  cases field with
  | inr event => rfl
  | inl input =>
    change pairSwap (if ∃ owner payload,
      graph.inputLayout input = .privateInput owner payload then some _ else none) = id
    have absent : ¬ ∃ other value, graph.inputLayout input = .privateInput other value := by
      rintro ⟨other, value, kind⟩
      cases binding.symm.trans kind
    rw [ite_eq_right absent]
    rfl

theorem privateInputs_action (event : graph.EventId) :
    (privateInputs first second).values.action event = id := by
  funext action
  change (privateInputPairs first second).action event action = action
  unfold SwapPairs.action
  cases nodeView graph event <;> simp only [privateInputPairs, pairSwap, id_eq, cast_cast, cast_eq]

theorem privateInputs_expiry (event : graph.EventId) :
    (privateInputs first second).values.ExpiryFixed event :=
  ValueSwap.ofPairs_expiryFixed (privateInputPairs first second) event

theorem privateInputs_compatible (event : graph.EventId) (candidate : Handle graph) :
    BindCompatible (privateInputs first second) event candidate :=
  HiddenSwap.bindCompatible_ofPairs_none (privateInputPairs first second) (fun _ => none) rfl rfl

theorem privateInputs_revealFixed (state : State graph) (event : graph.EventId) :
    RevealFixed (privateInputs first second) state event := by
  unfold RevealFixed
  cases nodeView graph event with
  | bind | sample => trivial
  | resolve owner payload binding checks output code =>
    exact ⟨privateInputs_binding first second _ owner payload binding.layout_eq,
      fun _ _ => rfl⟩

theorem privateInputs_input
    (unchanged : ∀ input, (¬ ∃ owner payload,
      graph.inputLayout input = .privateInput owner payload) → first input = second input)
    (input : graph.InputId) :
    (privateInputs first second).values.value (.inl input) (first input) = second input := by
  classical
  change pairSwap (if ∃ owner payload, graph.inputLayout input = .privateInput owner payload then
    some (first input, second input) else none) (first input) = _
  by_cases ordinary : ∃ owner payload, graph.inputLayout input = .privateInput owner payload
  · rw [ite_eq_left ordinary]
    exact Equiv.swap_apply_left _ _
  · rw [ite_eq_right ordinary]
    exact unchanged input ordinary

theorem privateInputs_visible (focal : Player)
    (agree : ∀ input, graph.fieldVisibleTo focal (.inl input) → first input = second input)
    (field : graph.Field) (visible : graph.fieldVisibleTo focal field) :
    (privateInputs first second).values.value field = id := by
  classical
  cases field with
  | inr event => rfl
  | inl input =>
    change pairSwap (if ∃ owner payload, graph.inputLayout input = .privateInput owner payload then
      some (first input, second input) else none) = id
    rw [agree input visible]
    split
    · simp only [pairSwap, Equiv.swap_self]
      rfl
    · rfl

theorem privateInputs_candidates
    (catalogue : CommitmentCandidates Player (CandidateSlot graph) (Raw L)) :
    (privateInputs first second).candidates catalogue = catalogue := by
  apply congrArg CommitmentCandidates.mk
  funext owner slot
  change swapCandidate id (catalogue.lookup (owner, slot)) = catalogue.lookup (owner, slot)
  cases catalogue.lookup (owner, slot) <;> rfl

end HiddenSwap

variable [DecidableEq Player]

namespace HiddenSwap

theorem privateInputs_initial (first second : graph.Inputs)
    (unchanged : ∀ input, (¬ ∃ owner payload,
      graph.inputLayout input = .privateInput owner payload) → first input = second input) :
    (State.initial first).swap (privateInputs first second) = State.initial second := by
  have configs : (EventGraph.Config.initial first).swap (privateInputs first second).values =
      EventGraph.Config.initial second := by
    apply EventGraph.Config.ext_fields
    · exact funext (privateInputs_input first second unchanged)
    · rfl
    · rfl
    · rfl
  have candidates : (State.initial first).candidates = (State.initial second).candidates := by
    apply congrArg CommitmentCandidates.mk
    funext owner slot
    cases slot with
    | prepared serial => rfl
    | initial input =>
      change State.candidateOfValue owner (graph.inputLayout input) (first input) =
        State.candidateOfValue owner (graph.inputLayout input) (second input)
      by_cases ordinary : ∃ other payload, graph.inputLayout input = .privateInput other payload
      · obtain ⟨other, payload, kind⟩ := ordinary
        have irrelevant (field : EventField Player L) (left right : field.Value)
            (named : field = .privateInput other payload) :
            State.candidateOfValue owner field left = State.candidateOfValue owner field right := by
          cases named
          rfl
        exact irrelevant _ _ _ kind
      · rw [unchanged input ordinary]
  change (⟨_, _, _, _, _⟩ : State graph) = ⟨_, _, _, _, _⟩
  rw [State.mk.injEq]
  exact ⟨configs, rfl, (privateInputs_candidates first second _).trans candidates, rfl, rfl⟩

theorem privateInputs_playerView (first second : graph.Inputs) (focal : Player)
    (agree : ∀ input, graph.fieldVisibleTo focal (.inl input) → first input = second input)
    (state : State graph) :
    (state.swap (privateInputs first second)).playerView focal = state.playerView focal := by
  rw [State.swap_playerView]
  unfold PlayerView.swap State.playerView
  rw [PlayerObservation.swap_eq_self (privateInputs first second).values
    (privateInputs_visible first second focal agree)
    (fun event _ => privateInputs_action first second event)]
  congr 1
  funext slot
  change swapCandidate id (state.candidates.lookup (focal, slot)) =
    state.candidates.lookup (focal, slot)
  cases state.candidates.lookup (focal, slot) <;> rfl

end HiddenSwap

namespace PhaseRuntimeState

/-- The supplied transposition connects the actual initialized states of any
two input vectors differing only at ordinary private-input fields. -/
theorem initial_privateInputs (plan : RuntimePhasePlan graph) (first second : graph.Inputs)
    (unchanged : ∀ input, (¬ ∃ owner payload,
      graph.inputLayout input = .privateInput owner payload) → first input = second input) :
    (initial plan first).swap (HiddenSwap.privateInputs first second) = initial plan second := by
  unfold initial
  rw [← settle_swap _ _ _ _ _ _ (HiddenSwap.privateInputs_expiry first second)]
  simp only [RecoveryState.swap, HiddenSwap.privateInputs_initial first second unchanged]
  rfl

/-- The existing physical normalizer commutes with ordinary private-input
changes, without a clear-state, finite-prior or successful-binding premise. -/
theorem handle_privateInputs (runtime : EventGraphRuntime graph)
    (first second : graph.Inputs) (state : PhaseRuntimeState graph)
    (message : Message Player (CommitAttemptPacket graph)) :
    (state.swap (HiddenSwap.privateInputs first second)).handle runtime message =
      (state.handle runtime message).map
        (PhaseRuntimeState.swap (HiddenSwap.privateInputs first second)) := by
  exact handle_swap runtime _ state message (HiddenSwap.privateInputs_expiry first second)
    (fun _ _ event candidate _ _ =>
      HiddenSwap.privateInputs_compatible first second event candidate)
    (fun _ event _ _ =>
      HiddenSwap.privateInputs_revealFixed first second state.current.native event)

/-- Clock, chance and expiry share their actual native draws, followed by the
same phase normalization and public retirement record. -/
theorem environment_privateInputs (runtime : EventGraphRuntime graph)
    (first second : graph.Inputs) (state : PhaseRuntimeState graph)
    (command : EnvironmentCommand graph) :
    (state.swap (HiddenSwap.privateInputs first second)).environment runtime command =
      (state.environment runtime command).map
        (PhaseRuntimeState.swap (HiddenSwap.privateInputs first second)) := by
  let swap := HiddenSwap.privateInputs first second
  unfold environment
  rw [swap_commandAllowed]
  split
  · simp only [swap_current, RecoveryState.swap_native]
    rw [EventGraphRuntime.environmentStep_swap runtime swap state.current.native command
      (fun event _ _ _ _ _ => HiddenSwap.privateInputs_expiry first second event),
      PMF.map_comp, PMF.map_comp]
    apply map_congr_on_support _
    intro native _
    have updated :
        ({ state.swap swap with
          current := (state.current.swap swap).environmentResult command (native.swap swap) } :
            PhaseRuntimeState graph) =
        ({ state with current := state.current.environmentResult command native } :
          PhaseRuntimeState graph).swap swap := by
      cases command <;> rfl
    simp only [Function.comp_apply]
    rw [updated, normalize_swap swap _ (HiddenSwap.privateInputs_expiry first second)]
  · exact (PMF.pure_map _ _).symm

/-- The real command kernels admit a shared-draw coupling retaining the exact
immutable input transformation at every supported successor. -/
theorem environment_privateInputs_coupling (runtime : EventGraphRuntime graph)
    (first second : graph.Inputs) (state : PhaseRuntimeState graph)
    (command : EnvironmentCommand graph) :
    ∃ joint : PMF (PhaseRuntimeState graph × PhaseRuntimeState graph),
      joint.map Prod.fst =
        (state.swap (HiddenSwap.privateInputs first second)).environment runtime command ∧
      joint.map Prod.snd = state.environment runtime command ∧
      ∀ pair ∈ joint.support, pair.1 = pair.2.swap (HiddenSwap.privateInputs first second) := by
  let swap := HiddenSwap.privateInputs first second
  let law := state.environment runtime command
  refine ⟨law.map (fun next => (next.swap swap, next)), ?_, ?_, ?_⟩
  · rw [PMF.map_comp]
    exact (environment_privateInputs runtime first second state command).symm
  · rw [PMF.map_comp]
    exact PMF.map_id _
  · intro pair present
    obtain ⟨next, _supported, rfl⟩ :=
      (PMF.mem_support_map_iff (fun next => (next.swap swap, next)) law _).mp present
    rfl

end PhaseRuntimeState
end Vegas.EventGraphRuntime

namespace Vegas.EventGraphRuntime.HiddenSwap

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (first second : graph.Inputs)

local notation "app" => phaseApplication runtime leaks
local notation "swap" => privateInputs first second

omit [DecidableEq Player] in
theorem privateInputs_submission (material : WitnessedSubmission graph) :
    material.swap swap = material := by
  rcases material with ⟨⟨packet, opening⟩, evidence⟩
  cases packet <;> simp only [WitnessedSubmission.swap, Submission.swap,
    privateInputs_raw, Option.map_id, id_eq]

theorem privateInputs_phaseAction (response : (app).Action) :
    (swap).phaseAction response = response := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material =>
      change (⟨some (material.swap swap)⟩ : (app).Action) = _
      rw [privateInputs_submission]

theorem privateInputs_observeEnvironment (execution : (app).Execution) :
    ((swap).phaseExecution execution).observeEnvironment (app) =
      execution.observeEnvironment (app) := by
  change (⟨execution.network.publicView,
    (execution.application.swap swap).publicView, execution.receipts⟩ :
      (app).EnvironmentView) = _
  rw [PhaseRuntimeState.swap_publicView]
  rfl

/-- The immutable input transformation fixes an actual focal callback view,
including the sampled network observation, receipts and complete phase archive. -/
theorem privateInputs_phaseView_observe (execution : (app).Execution) (focal : Player)
    (agree : ∀ input, graph.fieldVisibleTo focal (.inl input) → first input = second input) :
    (swap).phaseView (execution.observe (app) focal) = execution.observe (app) focal := by
  change (⟨execution.network.observe focal,
    (PlayerView.swap swap (execution.application.current.native.playerView focal),
      execution.application.publicView), execution.receipts⟩ : (app).PlayerView) = _
  rw [← State.swap_playerView, privateInputs_playerView first second focal agree]
  rfl

/-- Current focal observations agree without changing the physical message
network or its supplied observation rule. -/
theorem privateInputs_observe (execution : (app).Execution) (focal : Player)
    (agree : ∀ input, graph.fieldVisibleTo focal (.inl input) → first input = second input) :
    ((swap).phaseExecution execution).observe (app) focal = execution.observe (app) focal := by
  change (⟨execution.network.observe focal,
    ((execution.application.current.native.swap swap).playerView focal,
      (execution.application.swap swap).publicView), execution.receipts⟩ :
        (app).PlayerView) = _
  rw [privateInputs_playerView first second focal agree, PhaseRuntimeState.swap_publicView]
  rfl

/-- Every actual remembered callback is fixed for the focal player. This uses
its genuine recorded prefix, rather than imposing a condition on arbitrary
syntactic player entries. -/
theorem privateInputs_recall_history (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((app).protocol initial horizon scheduler).Trace (some control))
    (focal : Player)
    (agree : ∀ input, graph.fieldVisibleTo focal (.inl input) → first input = second input) :
    ((swap).phaseExecution control.execution).recall focal = control.execution.recall focal := by
  change (control.execution.recall focal).map (swap).phaseEntry = _
  conv_rhs => rw [← List.map_id (control.execution.recall focal)]
  apply List.map_congr_left
  intro entry recorded
  obtain ⟨before, _played, _actor, viewed⟩ :=
    (app).recorded_response_prefix initial horizon scheduler control trace focal entry recorded
  unfold phaseEntry
  rw [viewed, privateInputs_phaseView_observe runtime leaks first second before.execution
    focal agree, privateInputs_phaseAction, ← viewed]
  rfl

theorem privateInputs_traffic (execution : (app).Execution) (focal : Player)
    (agree : ∀ input, graph.fieldVisibleTo focal (.inl input) → first input = second input)
    (recalled : ((swap).phaseExecution execution).recall focal = execution.recall focal) :
    phaseTraffic runtime leaks focal ((swap).phaseExecution execution) =
      phaseTraffic runtime leaks focal execution := by
  have view := privateInputs_playerView first second focal agree
    execution.application.current.native
  change (execution.network, execution.receipts, execution.environmentRecall, _, _) = _
  rw [recalled]
  change (_, _, _, _, ((execution.application.current.native.swap swap).playerView focal,
    (execution.application.swap swap).publicView)) = _
  rw [view, PhaseRuntimeState.swap_publicView]
  rfl

/-- An actual raw history retains all focal traffic under an ordinary private
input change invisible to that player. The original joint input prior is not
modified or assumed to factor. -/
theorem privateInputs_traffic_history (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((app).protocol initial horizon scheduler).Trace (some control))
    (focal : Player)
    (agree : ∀ input, graph.fieldVisibleTo focal (.inl input) → first input = second input) :
    phaseTraffic runtime leaks focal ((swap).phaseExecution control.execution) =
      phaseTraffic runtime leaks focal control.execution :=
  privateInputs_traffic runtime leaks first second control.execution focal agree
    (privateInputs_recall_history runtime leaks first second initial horizon scheduler control
      trace focal agree)

/-- A focal raw policy sees exactly the same complete callback, including its
actual own history. No restriction on unilateral response laws is imposed. -/
theorem privateInputs_focal_dispatch_history (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((app).protocol initial horizon scheduler).Trace (some control))
    (focal : Player)
    (agree : ∀ input, graph.fieldVisibleTo focal (.inl input) → first input = second input)
    (players : Player → (app).Policy) :
    (((app).dispatch players (.activate focal) ((swap).phaseExecution control.execution)).map
      (phaseTraffic runtime leaks focal)) =
    (((app).dispatch players (.activate focal) control.execution).map
      (phaseTraffic runtime leaks focal)) :=
  phaseTraffic_focal_dispatch runtime leaks _ _ focal
    (privateInputs_traffic_history runtime leaks first second initial horizon scheduler control
      trace focal agree) players

theorem privateInputs_observe_map (execution : (app).Execution) (actor : Player) :
    ((swap).phaseExecution execution).observe (app) actor =
      (swap).phaseView (execution.observe (app) actor) := by
  change (⟨execution.network.observe actor,
    ((execution.application.current.native.swap swap).playerView actor,
      (execution.application.swap swap).publicView), execution.receipts⟩ :
        (app).PlayerView) = _
  rw [State.swap_playerView, PhaseRuntimeState.swap_publicView]
  rfl

/-- Actual submissions commute with the immutable input change. Their raw
syntax, evidence requests and emitted packets are identical; only recalled
private before-views are transformed. -/
theorem privateInputs_respond (execution : (app).Execution) (actor : Player)
    (response : (app).Action) :
    ((swap).phaseExecution execution).respond (app) actor response =
      (swap).phaseExecution (execution.respond (app) actor response) := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      change (⟨execution.application.swap swap, execution.network, execution.receipts,
        fun observer => if observer = actor then (execution.recall actor).map (swap).phaseEntry ++
          [⟨((swap).phaseExecution execution).observe (app) actor, ⟨none⟩, none⟩]
        else (execution.recall observer).map (swap).phaseEntry,
        execution.environmentRecall⟩ : (app).Execution) =
        (swap).phaseExecution ⟨execution.application, execution.network, execution.receipts,
          fun observer => if observer = actor then execution.recall actor ++
            [⟨execution.observe (app) actor, ⟨none⟩, none⟩] else execution.recall observer,
          execution.environmentRecall⟩
      rw [privateInputs_observe_map]
      change ReactiveApplication.Execution.mk _ _ _ _ _ = ReactiveApplication.Execution.mk _ _ _ _ _
      congr 1
      funext observer
      by_cases same : observer = actor
      · subst observer
        simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil]
        rfl
      · simp only [same, ↓reduceIte]
  | some material =>
      have submitted : (execution.application.swap swap).submit actor material =
          (execution.application.submit actor material).swap swap := by
        simpa only [privateInputs_submission] using
          PhaseRuntimeState.submit_swap swap execution.application actor material
      have fixed : material.evidence.FixedBy swap := by
        cases material.evidence <;> trivial
      have emitted := PhaseRuntimeState.emit_swap swap
        (execution.application.submit actor material) actor (execution.network.known actor)
          material fixed
      rw [privateInputs_submission] at emitted
      let after := execution.application.submit actor material
      let sent := execution.network.submit actor
        (after.emit actor (execution.network.known actor) material)
      change (⟨(execution.application.swap swap).submit actor material,
        (execution.network.submit actor
          (((execution.application.swap swap).submit actor material).emit actor
            (execution.network.known actor) material)).2, execution.receipts,
        fun observer => if observer = actor then (execution.recall actor).map (swap).phaseEntry ++
          [⟨((swap).phaseExecution execution).observe (app) actor, ⟨some material⟩,
            some (execution.network.submit actor
              (((execution.application.swap swap).submit actor material).emit actor
                (execution.network.known actor) material)).1⟩]
        else (execution.recall observer).map (swap).phaseEntry,
        execution.environmentRecall⟩ : (app).Execution) =
        (swap).phaseExecution ⟨after, sent.2, execution.receipts,
          fun observer => if observer = actor then execution.recall actor ++
            [⟨execution.observe (app) actor, ⟨some material⟩, some sent.1⟩]
          else execution.recall observer, execution.environmentRecall⟩
      rw [submitted, emitted, privateInputs_observe_map]
      change ReactiveApplication.Execution.mk _ _ _ _ _ = ReactiveApplication.Execution.mk _ _ _ _ _
      congr 1
      funext observer
      by_cases same : observer = actor
      · subst observer
        simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil]
        simp only [phaseEntry, privateInputs_phaseAction]
        rfl
      · simp only [same, ↓reduceIte]

/-- Inclusion commutes at the complete execution level, including acceptance
receipts. Malformed and stale-attempt packets are covered by the actual handler. -/
theorem privateInputs_includePending (execution : (app).Execution) (id : MessageId Player) :
    ((swap).phaseExecution execution).includePending (app) id =
      (swap).phaseExecution (execution.includePending (app) id) := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  simp only [phaseExecution_network]
  cases found : execution.network.lookup id with
  | none => rfl
  | some message =>
      have handled := PhaseRuntimeState.handle_privateInputs runtime first second
        execution.application message
      change (app).handle (execution.application.swap swap) message =
        ((app).handle execution.application message).map (PhaseRuntimeState.swap swap) at handled
      simp only [phaseExecution_application]
      rw [handled]
      cases (app).handle execution.application message <;> rfl

/-- All actual execution commands commute with the same immutable input
transformation. Activation uses the supplied pending-message sampler on the
unchanged network; clock, chance, expiry and rollback use their actual kernels. -/
theorem privateInputs_environmentStep (execution : (app).Execution) (command : (app).Command) :
    ((swap).phaseExecution execution).environmentStep (app) command =
      (execution.environmentStep (app) command).map (swap).phaseExecution := by
  unfold ReactiveApplication.Execution.environmentStep
  rw [privateInputs_observeEnvironment, PMF.map_comp]
  cases command with
  | activate actor =>
      simp only [phaseExecution_network, PMF.map_comp]
      rfl
  | wait =>
      simp only [PMF.pure_map]
      rfl
  | «include» id =>
      simp only [PMF.pure_map]
      rw [privateInputs_includePending]
      rfl
  | application command =>
      simp only [phaseExecution_application]
      change PMF.map _ (PMF.map _
        ((execution.application.swap swap).environment runtime command)) = _
      rw [PhaseRuntimeState.environment_privateInputs, PMF.map_comp, PMF.map_comp, PMF.map_comp]
      rfl

/-- The transposition sends one actual initialized execution to the other,
including its empty network and original recall fields. -/
theorem privateInputs_initial_execution (plan : RuntimePhasePlan graph)
    (unchanged : ∀ input, (¬ ∃ owner payload,
      graph.inputLayout input = .privateInput owner payload) → first input = second input) :
    (swap).phaseExecution (ReactiveApplication.Execution.initial (app)
      (PhaseRuntimeState.initial plan first)) =
    ReactiveApplication.Execution.initial (app) (PhaseRuntimeState.initial plan second) := by
  change (⟨(PhaseRuntimeState.initial plan first).swap swap, .empty, [], fun _ => [], []⟩ :
    (app).Execution) = _
  rw [PhaseRuntimeState.initial_privateInputs plan first second unchanged]
  rfl

/-- Every physical command has a joint execution law preserving both the exact
immutable-input relation and the entire focal communication readout. The focal
recall premise is supplied by every actual raw history above. -/
theorem privateInputs_environmentStep_coupling (execution : (app).Execution)
    (focal : Player)
    (agree : ∀ input, graph.fieldVisibleTo focal (.inl input) → first input = second input)
    (recalled : ((swap).phaseExecution execution).recall focal = execution.recall focal)
    (command : (app).Command) :
    ∃ joint : PMF ((app).Execution × (app).Execution),
      joint.map Prod.fst = ((swap).phaseExecution execution).environmentStep (app) command ∧
      joint.map Prod.snd = execution.environmentStep (app) command ∧
      ∀ pair ∈ joint.support,
        pair.1 = (swap).phaseExecution pair.2 ∧
        phaseTraffic runtime leaks focal pair.1 = phaseTraffic runtime leaks focal pair.2 := by
  let law := execution.environmentStep (app) command
  refine ⟨law.map (fun next => ((swap).phaseExecution next, next)), ?_, ?_, ?_⟩
  · rw [PMF.map_comp]
    exact (privateInputs_environmentStep runtime leaks first second execution command).symm
  · rw [PMF.map_comp]
    exact PMF.map_id _
  · intro pair present
    obtain ⟨next, supported, pairEq⟩ :=
      (PMF.mem_support_map_iff (fun next => ((swap).phaseExecution next, next)) law _).mp present
    subst pair
    refine ⟨rfl, privateInputs_traffic runtime leaks first second next focal agree ?_⟩
    change (next.recall focal).map (swap).phaseEntry = next.recall focal
    rw [(app).environmentStep_recall execution next command supported]
    exact recalled

/-- An arbitrary focal policy has an actual shared-response coupling with the
same immutable-input relation at each successor, retaining its full recall and
phase traffic. It may use every part of its permitted input. -/
theorem privateInputs_focal_policy_coupling (execution : (app).Execution) (focal : Player)
    (agree : ∀ input, graph.fieldVisibleTo focal (.inl input) → first input = second input)
    (recalled : ((swap).phaseExecution execution).recall focal = execution.recall focal)
    (policy : (app).Policy) :
    ∃ joint : PMF ((app).Execution × (app).Execution),
      joint.map Prod.fst = (app).invoke (fun _ => policy) focal ((swap).phaseExecution execution) ∧
      joint.map Prod.snd = (app).invoke (fun _ => policy) focal execution ∧
      ∀ pair ∈ joint.support,
        pair.1 = (swap).phaseExecution pair.2 ∧
        phaseTraffic runtime leaks focal pair.1 = phaseTraffic runtime leaks focal pair.2 := by
  let law := policy (execution.recall focal) (execution.observe (app) focal)
  let firstResponse := fun response =>
    ((swap).phaseExecution execution).respond (app) focal response
  let secondResponse := fun response => execution.respond (app) focal response
  have same := privateInputs_traffic runtime leaks first second execution focal agree recalled
  refine ⟨law.map (fun response => (firstResponse response, secondResponse response)),
    ?_, ?_, ?_⟩
  · rw [PMF.map_comp]
    unfold ReactiveApplication.invoke
    rw [recalled, privateInputs_observe runtime leaks first second execution focal agree]
    rfl
  · rw [PMF.map_comp]
    rfl
  · intro pair present
    obtain ⟨response, _supported, pairEq⟩ :=
      (PMF.mem_support_map_iff (fun response => (firstResponse response, secondResponse response))
        law _).mp present
    subst pair
    exact ⟨privateInputs_respond runtime leaks first second execution focal response,
      phaseTraffic_focal_response runtime leaks _ _ focal same response⟩

/-- Map only physical private data in a raw protocol state. Scheduling,
remaining fuel and the selected actor are unchanged. -/
def privateInputs_state (before : (app).ProtocolState) : (app).ProtocolState :=
  before.map fun control => { control with execution := (swap).phaseExecution control.execution }

/-- The actual raw transition uses the same scheduler and literal joint action.
Its initial distribution is transported as a whole, not replaced by independent
input marginals. -/
theorem privateInputs_transition (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) (before : (app).ProtocolState)
    (joint : Player → Option (app).Action) :
    ((app).transition initial horizon scheduler before joint).map
      (privateInputs_state runtime leaks first second) =
    (app).transition (initial.map (PhaseRuntimeState.swap swap)) horizon scheduler
      (privateInputs_state runtime leaks first second before) joint := by
  cases before with
  | none =>
      simp only [ReactiveApplication.transition, privateInputs_state, Option.map_none,
        PMF.map_comp]
      rfl
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          simp only [ReactiveApplication.transition, privateInputs_state, Option.map_some,
            PMF.pure_map]
          exact congrArg (fun next => PMF.pure (some
            (ReactiveApplication.Control.mk remaining none next)))
            (privateInputs_respond runtime leaks first second execution who
              ((joint who).getD ⟨none⟩)).symm
      | none =>
          cases remaining with
          | zero =>
              simp only [ReactiveApplication.transition, privateInputs_state, Option.map_some,
                PMF.pure_map]
          | succ remaining =>
              simp only [ReactiveApplication.transition, privateInputs_state, Option.map_some,
                PMF.map_bind, privateInputs_observeEnvironment]
              congr 1
              funext command
              rw [privateInputs_environmentStep, PMF.map_comp, PMF.map_comp]
              rfl

/-- Every complete raw trace has a counterpart under the immutable input
transformation. This is a structural legal-history witness: no compiler policy
or preservation of the original prior under the transposition is assumed. -/
def privateInputs_trace (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) :
    ∀ {before}, ((app).protocol initial horizon scheduler).Trace before →
      ((app).protocol (initial.map (PhaseRuntimeState.swap swap)) horizon scheduler).Trace
        (privateInputs_state runtime leaks first second before)
  | _, .start => .start
  | before, .extend prior joint legal reached =>
      .extend (privateInputs_trace initial horizon scheduler prior) joint
        (by
          rename_i source
          cases source <;> exact legal)
        (by
          rename_i source
          have mapped : privateInputs_state runtime leaks first second before ∈
              (((app).transition initial horizon scheduler source joint).map
                (privateInputs_state runtime leaks first second)).support := by
            rw [PMF.support_map]
            exact ⟨before, reached, rfl⟩
          rw [privateInputs_transition runtime leaks first second initial horizon scheduler]
            at mapped
          exact mapped)

/-- The transported legal history has exactly the same full focal information,
including its real before-response recall. The initial law is transported
jointly and is not assumed invariant under the input change. -/
theorem privateInputs_trace_info (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) {before : (app).ProtocolState}
    (trace : ((app).protocol initial horizon scheduler).Trace before)
    (focal : Player)
    (agree : ∀ input, graph.fieldVisibleTo focal (.inl input) → first input = second input) :
    ((app).signals (initial.map (PhaseRuntimeState.swap swap)) horizon scheduler).infoOf focal
      (privateInputs_trace runtime leaks first second initial horizon scheduler trace) =
    ((app).signals initial horizon scheduler).infoOf focal trace := by
  rw [ReactiveApplication.info, ReactiveApplication.info]
  cases before with
  | none => rfl
  | some control =>
      change (if control.actor = some focal then
        some (((swap).phaseExecution control.execution).recall focal,
          ((swap).phaseExecution control.execution).observe (app) focal) else none) = _
      rw [privateInputs_recall_history runtime leaks first second initial horizon scheduler
        control trace focal agree, privateInputs_observe runtime leaks first second
          control.execution focal agree]
      rfl

end Vegas.EventGraphRuntime.HiddenSwap
