/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionCompletion
import Vegas.Pending.ReactiveRuntime

/-! # Native execution with permanent exclusion

An accepted unusable binding does not exclude its owner. Exclusion follows an
owned expiry or an accepted opening whose public result is failure. Every
transition drains newly ready events of excluded owners before exposing a view.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace RecoveryState

/-- Membership in permanent exclusion is independent of hidden binding stores. -/
def excludedEvent (state : RecoveryState graph) (event : graph.EventId) : Bool :=
  (graph.actor? event).any fun owner => decide (owner ∈ state.excluded)

def excludedCall (state : RecoveryState graph) (call : Payload graph) : Bool :=
  match call.event? graph with
  | none => false
  | some event => state.excludedEvent event

/-- Inspect only the public result of a resolution, never a hidden binding result. -/
def publicationFailed (native : State graph) (event : graph.EventId) : Bool :=
  match nodeView graph event with
  | .resolve _owner _payload _binding _checks outputEq _ =>
      match native.config.outputs event with
      | none => false
      | some result =>
          match cast (congrArg EventField.Value outputEq) result with
          | .failure => true
          | .success _ => false
  | .bind .. | .sample .. => false

def excludeEvent (excluded : Finset Player) (event : graph.EventId) : Finset Player :=
  match graph.actor? event with
  | none => excluded
  | some owner => insert owner excluded

/-- Accepted bindings, even unusable ones, do not trigger exclusion. -/
def inclusionResult (state : RecoveryState graph) (call : Payload graph)
    (native : State graph) : RecoveryState graph :=
  ⟨native, match call with
    | .opening event _ _ =>
        if publicationFailed native event then excludeEvent state.excluded event else state.excluded
    | .commitment .. | .malformed .. => state.excluded⟩

/-- A newly completed expiry is a genuine event failure. Stuttering expiry and
all other commands leave the permanent exclusion set unchanged. -/
def environmentResult (state : RecoveryState graph) (command : EnvironmentCommand graph)
    (native : State graph) : RecoveryState graph :=
  ⟨native, match command with
    | .expire event =>
        if event ∉ state.native.config.cut.completed ∧ event ∈ native.config.cut.completed then
          excludeEvent state.excluded event else state.excluded
    | .advanceClock | .executeSample _ => state.excluded⟩

def publicView (state : RecoveryState graph) : PublicView graph × Finset Player :=
  (state.native.publicView, state.excluded)

def playerView (state : RecoveryState graph) (who : Player) : PlayerView graph × Finset Player :=
  (state.native.playerView who, state.excluded)

def emit (state : RecoveryState graph) (who : Player)
    (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) : WitnessedPacket graph :=
  let packet := submission.emit state.native who known
  if state.excludedCall packet.call then { packet with token := none } else packet

def submit (state : RecoveryState graph) (who : Player)
    (submission : WitnessedSubmission graph) : RecoveryState graph :=
  let native := submitStep (submission.call.register state.native who) who submission.call.packet
  { state with native }

def handle (runtime : EventGraphRuntime graph) (state : RecoveryState graph)
    (message : Message Player (WitnessedPacket graph)) : Option (RecoveryState graph) :=
  if state.excludedCall message.payload.call then none
  else if message.payload.tokenValid then
    (EventGraphRuntime.handle runtime state.native ⟨message.id, message.payload.call⟩).map
      fun native => (state.inclusionResult message.payload.call native).drain
  else none

def environment (runtime : EventGraphRuntime graph) (state : RecoveryState graph)
    (command : EnvironmentCommand graph) : PMF (RecoveryState graph) :=
  (environmentStep runtime state.native command).map fun native =>
    (state.environmentResult command native).drain

theorem excludedEvent_of_empty (state : RecoveryState graph) (empty : state.excluded = ∅)
    (event : graph.EventId) : state.excludedEvent event = false := by
  unfold excludedEvent
  cases graph.actor? event <;> simp [empty]

theorem excludedCall_of_empty (state : RecoveryState graph) (empty : state.excluded = ∅)
    (call : Payload graph) : state.excludedCall call = false := by
  unfold excludedCall
  cases call.event? graph with
  | none => rfl
  | some event => exact state.excludedEvent_of_empty empty event

theorem emit_of_empty (state : RecoveryState graph) (empty : state.excluded = ∅)
    (who : Player) (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) :
    state.emit who known submission = submission.emit state.native who known := by
  simp only [emit, state.excludedCall_of_empty empty, Bool.false_eq_true, ↓reduceIte]

/-- Before a failure, inclusion has precisely the default native outcome. -/
theorem inclusionResult_drain_of_empty (state : RecoveryState graph) (call : Payload graph)
    (native : State graph) (empty : (state.inclusionResult call native).excluded = ∅) :
    (state.inclusionResult call native).drain = ⟨native, ∅⟩ := by
  rw [drain_eq_of_empty _ empty]
  exact congrArg (fun excluded => (⟨native, excluded⟩ : RecoveryState graph)) empty

/-- A non-failing environment outcome is unchanged by automatic service. -/
theorem environmentResult_drain_of_empty (state : RecoveryState graph)
    (command : EnvironmentCommand graph) (native : State graph)
    (empty : (state.environmentResult command native).excluded = ∅) :
    (state.environmentResult command native).drain = ⟨native, ∅⟩ := by
  rw [drain_eq_of_empty _ empty]
  exact congrArg (fun excluded => (⟨native, excluded⟩ : RecoveryState graph)) empty

theorem submit_quiescent (state : RecoveryState graph) (who : Player)
    (submission : WitnessedSubmission graph) (clear : ∀ event, ¬ state.AutomaticReady event) :
    ∀ event, ¬ (state.submit who submission).AutomaticReady event := by
  intro event eligible
  apply clear event
  have configEq : (state.submit who submission).native.config = state.native.config := by
    change (submitStep _ who _).config = _
    rw [submitStep_config, (submission.call.register_facts who state.native).1]
  unfold AutomaticReady at eligible ⊢
  rw [configEq] at eligible
  exact eligible

theorem excludeEvent_subset (excluded : Finset Player) (event : graph.EventId) :
    excluded ⊆ excludeEvent excluded event := by
  unfold excludeEvent
  cases graph.actor? event with
  | none => exact fun _ member => member
  | some owner => exact Finset.subset_insert _ _

theorem inclusionResult_excluded_subset (state : RecoveryState graph) (call : Payload graph)
    (native : State graph) : state.excluded ⊆ (state.inclusionResult call native).excluded := by
  cases call with
  | commitment _ _ | malformed _ => exact fun _ member => member
  | opening event _ _ =>
      change state.excluded ⊆ (if publicationFailed native event then
        excludeEvent state.excluded event else state.excluded)
      split
      · exact excludeEvent_subset (graph := graph) _ _
      · exact fun _ member => member

theorem environmentResult_excluded_subset (state : RecoveryState graph)
    (command : EnvironmentCommand graph) (native : State graph) :
    state.excluded ⊆ (state.environmentResult command native).excluded := by
  cases command with
  | advanceClock | executeSample _ => exact fun _ member => member
  | expire event =>
      change state.excluded ⊆ (if event ∉ state.native.config.cut.completed ∧
        event ∈ native.config.cut.completed then excludeEvent state.excluded event
          else state.excluded)
      split
      · exact excludeEvent_subset (graph := graph) _ _
      · exact fun _ member => member

theorem handle_excluded_subset (runtime : EventGraphRuntime graph)
    (state next : RecoveryState graph) (message : Message Player (WitnessedPacket graph))
    (accepted : state.handle runtime message = some next) : state.excluded ⊆ next.excluded := by
  unfold handle at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · obtain ⟨native, _, rfl⟩ := Option.map_eq_some_iff.mp accepted
      rw [drain_excluded]
      exact inclusionResult_excluded_subset _ _ _
    · cases accepted

theorem environment_excluded_subset (runtime : EventGraphRuntime graph)
    (state next : RecoveryState graph) (command : EnvironmentCommand graph)
    (realized : next ∈ (state.environment runtime command).support) :
    state.excluded ⊆ next.excluded := by
  rw [environment, PMF.support_map] at realized
  obtain ⟨native, _, rfl⟩ := realized
  rw [drain_excluded]
  exact environmentResult_excluded_subset _ _ _

end RecoveryState

/-- The standard packet/network machinery with an explicit permanent-exclusion contract. -/
def recoveryApplication (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    ReactiveApplication Player where
  State := RecoveryState graph
  Payload := WitnessedPacket graph
  Submission := WitnessedSubmission graph
  EnvironmentCommand := EnvironmentCommand graph
  LocalObservation := PlayerView graph × Finset Player
  PublicObservation := PublicView graph × Finset Player
  packet := RecoveryState.emit
  submit := RecoveryState.submit
  handle := RecoveryState.handle runtime
  environment := RecoveryState.environment runtime
  observePlayer := RecoveryState.playerView
  observePublic := RecoveryState.publicView
  observePending := leaks

end Vegas.EventGraphRuntime
