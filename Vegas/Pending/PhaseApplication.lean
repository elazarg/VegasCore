/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseCompletion
import Vegas.EventGraph.ConfigRestriction

/-! # Automatic phase installation and physical attempt retirement

The application executes native commands inside the current source phase. At a
binding-phase boundary, only fresh public misses trigger rollback. Advancing a
phase saves its exact successor frontier; excluded owners are completed locally
before an observation is exposed. The enclosing network and recall never reset.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- The unexecuted phase suffix and its current semantic checkpoint. Generation
is global across the whole graph, while phase addresses are lower event ranks. -/
structure PhaseRuntimeState (graph : Vegas.EventGraph Player L) where
  phases : List (RuntimePhase graph)
  generation : Nat
  entry : RecoveryState graph
  current : RecoveryState graph
  retired : List (RetiredCommitAttempt graph)

/-- Public phase identity, live event readiness, and permanent retired outcomes.
The descriptor is static program data and exposes no private candidate meaning. -/
structure PhasePublicView (graph : Vegas.EventGraph Player L) where
  native : PublicView graph
  excluded : Finset Player
  phase : Option (RuntimePhaseKind × Nat × Nat)
  attempt : CommitAttemptId
  retired : List (CommitAttemptId × PublicView graph)

namespace PhaseRuntimeState

/-- Terminal states have no active event namespace. -/
def attempt (state : PhaseRuntimeState graph) : CommitAttemptId :=
  ⟨state.phases.head?.map RuntimePhase.low |>.getD graph.order.eventCount, state.generation⟩

/-- Only owned events in the currently installed phase can request local seeds. -/
def SeedRequest (state : PhaseRuntimeState graph) (owner : Player)
    (coordinate : CommitAttemptEvent graph) : Prop :=
  coordinate.attempt = state.attempt ∧
    (∃ phase ∈ state.phases.head?, coordinate.event ∈ phase.events) ∧
    state.current.native.config.cut.Ready coordinate.event ∧
    graph.actor? coordinate.event = some owner ∧ owner ∉ state.current.excluded

/-- Restore semantic data only. The catalogue, exclusion and actual global clock
come from the physical endpoint, and ready-event deadlines start at that clock. -/
def restore (entry current : RecoveryState graph) : RecoveryState graph where
  native :=
    { config := entry.native.config
      accepted := entry.native.accepted
      candidates := current.native.candidates
      clock := current.native.clock
      activatedAt := State.refreshActivated entry.native.config current.native.clock
        (fun _ => none) }
  excluded := current.excluded

omit [DecidableEq Player] in
theorem restore_invariant (entry current : RecoveryState graph) {inputs : graph.Inputs}
    (valid : entry.native.Invariant inputs) :
    (restore entry current).native.Invariant inputs := by
  refine ⟨valid.reachable, State.refreshActivated_isSome _ _ _, ?_⟩
  apply State.refreshActivated_le
  intro event entered impossible
  cases impossible

open Classical in
/-- Automatically drain the installed phase, close its result, and install the
next descriptor. Recursive advancement consumes a descriptor, so fully excluded
phases require neither an extra scheduler command nor a seed query. -/
def settle : List (RuntimePhase graph) → Nat → RecoveryState graph → RecoveryState graph →
    List (RetiredCommitAttempt graph) → PhaseRuntimeState graph
  | [], generation, entry, current, retired => ⟨[], generation, entry, current, retired⟩
  | phase :: remaining, generation, entry, current, retired =>
      let drained := phase.drain current
      if phase.Finished drained then
        if phase.kind = .commitment ∧
            ((drained.excluded \ entry.excluded) ∩ phase.owners).Nonempty then
          let checkpoint := restore entry drained
          let rebuilt := phase.drain checkpoint
          let archive := retired ++ [⟨⟨phase.low, generation⟩, drained.native⟩]
          if (phase.owners \ drained.excluded).Nonempty then
            ⟨phase :: remaining, generation + 1, checkpoint, rebuilt, archive⟩
          else settle remaining generation rebuilt rebuilt archive
        else settle remaining generation drained drained retired
      else ⟨phase :: remaining, generation, entry, drained, retired⟩

/-- Normalize after one native effect. This operation has no network effect. -/
def normalize (state : PhaseRuntimeState graph) : PhaseRuntimeState graph :=
  settle state.phases state.generation state.entry state.current state.retired

/-- Enter the compiled partition from the real native initial state. -/
def initial (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) : PhaseRuntimeState graph :=
  settle plan.phases 0 ⟨State.initial inputs, ∅⟩ ⟨State.initial inputs, ∅⟩ []

/-- Normalization retains the actual global clock, candidate meanings and
permanent exclusion, including across any chain of automatic phase advances. -/
theorem settle_physical (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph)) :
    (settle phases generation entry current retired).current.excluded = current.excluded ∧
      (settle phases generation entry current retired).current.native.candidates =
        current.native.candidates ∧
      (settle phases generation entry current retired).current.native.clock =
        current.native.clock := by
  induction phases generalizing generation entry current retired with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons phase remaining ih =>
      simp only [settle]
      split
      · split
        · split
          · exact ⟨(phase.drain_excluded _).trans (phase.drain_excluded current),
              (phase.drain_tables _).2.1.trans
                (phase.drain_tables current).2.1,
              (phase.drain_tables _).2.2.trans (phase.drain_tables current).2.2⟩
          · obtain ⟨excluded, candidates, clock⟩ := ih generation
              (phase.drain (restore entry (phase.drain current)))
              (phase.drain (restore entry (phase.drain current)))
              (retired ++ [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩])
            exact ⟨excluded.trans ((phase.drain_excluded _).trans (phase.drain_excluded _)),
              candidates.trans ((phase.drain_tables _).2.1.trans
                (phase.drain_tables current).2.1),
              clock.trans ((phase.drain_tables _).2.2.trans (phase.drain_tables current).2.2)⟩
        · obtain ⟨excluded, candidates, clock⟩ := ih generation (phase.drain current)
              (phase.drain current) retired
          exact ⟨excluded.trans (phase.drain_excluded _),
            candidates.trans (phase.drain_tables _).2.1,
            clock.trans (phase.drain_tables _).2.2⟩
      · exact ⟨phase.drain_excluded _, (phase.drain_tables _).2.1,
          (phase.drain_tables _).2.2⟩

/-- Saved and current configurations remain genuine native graph states. -/
structure Invariant (inputs : graph.Inputs) (state : PhaseRuntimeState graph) : Prop where
  saved : state.entry.native.Invariant inputs
  active : state.current.native.Invariant inputs

/-- Semantic rollback and every automatic completion preserve native reachability. -/
theorem settle_invariant (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    {inputs : graph.Inputs} (saved : entry.native.Invariant inputs)
    (active : current.native.Invariant inputs) :
    (settle phases generation entry current retired).Invariant inputs := by
  induction phases generalizing generation entry current retired with
  | nil => exact ⟨saved, active⟩
  | cons phase remaining ih =>
      simp only [settle]
      split
      · split
        · have restored := restore_invariant entry (phase.drain current) saved
          have rebuilt := phase.drain_invariant _ restored
          split
          · exact ⟨restored, rebuilt⟩
          · exact ih _ _ _ _ rebuilt rebuilt
        · have drained := phase.drain_invariant current active
          exact ih _ _ _ _ drained drained
      · exact ⟨saved, phase.drain_invariant current active⟩

/-- The next exposed descriptor has no ready excluded event in its own interval. -/
theorem settle_quiescent (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph)) :
    ∀ phase ∈ (settle phases generation entry current retired).phases.head?,
      ∀ event ∈ phase.events,
        ¬ (settle phases generation entry current retired).current.AutomaticReady event := by
  induction phases generalizing generation entry current retired with
  | nil => simp only [settle, List.head?_nil, Option.not_mem_none, false_implies, implies_true]
  | cons phase remaining ih =>
      simp only [settle]
      split
      · split
        · split
          · intro target member event inside eligible
            simp only [List.head?_cons, Option.mem_some_iff] at member
            subst target
            exact phase.drain_quiescent _ event ⟨inside, eligible⟩
          · exact ih _ _ _ _
        · exact ih _ _ _ _
      · intro target member event inside eligible
        simp only [List.head?_cons, Option.mem_some_iff] at member
        subst target
        exact phase.drain_quiescent _ event ⟨inside, eligible⟩

/-- Every earlier retirement remains in the permanent archive. -/
theorem settle_archive (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph)) :
    retired <+: (settle phases generation entry current retired).retired := by
  induction phases generalizing generation entry current retired with
  | nil => exact List.prefix_refl _
  | cons phase remaining ih =>
      simp only [settle]
      split
      · split
        · split
          · exact List.prefix_append _ _
          · exact (List.prefix_append _ _).trans (ih _ _ _ _)
        · exact ih _ _ _ _
      · exact List.prefix_refl _

/-- The global retry generation never decreases during phase advancement. -/
theorem settle_generation (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph)) :
    generation ≤ (settle phases generation entry current retired).generation := by
  induction phases generalizing generation entry current retired with
  | nil => exact le_rfl
  | cons phase remaining ih =>
      simp only [settle]
      split
      · split
        · split
          · exact Nat.le_succ _
          · exact ih _ _ _ _
        · exact ih _ _ _ _
      · exact le_rfl

theorem settle_suffix (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph)) :
    (settle phases generation entry current retired).phases <:+ phases := by
  induction phases generalizing generation entry current retired with
  | nil => exact List.suffix_refl _
  | cons phase remaining ih =>
      simp only [settle]
      split
      · split
        · split
          · exact List.suffix_refl _
          · exact (ih _ _ _ _).trans (List.suffix_cons _ _)
        · exact (ih _ _ _ _).trans (List.suffix_cons _ _)
      · exact List.suffix_refl _

/-- A clean completed phase saves its actual high frontier and advances
without allocating a retry generation. -/
theorem settle_clean (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph))
    (finished : phase.Finished (phase.drain current))
    (clean : ¬ (phase.kind = .commitment ∧
      (((phase.drain current).excluded \ entry.excluded) ∩ phase.owners).Nonempty)) :
    settle (phase :: remaining) generation entry current retired =
      settle remaining generation (phase.drain current) (phase.drain current) retired := by
  simp only [settle, finished, clean, ↓reduceIte]

/-- A failed binding phase with a survivor retires the actual failed result,
restores the entry, and installs a new namespace before any further command. -/
theorem settle_retry (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph))
    (finished : phase.Finished (phase.drain current)) (kind : phase.kind = .commitment)
    (missed : (((phase.drain current).excluded \ entry.excluded) ∩ phase.owners).Nonempty)
    (survivors : (phase.owners \ (phase.drain current).excluded).Nonempty) :
    settle (phase :: remaining) generation entry current retired =
      ⟨phase :: remaining, generation + 1, restore entry (phase.drain current),
        phase.drain (restore entry (phase.drain current)),
        retired ++ [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩]⟩ := by
  simp only [settle, finished, kind, true_and, missed, survivors, ↓reduceIte]

/-- With no survivor, a failed binding phase is rebuilt automatically and the
next source phase is installed without any fresh active attempt. -/
theorem settle_exhausted (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph))
    (finished : phase.Finished (phase.drain current)) (kind : phase.kind = .commitment)
    (missed : (((phase.drain current).excluded \ entry.excluded) ∩ phase.owners).Nonempty)
    (exhausted : ¬ (phase.owners \ (phase.drain current).excluded).Nonempty) :
    settle (phase :: remaining) generation entry current retired =
      settle remaining generation (phase.drain (restore entry (phase.drain current)))
        (phase.drain (restore entry (phase.drain current)))
        (retired ++ [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩]) := by
  simp only [settle, finished, kind, true_and, missed, exhausted, ↓reduceIte]

omit [DecidableEq Player] in
/-- Retrying cannot authorize any packet from the just-retired namespace. -/
theorem retry_namespace (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph)) :
    (⟨phase.low, generation⟩ : CommitAttemptId) ≠
      (⟨phase :: remaining, generation + 1, entry, current, retired⟩ :
        PhaseRuntimeState graph).attempt := by
  intro same
  have impossible := congrArg CommitAttemptId.generation same
  change generation = generation + 1 at impossible
  omega

/-- A current packet must address the installed rank interval. -/
def allows (state : PhaseRuntimeState graph) (call : Payload graph) : Bool :=
  match state.phases.head?, call.event? graph with
  | some phase, some event => decide (event ∈ phase.events)
  | _, _ => false

/-- The native handler runs before automatic completion, avoiding any writes to
future phases while the current checkpoint is being closed. -/
def handle (runtime : EventGraphRuntime graph) (state : PhaseRuntimeState graph)
    (message : Message Player (CommitAttemptPacket graph)) : Option (PhaseRuntimeState graph) :=
  if message.payload.tokenValid state.attempt && state.allows message.payload.packet.call &&
      !state.current.excludedCall message.payload.packet.call then
    (EventGraphRuntime.handle runtime state.current.native
      ⟨message.id, message.payload.packet.call⟩).map fun native =>
        ({ state with current := state.current.inclusionResult message.payload.packet.call native }
          : PhaseRuntimeState graph).normalize
  else none

/-- Stale packets retain their physical identity but never regain validity. -/
theorem handle_retired (runtime : EventGraphRuntime graph) (state : PhaseRuntimeState graph)
    (message : Message Player (CommitAttemptPacket graph))
    (retired : message.payload.attempt ≠ state.attempt) : state.handle runtime message = none := by
  simp only [handle, message.payload.tokenValid_retired state.attempt retired,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- Environment commands cannot execute or expire a future or retired phase. -/
def commandAllowed (state : PhaseRuntimeState graph) : EnvironmentCommand graph → Bool
  | .advanceClock => true
  | .executeSample event | .expire event =>
      state.phases.head?.any fun phase => decide (event ∈ phase.events)

/-- The original physical environment law is retained, followed by automatic
phase closure. Disallowed commands stutter without changing the transcript carrier. -/
def environment (runtime : EventGraphRuntime graph) (state : PhaseRuntimeState graph)
    (command : EnvironmentCommand graph) : PMF (PhaseRuntimeState graph) :=
  if state.commandAllowed command then
    (environmentStep runtime state.current.native command).map fun native =>
      ({ state with current := state.current.environmentResult command native }
        : PhaseRuntimeState graph).normalize
  else PMF.pure state

/-- Registering a private preparation cannot close a phase or change its namespace. -/
def submit (state : PhaseRuntimeState graph) (who : Player)
    (submission : WitnessedSubmission graph) : PhaseRuntimeState graph :=
  { state with current := state.current.submit who submission }

/-- Emission retains every authentic envelope, including malformed or retired
traffic; only an installed event can receive an authorizing token. -/
def emit (state : PhaseRuntimeState graph) (who : Player)
    (known : List (Message Player (CommitAttemptPacket graph)))
    (submission : WitnessedSubmission graph) : CommitAttemptPacket graph :=
  let packet := state.current.emit who
    (known.map fun message => ⟨message.id, message.payload.packet⟩) submission
  ⟨state.attempt, if state.allows packet.call then packet else { packet with token := none }⟩

def publicView (state : PhaseRuntimeState graph) : PhasePublicView graph where
  native := state.current.native.publicView
  excluded := state.current.excluded
  phase := state.phases.head?.map fun phase => (phase.kind, phase.low, phase.high)
  attempt := state.attempt
  retired := state.retired.map fun prior => (prior.attempt, prior.state.publicView)

def playerView (state : PhaseRuntimeState graph) (who : Player) :=
  (state.current.native.playerView who, state.publicView)

/-- Requests are computed from the actual public application projection. -/
def requests (view : PhasePublicView graph) (owner : Player)
    (coordinate : CommitAttemptEvent graph) : Prop :=
  coordinate.attempt = view.attempt ∧
    (∃ kind low high, view.phase = some (kind, low, high) ∧
      low ≤ coordinate.event.val ∧ coordinate.event.val < high) ∧
    (view.native.activatedAt coordinate.event).isSome = true ∧
    graph.actor? coordinate.event = some owner ∧ owner ∉ view.excluded

omit [DecidableEq Player] in
/-- On genuine states the public request projection is exactly current,
ready, nonexcluded owned-event access, with no seed value examined. -/
theorem requests_publicView {inputs : graph.Inputs} (state : PhaseRuntimeState graph)
    (valid : state.Invariant inputs) (owner : Player) (coordinate : CommitAttemptEvent graph) :
    requests state.publicView owner coordinate ↔ state.SeedRequest owner coordinate := by
  constructor
  · rintro ⟨same, ⟨kind, low, high, phaseEq, lower, upper⟩, activated, acting, unexcluded⟩
    cases head : state.phases.head? with
    | none => simp only [publicView, head, Option.map_none, reduceCtorEq] at phaseEq
    | some phase =>
        have triple : (phase.kind, phase.low, phase.high) = (kind, low, high) := by
          exact Option.some.inj (by
            simpa only [publicView, head, Option.map_some] using phaseEq)
        cases triple
        exact ⟨same, ⟨phase, head, (phase.mem_events _).mpr ⟨lower, upper⟩⟩,
          ((valid.active.activated_iff _).mp activated).1, acting, unexcluded⟩
  · rintro ⟨same, ⟨phase, member, inside⟩, ready, acting, unexcluded⟩
    have head : state.phases.head? = some phase := Option.mem_def.mp member
    obtain ⟨lower, upper⟩ := (phase.mem_events _).mp inside
    exact ⟨same, ⟨phase.kind, phase.low, phase.high, by simp only [publicView, head,
      Option.map_some], lower, upper⟩,
      (valid.active.activated_iff _).mpr ⟨ready, by simp only [acting, Option.isSome_some]⟩,
      acting, unexcluded⟩

omit [DecidableEq Player] in
/-- The current attempt's restored checkpoint is the exact saved semantic state. -/
theorem restore_semantics (entry current : RecoveryState graph) :
    (restore entry current).native.config = entry.native.config ∧
      (restore entry current).native.accepted = entry.native.accepted ∧
      (restore entry current).excluded = current.excluded ∧
      (restore entry current).native.candidates = current.native.candidates ∧
      (restore entry current).native.clock = current.native.clock :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

omit [DecidableEq Player] in
/-- Freshly ready retry events begin at the physical endpoint's clock. -/
theorem restore_ready_clock (entry current : RecoveryState graph) (event : graph.EventId)
    (ready : entry.native.config.cut.Ready event) {owner : Player}
    (acting : graph.actor? event = some owner) :
    (restore entry current).native.activatedAt event = some current.native.clock := by
  simp only [restore, State.refreshActivated, ready, ↓reduceDIte, acting]
  rfl

omit [DecidableEq Player] in
/-- The discarded semantic state restricts to the exact saved checkpoint. -/
theorem restore_restrict_store (entry current : RecoveryState graph)
    (agreement : entry.native.config.CompletedOutputAgreement current.native.config)
    (inputs : entry.native.config.inputs = current.native.config.inputs) :
    (restore entry current).native.config.store =
      (current.native.config.restrict entry.native.config.cut).store :=
  (agreement.restrict_store _ _ inputs).symm

/-- Previously excluded automatic failures cannot be interpreted as a fresh miss. -/
theorem automatic_no_new_miss (phase : RuntimePhase graph) (entry : RecoveryState graph) :
    ¬ (((phase.drain entry).excluded \ entry.excluded) ∩ phase.owners).Nonempty := by
  simp only [phase.drain_excluded, Finset.sdiff_self, Finset.empty_inter,
    Finset.not_nonempty_empty, not_false_eq_true]

end PhaseRuntimeState

/-- The physical network, receipts and player/environment recall are the
ordinary reactive execution carrier, with automatic phase normalization internal. -/
def phaseApplication (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    ReactiveApplication Player where
  State := PhaseRuntimeState graph
  Payload := CommitAttemptPacket graph
  Submission := WitnessedSubmission graph
  EnvironmentCommand := EnvironmentCommand graph
  LocalObservation := PlayerView graph × PhasePublicView graph
  PublicObservation := PhasePublicView graph
  packet := PhaseRuntimeState.emit
  submit := PhaseRuntimeState.submit
  handle := PhaseRuntimeState.handle runtime
  environment := PhaseRuntimeState.environment runtime
  observePlayer := PhaseRuntimeState.playerView
  observePublic := PhaseRuntimeState.publicView
  observePending := leaks

/-- Genuine native metadata survives submissions, arbitrary accepted packets,
clock/sample/expiry commands, rollback, and automatic phase installation. -/
theorem phaseApplication_invariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (inputs : graph.Inputs) :
    (phaseApplication runtime leaks).Invariant (PhaseRuntimeState.Invariant inputs) where
  submit state who submission valid := by
    refine ⟨valid.saved, ?_⟩
    apply valid.active.copy
    · change (submitStep _ who _).config = _
      rw [submitStep_config, (submission.call.register_facts who state.current.native).1]
    · have same := (submitStep_publicView
        (submission.call.register state.current.native who) who submission.call.packet).trans
          (submission.call.register_facts who state.current.native).2
      exact congrArg PublicView.clock same
    · have same := (submitStep_publicView
        (submission.call.register state.current.native who) who submission.call.packet).trans
          (submission.call.register_facts who state.current.native).2
      exact congrArg PublicView.activatedAt same
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact PhaseRuntimeState.settle_invariant _ _ _ _ _ valid.saved
        (handle_invariant runtime state.current.native native _ valid.active handled)
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, reached, rfl⟩ := reached
      exact PhaseRuntimeState.settle_invariant _ _ _ _ _ valid.saved
        (environmentStep_invariant runtime state.current.native native command valid.active reached)
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- Permanent exclusion is monotone through the actual application interface,
even when semantic outputs and accepted bindings are restored to a checkpoint. -/
theorem phaseApplication_exclusion_monotone (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).StepRelation
      (fun before after => before.current.excluded ⊆ after.current.excluded) where
  refl _ := fun _ member => member
  submit _ _ _ := fun _ member => member
  handle state message next accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      change state.current.excluded ⊆
        (PhaseRuntimeState.settle _ _ _ _ _).current.excluded
      rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).1]
      exact state.current.inclusionResult_excluded_subset _ native
    · cases accepted
  environment state command next reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, reached, rfl⟩ := reached
      change state.current.excluded ⊆
        (PhaseRuntimeState.settle _ _ _ _ _).current.excluded
      rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).1]
      exact state.current.environmentResult_excluded_subset command native
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact fun _ member => member

namespace PhaseRuntimeState

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- Automatic closure changes no physical network, receipt, or recall field. -/
def normalizeExecution (execution : (phaseApplication runtime leaks).Execution) :
    (phaseApplication runtime leaks).Execution :=
  { execution with application := execution.application.normalize }

theorem normalizeExecution_transcript
    (execution : (phaseApplication runtime leaks).Execution) :
    (normalizeExecution runtime leaks execution).network = execution.network ∧
      (normalizeExecution runtime leaks execution).receipts = execution.receipts ∧
      (normalizeExecution runtime leaks execution).recall = execution.recall ∧
      (normalizeExecution runtime leaks execution).environmentRecall =
        execution.environmentRecall :=
  ⟨rfl, rfl, rfl, rfl⟩

end PhaseRuntimeState
end Vegas.EventGraphRuntime
