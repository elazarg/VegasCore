/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseFrontier

/-! # Surviving phase events and exposed readiness

Automatic completion cannot consume a surviving owner's event. A failed phase
with a survivor therefore exposes a genuinely unfinished fresh attempt. Graph
barrier ordering then confines actual native readiness to the installed phase.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.RuntimePhase

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Automatic exclusion service cannot complete a nonexcluded owner's event. -/
theorem drainFuel_completed_survivor (phase : RuntimePhase graph) (fuel : Nat)
    (state : RecoveryState graph) (event : graph.EventId) (owner : Player)
    (acting : graph.actor? event = some owner) (survivor : owner ∉ state.excluded) :
    event ∈ (phase.drainFuel fuel state).native.config.cut.completed ↔
      event ∈ state.native.config.cut.completed := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      unfold drainFuel
      split
      · rename_i pending
        rw [ih (state.completeAutomatic (Classical.choose pending)
          (Classical.choose_spec pending).2) survivor]
        obtain ⟨actor, otherActor, excluded⟩ := (Classical.choose_spec pending).2.owned
        have different : event ≠ Classical.choose pending := by
          intro same
          have ownerEq := Option.some.inj (acting.symm.trans (same ▸ otherActor))
          exact survivor (ownerEq ▸ excluded)
        obtain ⟨action, supported⟩ := state.completeAutomatic_step
          (Classical.choose pending) (Classical.choose_spec pending).2
        rw [Config.step_cut _ _ _ _ _ supported, EventOrder.Cut.mem_complete]
        exact or_iff_right different
      · rfl

/-- A surviving phase owner has an event which remains missing after the saved
lower prefix is rebuilt; there is no vacuous retry which is already finished. -/
theorem drain_unfinished_of_survivor (phase : RuntimePhase graph) (state : RecoveryState graph)
    (saved : state.native.config.cut.IsPrefix phase.low)
    (survivor : (phase.owners \ state.excluded).Nonempty) :
    ¬ phase.Finished (phase.drain state) := by
  obtain ⟨owner, member⟩ := survivor
  obtain ⟨ownerMem, unexcluded⟩ := Finset.mem_sdiff.mp member
  obtain ⟨event, inside, acting⟩ := Finset.mem_biUnion.mp ownerMem
  have actor : graph.actor? event = some owner := by
    exact Option.mem_def.mp (by simpa only [Option.mem_toFinset] using acting)
  intro finished
  have completed := (phase.drainFuel_completed_survivor _ state event owner actor unexcluded).mp
    (finished inside)
  have lower := ((phase.mem_events _).mp inside).1
  have upper := (saved.2 event).mp completed
  omega

/-- Graph barriers keep every ready event inside the unfinished current phase.
The boundary conditions are structural facts about adjacent source phase kinds. -/
theorem ready_mem (phase : RuntimePhase graph) (state : RecoveryState graph)
    (ordered : graph.RevealRelaxedOrdered)
    (within : state.native.config.cut.Within phase.low phase.high)
    (unfinished : ¬ phase.Finished state)
    (bindingBoundary : phase.kind = .commitment → ∀ event : graph.EventId,
      event.val = phase.high → (graph.outputLayout event).IsPublic)
    (revealBoundary : phase.kind = .reveal → ∀ event : graph.EventId,
      event.val = phase.high → ¬ (graph.outputLayout event).IsPublication)
    (event : graph.EventId) (ready : state.native.config.cut.Ready event) :
    event ∈ phase.events := by
  have lower : phase.low ≤ event.val := by
    by_contra below
    exact ready.1 (within.1 event (by omega))
  apply (phase.mem_events event).mpr
  refine ⟨lower, ?_⟩
  cases kind : phase.kind with
  | commitment =>
      have plain : ∀ other : graph.EventId, phase.low ≤ other.val → other.val < phase.high →
          ¬ (graph.outputLayout other).IsPublication := by
        intro other low high
        have typed := phase.fields other low high
        rw [kind] at typed
        obtain ⟨owner, payload, typed⟩ := typed
        rw [typed]
        simp only [EventField.IsPublication, not_false_eq_true]
      rcases ordered.ready_lt_of_within within (bindingBoundary kind) plain ready with
        inside | complete
      · exact inside
      · exact (unfinished (fun other member =>
          complete other ((phase.mem_events _).mp member).2)).elim
  | reveal =>
      have publications : ∀ other : graph.EventId, phase.low ≤ other.val → other.val < phase.high →
          (graph.outputLayout other).IsPublication := by
        intro other low high
        have typed := phase.fields other low high
        rw [kind] at typed
        obtain ⟨payload, typed⟩ := typed
        rw [typed]
        trivial
      rcases ordered.ready_lt_of_within_publications within (revealBoundary kind)
        publications ready with inside | complete
      · exact inside
      · exact (unfinished (fun other member =>
          complete other ((phase.mem_events _).mp member).2)).elim
  | sample =>
      have singleton := phase.sample_singleton kind
      let sample : graph.EventId := ⟨phase.low, lt_of_lt_of_le phase.nonempty phase.bounded⟩
      have sampleInside : sample ∈ phase.events := (phase.mem_events _).mpr
        ⟨le_rfl, phase.nonempty⟩
      have sampleMissing : sample ∉ state.native.config.cut.completed := by
        intro completed
        apply unfinished
        intro other member
        have ranks := (phase.mem_events _).mp member
        have same : other = sample := Fin.ext (by dsimp [sample]; omega)
        exact same ▸ completed
      by_contra outside
      have before : sample.val < event.val := by dsimp [sample]; omega
      have typed := phase.fields sample le_rfl phase.nonempty
      rw [kind] at typed
      obtain ⟨payload, typed⟩ := typed
      apply sampleMissing
      apply ready.2
      apply ordered.keeps (barrierOrder_public_prior graph.outputLayout before ?_)
      · exact Or.inl (by rw [typed]; simp only [EventField.IsPublication, not_false_eq_true])
      · rw [typed]
        trivial

end Vegas.EventGraphRuntime.RuntimePhase

namespace Vegas.EventGraphRuntime.PhaseRuntimeState

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- Maximal adjacent phase kinds give precisely the graph barrier facts used
by native readiness confinement; no scheduling or posterior premise is needed. -/
theorem phase_boundaries (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (adjacent : (phase :: remaining).IsChain fun before after => before.high = after.low)
    (last : ∀ final ∈ (phase :: remaining).getLast?, final.high = graph.order.eventCount)
    (maximal : (phase :: remaining).IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample) :
    (phase.kind = .commitment → ∀ event : graph.EventId,
      event.val = phase.high → (graph.outputLayout event).IsPublic) ∧
    (phase.kind = .reveal → ∀ event : graph.EventId,
      event.val = phase.high → ¬ (graph.outputLayout event).IsPublication) := by
  cases remaining with
  | nil =>
      have ending := last phase (by simp)
      constructor <;> intro _ event same <;> have bounded := event.isLt <;> omega
  | cons next tail =>
      have boundary := adjacent.rel_head? (y := next) (by simp)
      have different := maximal.rel_head? (y := next) (by simp)
      constructor
      · intro kind event same
        have typed := next.fields event (by omega)
          (by have nonempty := next.nonempty; omega)
        cases nextKind : next.kind with
        | commitment =>
            rcases different with different | sample
            · exact (different (kind.trans nextKind.symm)).elim
            · cases kind.symm.trans sample
        | reveal =>
            rw [nextKind] at typed
            obtain ⟨payload, typed⟩ := typed
            rw [typed]
            trivial
        | sample =>
            rw [nextKind] at typed
            obtain ⟨payload, typed⟩ := typed
            rw [typed]
            trivial
      · intro kind event same
        have typed := next.fields event (by omega)
          (by have nonempty := next.nonempty; omega)
        cases nextKind : next.kind with
        | commitment =>
            rw [nextKind] at typed
            obtain ⟨owner, payload, typed⟩ := typed
            rw [typed]
            simp only [EventField.IsPublication, not_false_eq_true]
        | reveal =>
            rcases different with different | sample
            · exact (different (kind.trans nextKind.symm)).elim
            · cases kind.symm.trans sample
        | sample =>
            rw [nextKind] at typed
            obtain ⟨payload, typed⟩ := typed
            rw [typed]
            simp only [EventField.IsPublication, not_false_eq_true]

/-- Every nonterminal normalized state exposes a genuinely unfinished phase,
including immediately after a survivor retry. -/
theorem settle_unfinished (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (valid : Frontier (⟨phases, generation, entry, current, retired⟩ : PhaseRuntimeState graph)) :
    ∀ phase ∈ (settle phases generation entry current retired).phases.head?,
      ¬ phase.Finished (settle phases generation entry current retired).current := by
  induction phases generalizing generation entry current retired with
  | nil => simp only [settle, List.head?_nil, Option.not_mem_none, false_implies, implies_true]
  | cons phase remaining ih =>
      obtain ⟨adjacent, last, saved, within⟩ := valid
      have drainedWithin := phase.drain_within current within
      simp only [settle]
      split
      · rename_i finished
        split
        · rename_i failure
          have restoredWithin : (restore entry (phase.drain current)).native.config.cut.Within
              phase.low phase.high := saved.within phase.nonempty.le
          have rebuiltWithin := phase.drain_within (restore entry (phase.drain current))
            restoredWithin
          split
          · rename_i survivors
            intro target member
            simp only [List.head?_cons, Option.mem_some_iff] at member
            subst target
            exact phase.drain_unfinished_of_survivor _ saved survivors
          · rename_i exhausted
            have allExcluded : phase.owners ⊆ (restore entry (phase.drain current)).excluded := by
              intro owner member
              by_contra missing
              exact exhausted ⟨owner, Finset.mem_sdiff.mpr ⟨member, missing⟩⟩
            have rebuiltFinished := phase.drain_finished_of_excluded
              (restore entry (phase.drain current)) restoredWithin failure.1 allExcluded
            have next := positioned_next phase remaining _ adjacent last
              (phase.finished_prefix _ rebuiltWithin rebuiltFinished)
            exact ih _ _ _ _ ⟨next.adjacent, next.last, next.positioned⟩
        · have next := positioned_next phase remaining _ adjacent last
            (phase.finished_prefix _ drainedWithin finished)
          exact ih _ _ _ _ ⟨next.adjacent, next.last, next.positioned⟩
      · rename_i unfinished
        intro target member
        simp only [List.head?_cons, Option.mem_some_iff] at member
        subst target
        exact unfinished

omit [DecidableEq Player] in
/-- Exact native effects retain the saved phase checkpoint and active interval. -/
theorem Frontier.after_effect {state : PhaseRuntimeState graph} (valid : state.Frontier)
    (current : RecoveryState graph)
    (effect : current.native.config = state.current.native.config ∨
      ∃ phase ∈ state.phases.head?, ∃ event ∈ phase.events,
        ∃ (ready : state.current.native.config.cut.Ready event) (action : graph.Action event),
          current.native.config ∈ (state.current.native.config.step event ready action).support) :
    Frontier { state with current } := by
  rcases effect with same | ⟨phase, member, event, inside, ready, action, supported⟩
  · exact valid.copy_current _ same
  · cases phases : state.phases with
    | nil => simp only [phases, List.head?_nil, Option.not_mem_none] at member
    | cons installed remaining =>
        simp only [phases, List.head?_cons, Option.mem_some_iff] at member
        subst installed
        refine ⟨?_, ?_, ?_⟩
        · simpa only [phases] using valid.adjacent
        · simpa only [phases] using valid.last
        have positioned := valid.positioned
        rw [phases] at positioned
        exact ⟨positioned.1, native_step_within phase _ _ positioned.2 event inside
          ready action supported⟩

/-- On actual barrier-ordered phases, local automatic completion suppresses
ALL excluded-owner readiness before any next observation or seed query. -/
theorem settle_global_quiescent (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (ordered : graph.RevealRelaxedOrdered)
    (valid : Frontier (⟨phases, generation, entry, current, retired⟩ : PhaseRuntimeState graph))
    (maximal : phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample) :
    ∀ event, ¬ (settle phases generation entry current retired).current.AutomaticReady event := by
  have result := settle_frontier phases generation entry current retired valid
  have boundaries := maximal.suffix (settle_suffix phases generation entry current retired)
  intro event eligible
  cases installed : (settle phases generation entry current retired).phases with
  | nil =>
      have terminal := result.terminal installed
      exact eligible.1.1 ((Finset.eq_univ_iff_forall.mp terminal) event)
  | cons phase remaining =>
      have adjacent := result.adjacent
      have last := result.last
      rw [installed] at adjacent last boundaries
      obtain ⟨bindingBoundary, revealBoundary⟩ := phase_boundaries phase remaining adjacent
        last boundaries
      have positioned := result.positioned
      rw [installed] at positioned
      have head : phase ∈ (settle phases generation entry current retired).phases.head? := by
        simp only [installed, List.head?_cons, Option.mem_some_iff]
      have unfinished := settle_unfinished phases generation entry current retired valid
        phase head
      have inside := phase.ready_mem _ ordered positioned.2 unfinished bindingBoundary
        revealBoundary event eligible.1
      exact settle_quiescent phases generation entry current retired phase head event inside
        eligible

end Vegas.EventGraphRuntime.PhaseRuntimeState

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Actual runtime observations suppress excluded-owner readiness under the
compiled phase barriers, through every physical rollback and phase advance. -/
theorem phaseApplication_quiescent (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (ordered : graph.RevealRelaxedOrdered) :
    (phaseApplication runtime leaks).Invariant (fun state =>
      state.Frontier ∧ (state.phases.IsChain fun before after =>
        before.kind ≠ after.kind ∨ before.kind = .sample) ∧
        ∀ event, ¬ state.current.AutomaticReady event) where
  submit state who submission valid :=
    ⟨state.submit_frontier who submission valid.1, valid.2.1,
      state.current.submit_quiescent who submission valid.2.2⟩
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · rename_i allowed
      obtain ⟨native, rawAccepted, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have authorized := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).2
      obtain ⟨phase, member, event, named, inside⟩ :=
        PhaseRuntimeState.allows_event state _ authorized
      obtain ⟨actual, actualNamed, ready, action, supported⟩ :=
        handle_config_mem_step runtime state.current.native native _ rawAccepted
      have same : actual = event := Option.some.inj (actualNamed.symm.trans named)
      subst actual
      have raw := valid.1.after_effect
        (state.current.inclusionResult message.payload.packet.call native)
        (Or.inr ⟨phase, member, event, inside, ready, action, supported⟩)
      exact ⟨PhaseRuntimeState.settle_frontier _ _ _ _ _ raw,
        valid.2.1.suffix (PhaseRuntimeState.settle_suffix _ _ _ _ _),
        PhaseRuntimeState.settle_global_quiescent _ _ _ _ _ ordered raw valid.2.1⟩
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rename_i allowed
      rw [PMF.support_map] at reached
      obtain ⟨native, rawReached, rfl⟩ := reached
      have raw := valid.1.after_effect (state.current.environmentResult command native)
        (state.command_effect runtime command native allowed rawReached)
      exact ⟨PhaseRuntimeState.settle_frontier _ _ _ _ _ raw,
        valid.2.1.suffix (PhaseRuntimeState.settle_suffix _ _ _ _ _),
        PhaseRuntimeState.settle_global_quiescent _ _ _ _ _ ordered raw valid.2.1⟩
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- The actual initial law for a maximal compiled partition is globally
quiescent for excluded owners without suppressing surviving event calendars. -/
theorem phaseApplication_initial_quiescent (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample) (inputs : graph.Inputs) :
    (PhaseRuntimeState.initial plan inputs).Frontier ∧
      ((PhaseRuntimeState.initial plan inputs).phases.IsChain fun before after =>
        before.kind ≠ after.kind ∨ before.kind = .sample) ∧
      ∀ event, ¬ (PhaseRuntimeState.initial plan inputs).current.AutomaticReady event := by
  have raw : PhaseRuntimeState.Frontier
      (⟨plan.phases, 0, ⟨State.initial inputs, ∅⟩, ⟨State.initial inputs, ∅⟩, []⟩ :
        PhaseRuntimeState graph) := by
    refine ⟨plan.adjacent, plan.last, ?_⟩
    cases phases : plan.phases with
    | nil =>
        have noEvents := plan.empty phases
        constructor
        · omega
        · intro event
          exact Fin.elim0 (noEvents ▸ event)
    | cons phase remaining =>
        have low := plan.first phase (by simp only [phases, List.head?_cons,
          Option.mem_some_iff])
        have entry : (State.initial inputs).config.cut.IsPrefix phase.low := by
          constructor
          · omega
          · intro event
            simp only [State.initial, Config.initial, EventOrder.Cut.empty, Finset.notMem_empty,
              low, Nat.not_lt_zero]
        exact ⟨entry, entry.within phase.nonempty.le⟩
  exact ⟨PhaseRuntimeState.initial_frontier plan inputs,
    maximal.suffix (PhaseRuntimeState.settle_suffix _ _ _ _ _),
    PhaseRuntimeState.settle_global_quiescent _ _ _ _ _ ordered raw maximal⟩

end Vegas.EventGraphRuntime
