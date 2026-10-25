/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseSingletonRebuild

/-! # Actual failed singleton phase closure

A completed singleton is not drained twice. When its owner newly exits, the
saved semantic frontier rebuilds exactly the actual failure, while the phase
engine retains that failure in its archive and advances without a retry.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace RuntimePhase

theorem drain_eq_of_singleton_completed (phase : RuntimePhase graph)
    (state : RecoveryState graph) (event : graph.EventId) (only : phase.events = {event})
    (completed : event ∈ state.native.config.cut.completed) : phase.drain state = state := by
  apply phase.drain_eq_of_clear
  intro other ⟨inside, ready⟩
  have same := Finset.mem_singleton.mp ((Finset.ext_iff.mp only _).mp inside)
  subst other
  exact ready.1.1 completed

end RuntimePhase

namespace PhaseRuntimeState

/-- Singleton failed closure has exactly the native failure result and records
its actual endpoint without allocating a surviving-owner generation. -/
theorem settle_singleton_failure (phase : RuntimePhase graph)
    (remaining : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    {inputs : graph.Inputs} (valid : current.native.Invariant inputs)
    (event : graph.EventId) (only : phase.events = {event})
    (eligible : current.AutomaticReady event) {owner : Player}
    (owned : graph.actor? event = some owner) (kind : phase.kind = .commitment)
    (fresh : owner ∉ entry.excluded)
    (savedConfig : entry.native.config = current.native.config)
    (savedAccepted : entry.native.accepted = current.native.accepted)
    (unique : ∀ other, current.native.config.cut.Ready other → other = event) :
    let failed := current.completeAutomatic event eligible
    settle (phase :: remaining) generation entry failed retired =
      settle remaining generation failed failed
        (retired ++ [⟨⟨phase.low, generation⟩, failed.native⟩]) := by
  intro failed
  obtain ⟨action, supported⟩ := current.completeAutomatic_step event eligible
  have completed : event ∈ failed.native.config.cut.completed := by
    rw [current.native.config.step_cut event eligible.1 action _ supported]
    simp
  have drained := phase.drain_eq_of_singleton_completed failed event only completed
  have owners : phase.owners = {owner} := by
    rw [RuntimePhase.owners, only, Finset.singleton_biUnion, owned]
    rfl
  have excluded : owner ∈ failed.excluded := by
    change owner ∈ current.excluded
    simpa only [owned] using eligible.2
  have finished : phase.Finished (phase.drain failed) := by
    rw [drained]
    intro other inside
    have same := Finset.mem_singleton.mp ((Finset.ext_iff.mp only _).mp inside)
    subst other
    exact completed
  have missed : (((phase.drain failed).excluded \ entry.excluded) ∩ phase.owners).Nonempty := by
    rw [drained, owners]
    exact ⟨owner, Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨excluded, fresh⟩,
      Finset.mem_singleton_self _⟩⟩
  have exhausted : ¬ (phase.owners \ (phase.drain failed).excluded).Nonempty := by
    rw [drained, owners]
    rintro ⟨other, survivor⟩
    obtain ⟨same, notExcluded⟩ := Finset.mem_sdiff.mp survivor
    exact notExcluded (Finset.mem_singleton.mp same ▸ excluded)
  have rebuilt := phase.restore_completeAutomatic entry current valid event only eligible
    savedConfig savedAccepted unique
  change phase.drain (restore entry failed) = failed at rebuilt
  simpa only [drained, rebuilt] using
    settle_exhausted phase remaining generation entry failed retired finished kind missed exhausted

/-- The real due-expiry kernel closes a missed singleton binding with its actual
physical result and an archived endpoint, under primitive frontier/metadata facts. -/
theorem environment_expire_singleton (runtime : EventGraphRuntime graph)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph)) (generation : Nat)
    (entry before : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    {inputs : graph.Inputs} (valid : before.native.Invariant inputs)
    (event : graph.EventId) (only : phase.events = {event})
    (ready : before.native.config.cut.Ready event) (entered : Nat)
    (activated : before.native.activatedAt event = some entered)
    (due : runtime.deadline event ≤ before.native.clock - entered)
    (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (view : nodeView graph event = .bind owner payload outputEq codeEq)
    (kind : phase.kind = .commitment) (fresh : owner ∉ entry.excluded)
    (savedConfig : entry.native.config = before.native.config)
    (savedAccepted : entry.native.accepted = before.native.accepted)
    (unique : ∀ other, before.native.config.cut.Ready other → other = event) :
    let failedNative := before.native.completeFailure event ready
    let failed := before.environmentResult (.expire event) failedNative
    environment runtime ⟨phase :: remaining, generation, entry, before, retired⟩ (.expire event) =
      PMF.pure (settle remaining generation failed failed
        (retired ++ [⟨⟨phase.low, generation⟩, failedNative⟩])) := by
  intro failedNative failed
  have owned : graph.actor? event = some owner :=
    graph.actor?_of_outputLayout_binding outputEq
  obtain ⟨action, supported⟩ := before.native.completeFailure_step event ready owned
  have completed : event ∈ failedNative.config.cut.completed := by
    rw [before.native.config.step_cut event ready action _ supported]
    simp
  have nativeLaw : environmentStep runtime before.native (.expire event) =
      PMF.pure failedNative := by
    dsimp only [failedNative]
    simpa only [State.completeFailure, view] using
      environmentStep_expire_bind_eq runtime before.native event ready entered activated due
        owner payload outputEq codeEq view
  let excludedBefore : RecoveryState graph := ⟨before.native, insert owner before.excluded⟩
  have eligible : excludedBefore.AutomaticReady event := by
    refine ⟨ready, ?_⟩
    change (match graph.actor? event with
      | none => False
      | some who => who ∈ insert owner before.excluded)
    rw [owned]
    exact Finset.mem_insert_self _ _
  have excluded : failed.excluded = insert owner before.excluded := by
    change (if event ∉ before.native.config.cut.completed ∧
        event ∈ failedNative.config.cut.completed then
      RecoveryState.excludeEvent before.excluded event else before.excluded) = _
    rw [ite_eq_left ⟨ready.1, completed⟩]
    simp only [RecoveryState.excludeEvent, owned]
  have same : failed = excludedBefore.completeAutomatic event eligible :=
    congrArg (fun excluded => (⟨failedNative, excluded⟩ : RecoveryState graph)) excluded
  have closed := settle_singleton_failure phase remaining generation entry excludedBefore retired
    valid event only eligible owned kind fresh savedConfig savedAccepted unique
  rw [← same] at closed
  have allowed : (⟨phase :: remaining, generation, entry, before, retired⟩ :
      PhaseRuntimeState graph).commandAllowed (.expire event) = true := by
    change decide (event ∈ phase.events) = true
    exact decide_eq_true ((Finset.ext_iff.mp only _).mpr (Finset.mem_singleton_self event))
  simp only [environment, allowed, ↓reduceIte, nativeLaw, PMF.pure_map]
  change PMF.pure (settle (phase :: remaining) generation entry failed retired) = _
  rw [closed]
  rfl

end PhaseRuntimeState

end Vegas.EventGraphRuntime
