/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseDrain
import Vegas.Pending.PhaseSingletonTransition

/-! # The actual failed singleton expiry has the recovery drain endpoint -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRuntimeState

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- After the native failure effect, actual singleton phase closure retains
exactly the global recovery drain. The native expiry kernel determines when
this effect occurs; no deadline or final-state equality is assumed here. -/
theorem settle_expire_binding_current_eq_drain_sequential
    (phase : RuntimePhase graph.sequentialize)
    (remaining : List (RuntimePhase graph.sequentialize)) (generation : Nat)
    (entry before : RecoveryState graph.sequentialize)
    (retired : List (RetiredCommitAttempt graph.sequentialize))
    {inputs : graph.sequentialize.Inputs} (valid : before.native.Invariant inputs)
    (frontier : Frontier (⟨phase :: remaining, generation, entry, before, retired⟩ :
      PhaseRuntimeState graph.sequentialize))
    (event : graph.EventId) (only : phase.events = {event})
    (ready : before.native.config.cut.Ready event) {owner : Player}
    (owned : graph.sequentialize.actor? event = some owner) (kind : phase.kind = .commitment)
    (fresh : owner ∉ entry.excluded)
    (savedConfig : entry.native.config = before.native.config)
    (savedAccepted : entry.native.accepted = before.native.accepted) :
    let failed := before.environmentResult (.expire event)
      (before.native.completeFailure event ready)
    (settle (phase :: remaining) generation entry failed retired).current = failed.drain := by
  intro failed
  let failedNative := before.native.completeFailure event ready
  obtain ⟨action, supported⟩ := before.native.completeFailure_step event ready owned
  have completed : event ∈ failedNative.config.cut.completed := by
    rw [before.native.config.step_cut event ready action _ supported]
    simp
  let excludedBefore : RecoveryState graph.sequentialize :=
    ⟨before.native, insert owner before.excluded⟩
  have eligible : excludedBefore.AutomaticReady event := by
    refine ⟨ready, ?_⟩
    change (match graph.sequentialize.actor? event with
      | none => False
      | some who => who ∈ insert owner before.excluded)
    rw [owned]
    exact Finset.mem_insert_self _ _
  have excluded : failed.excluded = insert owner before.excluded := by
    change (if event ∉ before.native.config.cut.completed ∧
        event ∈ failedNative.config.cut.completed then
      RecoveryState.excludeEvent before.excluded event else before.excluded) = _
    rw [ite_eq_left ⟨ready.1, completed⟩]
    simp only [RecoveryState.excludeEvent]
    change graph.actor? event = some owner at owned
    rw [owned]
  have same : failed = excludedBefore.completeAutomatic event eligible :=
    congrArg (fun excluded => (⟨failedNative, excluded⟩ : RecoveryState graph.sequentialize))
      excluded
  have closed := settle_singleton_failure phase remaining generation entry excludedBefore retired
    valid event only eligible owned kind fresh savedConfig savedAccepted
      (fun _ otherReady => before.native.config.cut.ready_unique otherReady ready)
  rw [← same] at closed
  have inside : event ∈ phase.events := by rw [only]; exact Finset.mem_singleton_self _
  have within : failed.native.config.cut.Within phase.low phase.high :=
    native_step_within phase before.native failed.native frontier.positioned.2 event inside
      ready action supported
  have finished : phase.Finished failed := by
    intro other member
    have equal : other = event := Finset.mem_singleton.mp (only ▸ member)
    subst other
    exact completed
  have next := positioned_next phase remaining failed frontier.adjacent frontier.last
    (phase.finished_prefix failed within finished)
  rw [closed]
  exact settle_current_eq_drain_sequential remaining generation failed failed _ rfl
    ⟨next.adjacent, next.last, next.positioned⟩

end Vegas.EventGraphRuntime.PhaseRuntimeState
