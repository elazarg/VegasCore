/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastProperOpening
import Vegas.Examples.CommitSeedBroadcastTail
import Vegas.Pending.PhasePlanSuffix
import Vegas.Pending.PhaseSemanticProgress
import Vegas.Pending.PhaseFailureCoverage
import Vegas.EventGraph.ResolutionProvenance

/-! # Standing failed bindings after the original commitment closes -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem owned_event_cases (event : graph.EventId) (owner : Player)
    (acting : graph.actor? event = some owner) :
    event = bindingEvent owner ∨ event = revealEvent owner := by
  have classified : ∀ (event : graph.EventId) (owner : Player),
      graph.actor? event = some owner →
        event = bindingEvent owner ∨ event = revealEvent owner := by decide
  exact classified event owner acting

/-- Completed bindings put the actual normalized state in the publication suffix. -/
theorem completed_bindings_publication_tail (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current))
    (done : ∀ owner, bindingEvent owner ∈
      current.execution.application.current.native.config.cut.completed) :
    current.execution.application.phases <:+ [publicationPhase] := by
  classical
  rcases raw_phases_cases selected current trace with all | publication | empty
  · have live := (raw_phase_geometry selected current trace).2.1
    have unfinished := live commitmentPhase (by rw [all]; rfl)
    apply (unfinished ?_).elim
    intro event inside
    have interval := (RuntimePhase.mem_events commitmentPhase event).mp inside
    change 0 ≤ event.val ∧ event.val < 3 at interval
    let owner : Player := ⟨event.val, interval.2⟩
    have same : bindingEvent owner = event := Fin.ext rfl
    exact same ▸ done owner
  · rw [publication]
  · rw [empty]
    exact List.nil_suffix

private theorem settle_noncommit_keepsStore (phases : List (RuntimePhase graph))
    (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph))
    (noncommit : ∀ phase ∈ phases, phase.kind ≠ .commitment) :
    KeepsStore current.native
      (PhaseRuntimeState.settle phases generation entry current retired).current.native := by
  induction phases generalizing generation entry current retired with
  | nil => exact fun _ _ stored => stored
  | cons phase remaining ih =>
      have next := ih generation (phase.drain current) (phase.drain current) retired
        (fun next member => noncommit next (List.mem_cons_of_mem phase member))
      simp only [PhaseRuntimeState.settle]
      split
      · split
        · rename_i failure
          exact (noncommit phase (by simp) failure.1).elim
        · exact fun field value stored => next field value
            (phase.drain_keepsStore current field value stored)
      · exact phase.drain_keepsStore current

theorem settle_publication_keepsStore (phases : List (RuntimePhase graph))
    (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph)) (suffix : phases <:+ [publicationPhase]) :
    KeepsStore current.native
      (PhaseRuntimeState.settle phases generation entry current retired).current.native := by
  apply settle_noncommit_keepsStore
  intro phase member
  have present := suffix.sublist.subset member
  have same : phase = publicationPhase := List.mem_singleton.mp present
  subst phase
  decide

/-- Every subsequent raw packet and scheduler effect preserves the actual
standing binding cell. There is no commitment descriptor left to roll it back. -/
theorem publication_tail_store_invariant (frozen : EventGraphRuntime.State graph) :
    app.Invariant (fun state => state.phases <:+ [publicationPhase] ∧
      KeepsStore frozen state.current.native) where
  submit state who material valid := by
    refine ⟨valid.1, ?_⟩
    intro field value stored
    change (submitStep (material.call.register state.current.native who) who
      material.call.packet).config.store field = some value
    rw [submitStep_config, (material.call.register_facts who state.current.native).1]
    exact valid.2 field value stored
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      refine ⟨(PhaseRuntimeState.settle_suffix _ _ _ _ _).trans valid.1, ?_⟩
      have normalization := settle_publication_keepsStore state.phases state.generation state.entry
        (state.current.inclusionResult message.payload.packet.call native) state.retired valid.1
      intro field value stored
      exact normalization field value
        (handle_store_of_some runtime _ native _ handled field value (valid.2 field value stored))
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, supported, rfl⟩ := PMF.support_map .. ▸ reached
      refine ⟨(PhaseRuntimeState.settle_suffix _ _ _ _ _).trans valid.1, ?_⟩
      have normalization := settle_publication_keepsStore state.phases state.generation state.entry
        (state.current.environmentResult command native) state.retired valid.1
      intro field value stored
      exact normalization field value
        (environmentStep_store_of_some runtime _ native command supported field value
          (valid.2 field value stored))
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid

/-- The binding's original failure survives the entire actual physical tail,
including arbitrary future raw submissions and the reveal phase's own expiry. -/
theorem publication_tail_run_keepsStore (selected : app.Scheduler)
    (players : Player → app.Policy) (count : Nat) (before after : app.Execution)
    (tail : before.application.phases <:+ [publicationPhase])
    (supported : after ∈ (app.runRounds selected players count before).support) :
    KeepsStore before.application.current.native after.application.current.native := by
  have invariant := (publication_tail_store_invariant
    before.application.current.native).policyInvariant app players
  exact (invariant.runRounds selected count before after
    ⟨tail, fun _ _ stored => stored⟩ supported).2

end Vegas.Examples.CommitSeedBroadcast
