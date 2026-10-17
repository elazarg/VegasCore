/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingPayoffs
import Vegas.Pending.PhasePlanSuffix
import Vegas.Pending.PhaseSemanticProgress
import Vegas.Pending.PhaseFailureCoverage
import Vegas.EventGraph.ResolutionProvenance

/-! # Standing failed bindings after the original commitment closes -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- Both completed binding cells force the real normalizer past the commitment
phase; it cannot expose a completed commitment phase as a live callback. -/
theorem completed_bindings_publication_tail (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current))
    (aliceDone : aliceBinding ∈ current.execution.application.current.native.config.cut.completed)
    (bobDone : bobBinding ∈ current.execution.application.current.native.config.cut.completed) :
    current.execution.application.phases <:+ [publicationPhase] := by
  classical
  have suffix := phasePlanSuffix_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon selected trace
  rw [plan_phases] at suffix
  obtain ⟨prior, joined⟩ := suffix
  cases prior with
  | nil =>
      simp only [List.nil_append] at joined
      have live := (raw_phase_geometry selected current trace).2.1
      have unfinished := live commitmentPhase (by rw [joined]; rfl)
      apply (unfinished ?_).elim
      intro event inside
      have interval := (RuntimePhase.mem_events commitmentPhase event).mp inside
      change 0 ≤ event.val ∧ event.val < 2 at interval
      fin_cases event
      · exact aliceDone
      · exact bobDone
      · change 0 ≤ 2 ∧ 2 < 2 at interval
        omega
      · change 0 ≤ 3 ∧ 3 < 2 at interval
        omega
  | cons first remaining =>
      cases remaining with
      | nil =>
          have tail := congrArg List.tail joined
          have phases : current.execution.application.phases = [publicationPhase] := by
            simpa only [List.cons_append, List.nil_append, List.tail_cons] using tail
          exact ⟨[], by simpa only [List.nil_append] using phases⟩
      | cons second remaining =>
          have lengths := congrArg List.length joined
          simp only [List.length_append, List.length_cons, List.length_nil] at lengths
          have empty : current.execution.application.phases = [] :=
            List.eq_nil_of_length_eq_zero (by omega)
          rw [empty]
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

/-- A failed Alice declaration cannot later become a successful publication.
This is a reachability consequence, independent of the later player policies. -/
theorem alice_failed_binding_publication (native : EventGraphRuntime.State graph)
    (valid : native.Invariant (encodeInputs (Env.empty (CellVal simpleExpr))))
    (complete : native.config.cut.Terminal)
    (failed : native.config.outputs aliceBinding = some .failure) :
    RecoveryState.publicationFailed native aliceReveal = true := by
  classical
  have present : aliceReveal ∈ native.config.cut.completed := by
    rw [complete]
    exact Finset.mem_univ _
  obtain ⟨result, output⟩ := Option.isSome_iff_exists.mp
    ((native.config.output_available aliceReveal).mpr present)
  have failedOutput : native.config.outputs aliceReveal = some .failure := by
    cases result with
    | failure => exact output
    | success value =>
        have binding := valid.reachable.publication_binding aliceReveal alice .bool
          ⟨.inr aliceBinding, binding_layouts.1⟩ _ rfl rfl value output
        change native.config.outputs aliceBinding = some (.success value) at binding
        rw [failed] at binding
        cases binding
  cases node : nodeView graph aliceReveal with
  | bind owner payload kind code => cases kind.symm.trans reveal_layouts.1
  | sample payload law kind code => cases kind.symm.trans reveal_layouts.1
  | resolve owner payload binding checks kind code =>
      have same := EventField.publication.inj (kind.symm.trans reveal_layouts.1)
      subst payload
      rw [RecoveryState.publicationFailed, node, failedOutput]
      rfl

/-- The corresponding native obstruction for Bob's standing failed declaration. -/
theorem bob_failed_binding_publication (native : EventGraphRuntime.State graph)
    (valid : native.Invariant (encodeInputs (Env.empty (CellVal simpleExpr))))
    (complete : native.config.cut.Terminal)
    (failed : native.config.outputs bobBinding = some .failure) :
    RecoveryState.publicationFailed native bobReveal = true := by
  classical
  have present : bobReveal ∈ native.config.cut.completed := by
    rw [complete]
    exact Finset.mem_univ _
  obtain ⟨result, output⟩ := Option.isSome_iff_exists.mp
    ((native.config.output_available bobReveal).mpr present)
  have failedOutput : native.config.outputs bobReveal = some .failure := by
    cases result with
    | failure => exact output
    | success value =>
        have binding := valid.reachable.publication_binding bobReveal bob .bool
          ⟨.inr bobBinding, binding_layouts.2⟩ _ rfl rfl value output
        change native.config.outputs bobBinding = some (.success value) at binding
        rw [failed] at binding
        cases binding
  cases node : nodeView graph bobReveal with
  | bind owner payload kind code => cases kind.symm.trans reveal_layouts.2
  | sample payload law kind code => cases kind.symm.trans reveal_layouts.2
  | resolve owner payload binding checks kind code =>
      have same := EventField.publication.inj (kind.symm.trans reveal_layouts.2)
      subst payload
      rw [RecoveryState.publicationFailed, node, failedOutput]
      rfl

/-- A clean player's standing bad declaration has its literal exclusion payoff
at every completed native terminal. No future-rationality premise is used. -/
theorem standing_bad_terminal_payoff (history : rawProtocol.History) (current : app.Control)
    (state : history.state = some current)
    (complete : current.execution.application.current.native.config.cut.Terminal)
    (who : Player) (clean : OwnPermitted who current.execution)
    (failed : if who = alice then
      current.execution.application.current.native.config.outputs aliceBinding = some .failure
      else current.execution.application.current.native.config.outputs bobBinding = some .failure) :
    rawPayoff who history = -1 := by
  classical
  have trace := rawMenu.toRawTrace initial horizon scheduler history.trace
  rw [state] at trace
  have native := raw_native_valid scheduler current trace
  have coverage := phaseFailureCoverage_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon scheduler trace
  have excluded : who ∈ current.execution.application.current.excluded := by
    fin_cases who
    · have bad : current.execution.application.current.native.config.outputs aliceBinding =
          some .failure := by simpa [OnePacketCommitRevealHypotheses.alice] using failed
      have published := alice_failed_binding_publication _ native.active complete bad
      exact coverage.active.covered aliceReveal alice reveal_actors.1 (Or.inr published)
    · have bad : current.execution.application.current.native.config.outputs bobBinding =
          some .failure := by simpa using failed
      have published := bob_failed_binding_publication _ native.active complete bad
      exact coverage.active.covered bobReveal bob reveal_actors.2 (Or.inr published)
  rw [rawPayoff_terminal_formula history current state complete who clean,
    ite_eq_left excluded]

/-- A failed original declaration remains bad through the actual arbitrary raw
physical tail after both original bindings have completed. -/
theorem completed_binding_failure_persists (selected : app.Scheduler)
    (players : Player → app.Policy) (remaining count : Nat) (before after : app.Execution)
    (trace : (app.protocol initial horizon selected).Trace (some ⟨remaining, none, before⟩))
    (aliceDone : aliceBinding ∈ before.application.current.native.config.cut.completed)
    (bobDone : bobBinding ∈ before.application.current.native.config.cut.completed)
    (supported : after ∈ (app.runRounds selected players count before).support)
    (who : Player) (failed : if who = alice then
      before.application.current.native.config.outputs aliceBinding = some .failure
      else before.application.current.native.config.outputs bobBinding = some .failure) :
    if who = alice then
      after.application.current.native.config.outputs aliceBinding = some .failure
      else after.application.current.native.config.outputs bobBinding = some .failure := by
  classical
  have tail := completed_bindings_publication_tail selected _ trace aliceDone bobDone
  have retained := publication_tail_run_keepsStore selected players count before after
    tail supported
  fin_cases who
  · have bad : before.application.current.native.config.outputs aliceBinding = some .failure := by
      simpa [OnePacketCommitRevealHypotheses.alice] using failed
    have preserved := retained (.inr aliceBinding) .failure bad
    change after.application.current.native.config.outputs aliceBinding = some .failure at preserved
    simpa [OnePacketCommitRevealHypotheses.alice] using preserved
  · have bad : before.application.current.native.config.outputs bobBinding = some .failure := by
      simpa using failed
    have preserved := retained (.inr bobBinding) .failure bad
    change after.application.current.native.config.outputs bobBinding = some .failure at preserved
    simpa [OnePacketCommitRevealHypotheses.alice, OnePacketCommitRevealHypotheses.bob]
      using preserved

end Vegas.Examples.CommitSeedSignalling
