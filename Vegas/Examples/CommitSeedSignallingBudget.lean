/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingRevealCompletion

/-! # A uniform completion bound for arbitrary raw responses -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private abbrev originalInput : graph.Inputs :=
  encodeInputs (Env.empty (CellVal simpleExpr))

private theorem live_generation_bound (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (live : current.execution.application.phases ≠ []) :
    current.execution.application.generation ≤ 1 := by
  classical
  have geometry := raw_phase_geometry (family seeds) current trace
  obtain ⟨phase, installed, block⟩ : ∃ phase,
      current.execution.application.phases.head? = some phase ∧
        (phase = commitmentPhase ∨ phase = publicationPhase) := by
    rcases raw_phases_cases (family seeds) current trace with phases | phases | phases
    · exact ⟨commitmentPhase, by rw [phases]; rfl, Or.inl rfl⟩
    · exact ⟨publicationPhase, by rw [phases]; rfl, Or.inr rfl⟩
    · exact (live phases).elim
  obtain ⟨event, inside, unfinished⟩ : ∃ event ∈ phase.events,
      event ∉ current.execution.application.current.native.config.cut.completed := by
    by_contra absent
    apply geometry.2.1 phase installed
    intro event inside
    by_contra unfinished
    exact absent ⟨event, inside, unfinished⟩
  obtain ⟨owner, acting⟩ : ∃ owner, graph.actor? event = some owner := by
    change Fin 4 at event
    fin_cases event
    · exact ⟨alice, binding_actors.1⟩
    · exact ⟨bob, binding_actors.2⟩
    · exact ⟨alice, reveal_actors.1⟩
    · exact ⟨bob, reveal_actors.2⟩
  have request := raw_phase_event_request (family seeds) current trace phase installed block
    event inside owner acting unfinished
  have survives := request.2.2.2.2
  have strict : current.execution.application.current.excluded ⊂ (Finset.univ : Finset Player) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, by
      intro same
      exact survives (same ▸ Finset.mem_univ owner)⟩
  have count := Finset.card_lt_card strict
  have budget := (phaseApplication_seedBudget runtime leaks).history initial horizon
    (family seeds) (by
      intro state supported
      rw [initial_eq_pure, PMF.mem_support_pure_iff] at supported
      subst state
      exact PhaseRuntimeState.initial_seedBudget plan originalInput) trace
  have bounded := budget.current_generation
  change current.execution.application.current.excluded.card < 2 at count
  omega

private def commandOrdinal (execution : app.Execution) : Nat :=
  if execution.application.attempt = originalAttempt then execution.environmentRecall.length
  else if execution.application.attempt.phase = 0 then
    22 + 9 * (execution.application.generation - 1) +
      tailIndex execution.environmentRecall (execution.observeEnvironment app)
  else 31 + 12 * execution.application.generation +
      tailIndex execution.environmentRecall (execution.observeEnvironment app)

private theorem live_ordinal_bound (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (live : current.execution.application.phases ≠ []) :
    commandOrdinal current.execution < 55 := by
  have generation := live_generation_bound seeds current trace live
  by_cases original : current.execution.application.attempt = originalAttempt
  · have length : current.execution.environmentRecall.length < 22 := by
      by_contra enough
      exact original_attempt_retired seeds current trace (by omega) original
    simp only [commandOrdinal, ite_eq_left original]
    omega
  · rcases raw_phases_cases (family seeds) current trace with phases | phases | phases
    · have zero : current.execution.application.attempt.phase = 0 := by
        change (current.execution.application.phases.head?.map RuntimePhase.low).getD 4 = 0
        rw [phases]
        rfl
      have index := retry_index_bound seeds trace original (by rw [phases]; rfl)
      simp only [commandOrdinal, ite_eq_right original, ite_eq_left zero]
      omega
    · have two : current.execution.application.attempt.phase = 2 := by
        change (current.execution.application.phases.head?.map RuntimePhase.low).getD 4 = 2
        rw [phases]
        rfl
      have index := publication_index_bound seeds current trace original (by rw [phases]; rfl)
      have notZero : current.execution.application.attempt.phase ≠ 0 := by omega
      simp only [commandOrdinal, ite_eq_right original, ite_eq_right notZero]
      omega
    · exact (live phases).elim

private theorem ordinal_environment_step (seeds : Seeds) (before after : app.Control)
    (beforeTrace : (app.protocol initial horizon (family seeds)).Trace (some before))
    (afterTrace : (app.protocol initial horizon (family seeds)).Trace (some after))
    (command : app.Command)
    (moved : after.execution ∈ (before.execution.environmentStep app command).support)
    (afterLive : after.execution.application.phases ≠ []) :
    before.execution.application.phases ≠ [] ∧
      commandOrdinal before.execution + 1 ≤ commandOrdinal after.execution := by
  have geometry := raw_phase_geometry (family seeds) before beforeTrace
  have progress := (phaseApplication_namespace_progress runtime leaks).environmentStep
    before.execution after.execution command moved geometry.1.adjacent
  have beforeLive : before.execution.application.phases ≠ [] := by
    intro empty
    have low := progress.2
    change (before.execution.application.phases.head?.map RuntimePhase.low).getD 4 ≤
      (after.execution.application.phases.head?.map RuntimePhase.low).getD 4 at low
    rcases raw_phases_cases (family seeds) after afterTrace with phases | phases | phases
    · rw [empty, phases] at low
      norm_num [commitmentPhase] at low
    · rw [empty, phases] at low
      norm_num [publicationPhase] at low
    · exact afterLive phases
  refine ⟨beforeLive, ?_⟩
  have beforeGen := live_generation_bound seeds before beforeTrace beforeLive
  have afterGen := live_generation_bound seeds after afterTrace afterLive
  have counts : after.execution.environmentRecall.length =
      before.execution.environmentRecall.length + 1 := by
    rw [app.environmentStep_environmentRecall before.execution after.execution command moved,
      List.length_append, List.length_singleton]
  by_cases same : before.execution.application.attempt = after.execution.application.attempt
  · have index := tailIndex_after_same_attempt before.execution after.execution command moved
      same.symm
    have generation : before.execution.application.generation =
        after.execution.application.generation := congrArg CommitAttemptId.generation same
    unfold commandOrdinal
    rw [← same, ← generation]
    split
    · omega
    · split <;> omega
  · by_cases beforeOriginal : before.execution.application.attempt = originalAttempt
    · have beforeIndex : before.execution.environmentRecall.length < 22 := by
        by_contra enough
        exact original_attempt_retired seeds before beforeTrace (by omega) beforeOriginal
      have afterOriginal : after.execution.application.attempt ≠ originalAttempt := by
        intro original
        exact same (beforeOriginal.trans original.symm)
      simp only [commandOrdinal, ite_eq_left beforeOriginal, ite_eq_right afterOriginal]
      split <;> omega
    · have afterOriginal : after.execution.application.attempt ≠ originalAttempt := by
        intro original
        apply beforeOriginal
        rcases address : before.execution.application.attempt with ⟨phase, generation⟩
        rw [original, address] at progress
        change generation ≤ 0 ∧ phase ≤ 0 at progress
        have phaseZero : phase = 0 := by omega
        have generationZero : generation = 0 := by omega
        simp only [phaseZero, generationZero, originalAttempt]
      have changed : before.execution.application.generation ≠
          after.execution.application.generation ∨
          before.execution.application.attempt.phase ≠
            after.execution.application.attempt.phase := by
        by_contra unchanged
        push Not at unchanged
        apply same
        have generation : before.execution.application.attempt.generation =
            after.execution.application.attempt.generation := unchanged.1
        have phase := unchanged.2
        cases first : before.execution.application.attempt with
        | mk firstPhase firstGeneration =>
            cases second : after.execution.application.attempt with
            | mk secondPhase secondGeneration =>
                simp only [first, second] at generation phase
                simp only [CommitAttemptId.mk.injEq]
                exact ⟨phase, generation⟩
      have beforeNotZero : before.execution.application.attempt.phase ≠ 0 ∨
          before.execution.application.attempt.generation ≠ 0 := by
        by_contra zero
        push Not at zero
        apply beforeOriginal
        cases address : before.execution.application.attempt with
        | mk phase generation =>
            simp only [address] at zero
            simp only [zero.1, zero.2, originalAttempt]
      rcases raw_phases_cases (family seeds) before beforeTrace with beforePhases |
        beforePhases | beforePhases
      all_goals
        rcases raw_phases_cases (family seeds) after afterTrace with afterPhases |
          afterPhases | afterPhases
      all_goals try exact (beforeLive beforePhases).elim
      all_goals try exact (afterLive afterPhases).elim
      all_goals
        have cursor : tailIndex before.execution.environmentRecall
            (before.execution.observeEnvironment app) < 12 := by
          first
          | exact lt_trans
              (retry_index_bound seeds beforeTrace beforeOriginal (by rw [beforePhases]; rfl))
              (by decide : 9 < 12)
          | exact publication_index_bound seeds before beforeTrace beforeOriginal
              (by rw [beforePhases]; rfl)
      all_goals
        have firstLow : before.execution.application.attempt.phase =
            (before.execution.application.phases.head?.map RuntimePhase.low).getD 4 := rfl
        have secondLow : after.execution.application.attempt.phase =
            (after.execution.application.phases.head?.map RuntimePhase.low).getD 4 := rfl
        rw [beforePhases] at firstLow
        rw [afterPhases] at secondLow
        norm_num [commitmentPhase, publicationPhase] at firstLow secondLow
      all_goals
        simp only [commandOrdinal, ite_eq_right beforeOriginal]
        simp only [ite_eq_right afterOriginal]
        simp only [firstLow, secondLow, OfNat.ofNat_ne_zero, ite_true, ite_false]
      all_goals
        have firstGeneration : before.execution.application.attempt.generation =
            before.execution.application.generation := rfl
        have secondGeneration : after.execution.application.attempt.generation =
            after.execution.application.generation := rfl
        omega

private theorem ordinal_respond (execution : app.Execution) (owner : Player)
    (response : app.Action) :
    commandOrdinal (execution.respond app owner response) = commandOrdinal execution := by
  have same : (execution.respond app owner response).application.attempt =
      execution.application.attempt := by
    rcases response with ⟨packet⟩
    cases packet <;> rfl
  have generation : (execution.respond app owner response).application.generation =
      execution.application.generation := congrArg CommitAttemptId.generation same
  have index := tailIndex_congr_attempt execution.environmentRecall
    ((execution.respond app owner response).observeEnvironment app)
    (execution.observeEnvironment app) same
  simp only [commandOrdinal, app.respond_environmentRecall, same, generation, index]

private theorem raw_command_accounting (seeds : Seeds) :
    ∀ {state} (_trace : (app.protocol initial horizon (family seeds)).Trace state),
      state.elim True (fun current => current.execution.application.phases ≠ [] →
        current.execution.environmentRecall.length ≤ commandOrdinal current.execution) := by
  intro state trace
  induction trace with
  | start => trivial
  | @extend source target prior joint legal reached ih =>
      have targetTrace := prior.extend joint legal reached
      change target ∈ (app.transition initial horizon (family seeds) source joint).support
        at reached
      cases source with
      | none =>
          obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
          rw [initial_eq_pure, PMF.mem_support_pure_iff] at supported
          subst state
          intro _live
          exact Nat.zero_le _
      | some current =>
          rcases current with ⟨remaining, active, execution⟩
          change (execution.application.phases ≠ [] →
            execution.environmentRecall.length ≤ commandOrdinal execution) at ih
          cases active with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              intro live
              have phases :
                  (execution.respond app who ((joint who).getD ⟨none⟩)).application.phases =
                  execution.application.phases := by
                cases response : (joint who).getD ⟨none⟩ with
                | mk packet => cases packet <;> rfl
              change (execution.respond app who ((joint who).getD ⟨none⟩)).application.phases ≠ []
                at live
              rw [phases] at live
              simpa only [app.respond_environmentRecall, ordinal_respond] using ih live
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, _selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  intro live
                  change next.application.phases ≠ [] at live
                  obtain ⟨beforeLive, step⟩ := ordinal_environment_step seeds
                    ⟨remaining + 1, none, execution⟩
                    ⟨remaining, command.actor? app, next⟩ prior targetTrace command supported live
                  have beforeBound := ih beforeLive
                  have length : next.environmentRecall.length =
                      execution.environmentRecall.length + 1 := by
                    rw [app.environmentStep_environmentRecall execution next command supported,
                      List.length_append, List.length_singleton]
                  change next.environmentRecall.length ≤ commandOrdinal next
                  change commandOrdinal execution + 1 ≤ commandOrdinal next at step
                  omega

/-- The actual scheduler completes every graph event under unrestricted raw
responses before the fixed native horizon is exhausted. -/
theorem family_completesPlay (seeds : Seeds) :
    PhaseService.CompletesPlay runtime leaks initial horizon (family seeds) := by
  intro current trace terminal
  have finished : current.execution.application.phases = [] := by
    by_contra live
    have account := raw_command_accounting seeds trace live
    have bound := live_ordinal_bound seeds current trace live
    have horizonAccount := app.raw_trace_horizon initial horizon (family seeds) trace
    change current.remaining = 0 ∧ current.actor = none at terminal
    change current.execution.environmentRecall.length + current.remaining = 64 at horizonAccount
    omega
  exact (raw_phase_geometry (family seeds) current trace).1.terminal finished

/-- Every actual requested callback has enough environment rounds remaining
for protected inclusion; the native horizon cannot truncate its response. -/
theorem family_requested_remaining (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (request : current.execution.application.SeedRequest owner coordinate) :
    9 < current.remaining := by
  have live : current.execution.application.phases ≠ [] := by
    obtain ⟨phase, installed, _inside⟩ := request.2.1
    intro empty
    simp only [empty, List.head?_nil, Option.not_mem_none] at installed
  have account := raw_command_accounting seeds trace live
  have bound := live_ordinal_bound seeds current trace live
  have horizonAccount := app.raw_trace_horizon initial horizon (family seeds) trace
  change current.execution.environmentRecall.length + current.remaining = 64 at horizonAccount
  omega

end Vegas.Examples.CommitSeedSignalling
