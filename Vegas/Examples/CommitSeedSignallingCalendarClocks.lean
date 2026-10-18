/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingTailRecall

/-! # Actual singleton relative clock words in continuation service -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem tail_callback_elapsed (menu : app.ResponseMenu)
    (seeds : Seeds) (current : app.Control)
    (trace : (menu.protocol initial horizon (family seeds)).Trace (some current))
    (owner : Player) (active : current.actor = some owner)
    (coordinate : CommitAttemptEvent graph) (retired : coordinate.attempt ≠ originalAttempt)
    (request : current.execution.application.SeedRequest owner coordinate) :
    (PhaseSeedScheduler.informationInput runtime leaks coordinate owner
      (current.execution.recall owner) (current.execution.observe app owner)).elapsed = 0 := by
  rcases current with ⟨remaining, acting, execution⟩
  cases active
  obtain ⟨before, _word, selected, moved, _input⟩ :=
    PhaseSeedScheduler.active_informationInput_of_trace runtime leaks menu initial horizon
      (family seeds) remaining owner execution trace coordinate
  have application : execution.application = before.application := by
    obtain ⟨updated, reached, rfl⟩ := PMF.support_map .. ▸ moved
    obtain ⟨sample, _supported, rfl⟩ := PMF.support_map .. ▸ reached
    rfl
  have index := tailIndex_after_same_attempt before execution (.activate owner) moved
    (congrArg PhaseRuntimeState.attempt application)
  have selectedEq : choose seeds before.environmentRecall (before.observeEnvironment app) =
      .activate owner := ((PMF.mem_support_pure_iff _ _).mp selected).symm
  obtain ⟨phase, installed, inside⟩ := request.2.1
  have head := Option.mem_def.mp installed
  have blocks : phase = commitmentPhase ∨ phase = publicationPhase := by
    rcases raw_phases_cases (family seeds) _
      (menu.toRawTrace initial horizon (family seeds) trace) with all | reveal | empty
    · rw [all] at head
      exact Or.inl (Option.some.inj head).symm
    · rw [reveal] at head
      exact Or.inr (Option.some.inj head).symm
    · rw [empty] at head
      cases head
  have phaseView : (before.observeEnvironment app).application.phase =
      some (phase.kind, phase.low, phase.high) := by
    change before.application.phases.head?.map
      (fun current => (current.kind, current.low, current.high)) = _
    rw [← application, head]
    rfl
  have notOriginal : (before.observeEnvironment app).application.attempt ≠ originalAttempt := by
    change before.application.attempt ≠ originalAttempt
    rw [← application, ← request.1]
    exact retired
  rw [choose, ite_eq_right notOriginal, phaseView] at selectedEq
  have elapsed := tail_request_elapsed seeds _
    (menu.toRawTrace initial horizon (family seeds) trace) coordinate owner retired request
  have interval := (RuntimePhase.mem_events phase coordinate.event).mp inside
  change PhaseSeedScheduler.elapsed runtime leaks coordinate (execution.observeEnvironment app) = 0
  rw [index] at elapsed
  rcases blocks with rfl | rfl
  · change retryCommand (tailIndex before.environmentRecall (before.observeEnvironment app))
      before.environmentRecall (before.observeEnvironment app) = .activate owner at selectedEq
    have turn := (retry_activation _ _ _ _ selectedEq).1
    change 0 ≤ coordinate.event.val ∧ coordinate.event.val < 2 at interval
    rw [ite_eq_left interval.2, turn] at elapsed
    exact elapsed
  · change revealCommand (tailIndex before.environmentRecall (before.observeEnvironment app))
      before.environmentRecall (before.observeEnvironment app) = .activate owner at selectedEq
    have turns := reveal_activation _ _ _ _ selectedEq
    change 2 ≤ coordinate.event.val ∧ coordinate.event.val < 4 at interval
    rw [ite_eq_right (by omega : ¬ coordinate.event.val < 2)] at elapsed
    rcases turns with ⟨turn, _owner⟩ | ⟨turn, _owner⟩
    all_goals rw [turn] at elapsed
    all_goals exact elapsed

private theorem tail_callback_own_word_nil (menu : app.ResponseMenu)
    (silence : ∀ owner past view,
      (⟨none⟩ : app.Action) ∈ menu.actions owner past view) (seeds : Seeds) (current : app.Control)
    (trace : (menu.protocol initial horizon (family seeds)).Trace (some current))
    (owner : Player) (active : current.actor = some owner)
    (coordinate : CommitAttemptEvent graph) (retired : coordinate.attempt ≠ originalAttempt)
    (request : current.execution.application.SeedRequest owner coordinate) :
    PhaseSeedScheduler.ownerWord runtime leaks coordinate owner (current.execution.recall owner) =
      [] := by
  classical
  rcases current with ⟨remaining, acting, execution⟩
  cases active
  obtain ⟨responded⟩ := menu.trace_respond initial horizon (family seeds) remaining
    execution owner ⟨none⟩ trace (silence owner _ _)
  let last : app.PlayerEntry := ⟨execution.observe app owner, ⟨none⟩, none⟩
  have afterRecall : (execution.respond app owner ⟨none⟩).recall owner =
      execution.recall owner ++ [last] := by
    simp only [ReactiveApplication.Execution.respond, last, ite_true]
  have valid := raw_native_valid (family seeds) _
    (menu.toRawTrace initial horizon (family seeds) trace)
  have lastRequest :
      PhaseRuntimeState.requests last.beforeView.application.2 owner coordinate := by
    exact (PhaseRuntimeState.requests_publicView _ valid owner coordinate).mpr request
  have empty : (execution.recall owner).filter (fun entry => decide
      (PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro entry member recorded
    have requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate :=
      of_decide_eq_true recorded
    obtain ⟨earlier, later, recalled⟩ := List.mem_iff_append.mp member
    have full : (execution.respond app owner ⟨none⟩).recall owner =
        earlier ++ entry :: (later ++ last :: []) := by
      rw [afterRecall, recalled]
      simp only [List.append_assoc, List.cons_append]
    exact tail_recalled_callbacks_no_repeat menu silence seeds
      _ responded coordinate owner retired earlier
      later [] entry last full requested lastRequest
  simp only [PhaseSeedScheduler.ownerWord, empty, List.map_nil]

/-- Every genuine continuation callback has the literal singleton relative
clock word. This follows from actual command turns and retained own recall,
with neither an elapsed-time premise nor a supplied calendar. -/
theorem tail_service_clocks (menu : app.ResponseMenu)
    (silence : ∀ owner past view,
      (⟨none⟩ : app.Action) ∈ menu.actions owner past view) (seeds : Seeds) (current : app.Control)
    (trace : (menu.protocol initial horizon (family seeds)).Trace (some current))
    (owner : Player) (active : current.actor = some owner)
    (coordinate : CommitAttemptEvent graph) (retired : coordinate.attempt ≠ originalAttempt)
    (request : current.execution.application.SeedRequest owner coordinate) :
    PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner
      (current.execution.recall owner) (current.execution.observe app owner) = [0] := by
  have empty := tail_callback_own_word_nil menu silence seeds
    current trace owner active coordinate retired
    request
  have elapsed := tail_callback_elapsed menu seeds
    current trace owner active coordinate retired request
  change (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner
      (current.execution.recall owner)).map Prod.fst ++
      [(PhaseSeedScheduler.informationInput runtime leaks coordinate owner
        (current.execution.recall owner) (current.execution.observe app owner)).elapsed] = [0]
  rw [empty, List.map_nil, List.nil_append, elapsed]

end Vegas.Examples.CommitSeedSignalling
