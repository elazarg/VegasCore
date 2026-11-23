module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.CorrelatedInitialBitsService
public import Interaction.ReactiveRoundTrace

@[expose] public section

/-! # Repeated opportunities on the periodic common-bit ledger -/

noncomputable section

namespace Vegas.Examples.CorrelatedInitialBits.Service

open SourceProgram EventGraphRuntime Interaction GameTheory.Protocol

private abbrev event : graph.EventId := ⟨0, by decide⟩
private abbrev roster := Equiv.refl Bool
private abbrev menu := bounds.onePacketMenu timeouts leaks
private abbrev initial := Vegas.initialLaw setup
private abbrev cmd := PeriodicService.command graph roster leaks

private theorem command_not_sample (n : Nat) (view : app.EnvironmentView) (i : graph.EventId) :
    cmd n view ≠ .application (.executeSample i) := by
  unfold cmd PeriodicService.command ReactiveApplication.pendingHeadCommand
  dsimp only
  cases view.network.pending.head? <;>
    simp only <;> split_ifs <;> rintro ⟨⟩

private theorem environment_quiet {before after : app.Execution} {command : app.Command}
    (clock : before.application.clock < 6) (clear : before.application.config.defaulted = ∅)
    (empty : before.network.pending = []) (sample : ∀ i, command ≠ .application (.executeSample i))
    (moved : after ∈ (before.environmentStep app command).support) :
    after.application.config = before.application.config ∧ after.network.pending = [] := by
  obtain ⟨middle, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp moved
  cases command with
  | wait =>
    cases (PMF.mem_support_pure_iff _ _).mp supported
    exact ⟨rfl, empty⟩
  | activate who =>
    obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact ⟨rfl, empty⟩
  | «include» id =>
    cases (PMF.mem_support_pure_iff _ _).mp supported
    have kept : before.includePending app id = before := by
      simp [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        MessageNetwork.lookup, empty]
    simpa only [kept] using And.intro (rfl : before.application.config = _) empty
  | application action =>
    obtain ⟨native, nativeSupported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    obtain ⟨original, step, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp nativeSupported
    have same : original.config = before.application.config := by
      cases action with
      | advanceClock =>
        cases (PMF.mem_support_pure_iff _ _).mp step
        rfl
      | executeSample i => exact False.elim (sample i rfl)
      | expire i =>
        cases (PMF.mem_support_pure_iff _ _).mp step
        unfold expire
        split
        · split
          · rfl
          · rename_i entered _
            have early : ¬ timeouts.duration i ≤ before.application.clock - entered := by
              change ¬ 6 ≤ _
              omega
            simp only [early, ↓reduceDIte]
        · rfl
    exact ⟨(congrArg State.config (original.drain_eq_of_empty (same ▸ clear))).trans same, empty⟩

private abbrev inputs : graph.Inputs := setup.eventInputs (sourceInitial false)
private abbrev start := State.initial (graph := graph) inputs

private theorem ownerTurn (execution : app.Execution) (same : execution.application.config =
    start.config) : execution.application.publicView.ownTurn? false = some event := by
  apply ownTurn?_of_ready setup _ _ rfl
  rw [same]
  decide

private structure Prefix (n : Nat) (execution : app.Execution) : Prop where
  trace : Nonempty ((menu.protocol initial horizon scheduler).Trace
    (some ⟨horizon - n, none, execution⟩))
  cursor : execution.environmentRecall.length = n
  clock : PeriodicService.ClockAligned inputs 0 execution
  config : execution.application.config = start.config
  empty : execution.network.pending = []
  silent : ∀ entry ∈ execution.logs false, entry.action.transmission = none
  passed : 135 < n → ∃ entry ∈ execution.logs false, ActivatedAt setup timeouts leaks false
    event entry

private theorem initial_prefix : ∃ execution, Prefix 0 execution := by
  have member : sourceInitial false ∈ setup.initialLaw.support := by
    apply (PMF.mem_support_iff _ _).mpr
    change setup.initialLaw (sourceState false false) ≠ 0
    rw [initialLaw_apply]
    norm_num
  have initialized : start ∈ initial.support := (PMF.mem_support_map_iff _ _ _).mpr
    ⟨sourceInitial false, member, rfl⟩
  refine ⟨ReactiveApplication.Execution.initial app start, ?_⟩
  exact ⟨menu.trace_initial initial horizon scheduler start initialized, rfl,
    ⟨State.initial_invariant _, rfl⟩, rfl, rfl, (fun _ h => nomatch h), by omega⟩

private theorem prefix_succ {n : Nat} (small : n < 277) {execution : app.Execution}
    (priorState : Prefix n execution) : ∃ next, Prefix (n + 1) next := by
  let view := execution.observeEnvironment app
  let selected := cmd n view
  have scheduled : selected ∈ (scheduler execution.environmentRecall view).support := by
    apply (PMF.mem_support_pure_iff _ _).mpr
    change cmd n view = cmd execution.environmentRecall.length view
    rw [priorState.cursor]
  obtain ⟨middle, moved⟩ := (execution.environmentStep app selected).support_nonempty
  have remaining : horizon - n = (horizon - (n + 1)) + 1 := by
    change 2272 - n = 2272 - (n + 1) + 1
    omega
  obtain ⟨prior⟩ := priorState.trace
  rw [remaining] at prior
  obtain ⟨traced⟩ := menu.trace_environment initial horizon scheduler _ execution middle selected
    prior scheduled moved
  have aligned := (PeriodicService.clock_aligned_invariant (roster := roster) inputs 0).environment
    execution middle selected priorState.clock scheduled moved
  have clock : execution.application.clock < 6 := by
    rw [priorState.clock.clock, priorState.cursor]
    change 0 + n / 71 < 6
    omega
  have clear : execution.application.config.defaulted = ∅ := by rw [priorState.config]; rfl
  obtain ⟨same, empty⟩ := environment_quiet clock clear priorState.empty (command_not_sample n view)
    moved
  have config := same.trans priorState.config
  have cursor : middle.environmentRecall.length = n + 1 := by
    rw [app.environmentStep_environmentRecall _ _ _ moved, List.length_append,
      List.length_singleton, priorState.cursor]
  have logs := congrFun (app.environmentStep_recall execution middle selected moved) false
  have first : n = 135 → selected = .activate false := by
    rintro rfl
    exact PeriodicService.first_activation (roster := roster) 1 view (by decide)
  cases active : selected.actor? app with
  | none =>
    rw [active] at traced
    refine ⟨middle, ⟨⟨traced⟩, cursor, aligned, config, empty, ?_, ?_⟩⟩
    · rw [logs]
      exact priorState.silent
    · intro later
      have diff : n ≠ 135 := fun eq => by rw [first eq] at active; cases active
      rw [logs]
      exact priorState.passed (by omega)
  | some who =>
    rw [active] at traced
    let passed := middle.respond app who ⟨none⟩
    obtain ⟨nextTrace⟩ := menu.trace_respond initial horizon scheduler _ middle who ⟨none⟩ traced
      (bounds.silence_onePacket timeouts leaks ..)
    have nextClock := (PeriodicService.clock_aligned_invariant (roster := roster) inputs 0).respond
      middle who ⟨none⟩ aligned
    refine ⟨passed, ⟨⟨nextTrace⟩, cursor, nextClock, config, empty, ?_, ?_⟩⟩
    · intro entry recorded
      change entry ∈ (if false = who then middle.logs who ++
          [⟨middle.observe app who, ⟨none⟩, none⟩] else middle.logs false) at recorded
      split at recorded
      · rename_i eq
        subst who
        rcases List.mem_append.mp recorded with old | fresh
        · exact priorState.silent entry (logs ▸ old)
        · cases List.mem_singleton.mp fresh
          rfl
      · exact priorState.silent entry (logs ▸ recorded)
    · intro later
      by_cases atFirst : n = 135
      · rw [first atFirst] at active
        change some false = some who at active
        cases Option.some.inj active
        refine ⟨⟨middle.observe app false, ⟨none⟩, none⟩, ?_, ownerTurn middle config⟩
        simp [passed, ReactiveApplication.Execution.respond]
      · obtain ⟨entry, old, atTurn⟩ := priorState.passed (by omega)
        exact ⟨entry, app.respond_recall_mono middle who false ⟨none⟩ (logs ▸ old), atTurn⟩

private theorem silent_prefix (n : Nat) (small : n ≤ 277) : ∃ execution, Prefix n execution := by
  induction n with
  | zero => exact initial_prefix
  | succ n ih =>
    obtain ⟨execution, prior⟩ := ih (by omega)
    exact prefix_succ (by omega) prior

/-- After an initial silence, the owner of the first binding has a second genuine
opportunity at clock three on a legal one-packet history of the periodic service. -/
theorem repeated_opportunity :
    ∃ site : (onePacketInformation setup timeouts leaks bounds horizon scheduler).InformationSite
        false, LateDelivery setup timeouts leaks false site.1 := by
  obtain ⟨before, priorState⟩ := silent_prefix 277 (by decide)
  let command : app.Command := .activate false
  obtain ⟨after, moved⟩ := (before.environmentStep app command).support_nonempty
  have scheduled : command ∈ (scheduler before.environmentRecall
      (before.observeEnvironment app)).support := by
    apply (PMF.mem_support_pure_iff _ _).mpr
    change command = cmd before.environmentRecall.length (before.observeEnvironment app)
    rw [priorState.cursor]
    exact (PeriodicService.first_activation (roster := roster) 3 _ (by decide)).symm
  obtain ⟨prior⟩ := priorState.trace
  obtain ⟨trace⟩ := menu.trace_environment initial horizon scheduler 1994 before after command
    prior scheduled moved
  let info := some (after.logs false, after.observe app false)
  have observed : (menu.information initial horizon scheduler).infoOf false trace = info := by
    change (menu.signals initial horizon scheduler).infoOf false trace = _
    rw [menu.info]
    rfl
  let site : (onePacketInformation setup timeouts leaks bounds horizon scheduler).InformationSite
      false := ⟨info, ⟨⟨⟨_, trace⟩, observed⟩, (fun terminal => by
          have stopped : 1994 = 0 := terminal.1
          omega),
        ⟨⟨none⟩, ⟨⟨none⟩, bounds.silence_onePacket timeouts leaks _ _ _, rfl⟩⟩⟩⟩
  have logs := congrFun (app.environmentStep_recall before after command moved) false
  obtain ⟨middle, learned, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp moved
  obtain ⟨selection, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp learned
  refine ⟨site, _, _, event, rfl, pendingEvent_of_spec (setup := setup)
    (ownerTurn before priorState.config) ?_, ?_⟩
  · unfold eventRecorded
    apply Bool.eq_false_iff.mpr
    intro yes
    obtain ⟨entry, mem, chosen⟩ := List.any_eq_true.mp yes
    have no := priorState.silent entry (logs ▸ mem)
    simp [submittedEvent?, no] at chosen
  · obtain ⟨entry, mem, activated⟩ := priorState.passed (by decide)
    exact ⟨entry, logs ▸ mem, activated⟩

/-- The concrete correlated-bit ledger falls outside the single-opportunity prior
alternative of the prior preservation theorem. -/
theorem not_singleSubmissionOpportunity :
    ¬ SingleSubmissionOpportunity setup timeouts leaks bounds horizon scheduler := by
  obtain ⟨site, late⟩ := repeated_opportunity
  exact fun once => once false site late

/-- The original prior condition fails on the concrete periodic service: no public initial
signal renders these private inputs independent, and the first binding has a retry. -/
theorem not_sequentialPriorCondition :
    ¬ SequentialPriorCondition setup timeouts leaks bounds horizon scheduler := by
  intro prior
  cases prior with
  | independent observed independent visible =>
    exact not_independent_of_publicSignal observed visible independent
  | singleOpportunity _ once => exact not_singleSubmissionOpportunity once

end Vegas.Examples.CorrelatedInitialBits.Service
