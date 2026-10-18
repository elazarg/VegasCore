/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingCalendarClocks
import Vegas.Examples.CommitSeedSignallingUnresolved
import Vegas.Examples.CommitSeedSignallingLateBeliefs
import Vegas.Pending.PhaseAttemptCheckpoint

/-! # Original ready requests at every earlier service turn -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private abbrev originalInput : graph.Inputs :=
  encodeInputs (Env.empty (CellVal simpleExpr))

theorem resolved_prefix (menu : app.ResponseMenu)
    (seeds : Seeds) (before after : app.Control)
    (beforeTrace : (menu.protocol initial horizon (family seeds)).Trace (some before))
    (afterTrace : (menu.protocol initial horizon (family seeds)).Trace (some after))
    (kept : TracePrefix beforeTrace afterTrace) (coordinate : CommitAttemptEvent graph)
    (resolved : coordinate.Resolved before.execution.application) :
    coordinate.Resolved after.execution.application := by
  have along : ∀ {state}
      {trace : (menu.protocol initial horizon (family seeds)).Trace state},
      TracePrefix beforeTrace trace → ∃ current : app.Control, state = some current ∧
        coordinate.Resolved current.execution.application := by
    intro state trace retained
    induction retained with
    | refl => exact ⟨before, rfl, resolved⟩
    | @extend source target prior retained joint legal moved ih =>
        obtain ⟨current, rfl, already⟩ := ih
        change target ∈ (app.transition initial horizon (family seeds) (some current)
          joint).support at moved
        obtain ⟨next, rfl, _recall⟩ := app.transition_recall_prefix initial horizon (family seeds)
          current target joint moved
        have raw := menu.toRawTrace initial horizon (family seeds) prior
        have valid := raw_native_valid (family seeds) current raw
        have ordered := (raw_phase_geometry (family seeds) current raw).1.adjacent
        refine ⟨next, rfl, ?_⟩
        exact (phaseApplication_resolution runtime leaks coordinate).transition initial horizon
          (family seeds) current next joint moved originalInput valid ordered already
  obtain ⟨next, equal, result⟩ := along kept
  cases Option.some.inj equal
  exact result

/-- A still-requested original binding was genuinely requested at every
earlier physical prefix. This uses permanent coordinate resolution, without
requiring the whole execution or the other owner's current choices to be clear. -/
theorem original_binding_request_of_prefix (menu : app.ResponseMenu)
    (seeds : Seeds) (before after : app.Control)
    (beforeTrace : (menu.protocol initial horizon (family seeds)).Trace (some before))
    (afterTrace : (menu.protocol initial horizon (family seeds)).Trace (some after))
    (kept : TracePrefix beforeTrace afterTrace) (owner : Player)
    (request : after.execution.application.SeedRequest owner (originalCoordinate owner)) :
    before.execution.application.SeedRequest owner (originalCoordinate owner) := by
  apply original_binding_request_of_unresolved (family seeds) before
    (menu.toRawTrace initial horizon (family seeds) beforeTrace) owner
  intro resolved
  have later := resolved_prefix menu seeds before after beforeTrace afterTrace kept
    (originalCoordinate owner) resolved
  exact CommitAttemptEvent.Resolved.not_request (originalCoordinate owner)
    after.execution.application later owner request

def originalTurns (owner : Player) (bit : Bool) : List Nat :=
  if owner = alice then [0, if bit then 6 else 4, 9]
  else [1, if bit then 14 else 12, 17]

def originalClockWord (owner : Player) (bit : Bool) : Nat → List Nat
  | 0 => []
  | count + 1 => originalClockWord owner bit count ++
      if count ∈ originalTurns owner bit then [originalClock count] else []

private theorem activateReady_activation (source owner : Player) (event : graph.EventId)
    (view : app.EnvironmentView) :
    activateReady source event view = .activate owner ↔
      source = owner ∧ ready source event view = true := by
  unfold activateReady
  by_cases enabled : ready source event view = true
  · rw [ite_eq_left enabled]
    constructor
    · intro same
      exact ⟨ReactiveApplication.Command.activate.inj same, enabled⟩
    · rintro ⟨rfl, _⟩
      rfl
  · rw [ite_eq_right enabled]
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨_same, readyNow⟩
      exact (enabled readyNow).elim

private theorem pollCommand_activation (source owner : Player) (bit wanted : Bool)
    (view : app.EnvironmentView) :
    pollCommand source bit wanted view = .activate owner ↔
      bit = wanted ∧ source = owner ∧ ready source (bindingEvent source) view = true := by
  unfold pollCommand
  by_cases selected : bit = wanted
  · rw [ite_eq_left selected, activateReady_activation]
    exact ⟨fun facts => ⟨selected, facts⟩, fun facts => facts.2⟩
  · rw [ite_eq_right selected]
    constructor
    · intro impossible
      cases impossible
    · intro facts
      exact (selected facts.1).elim

theorem original_command_activation (seeds : Seeds) (owner : Player) (position : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (readyOwner : ready owner (bindingEvent owner) view = true) :
    originalCommand seeds position past view = .activate owner ↔
      position ∈ originalTurns owner (seeds.2 (originalAddress owner)) := by
  classical
  constructor
  · intro selected
    have bounded : position < 22 := by
      by_contra late
      rw [originalCommand_bound seeds position past view (by omega)] at selected
      cases selected
    have positions := original_activation_positions seeds position past view owner bounded selected
    rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change activateReady alice aliceBinding view = .activate owner at selected
      obtain ⟨rfl, _enabled⟩ := (activateReady_activation _ _ _ _).mp selected
      change 0 ∈ [0, if seeds.2 (originalAddress alice) then 6 else 4, 9]
      exact List.mem_cons_self
    · change activateReady bob bobBinding view = .activate owner at selected
      obtain ⟨rfl, _enabled⟩ := (activateReady_activation _ _ _ _).mp selected
      change 1 ∈ [1, if seeds.2 (originalAddress bob) then 14 else 12, 17]
      exact List.mem_cons_self
    · change pollCommand alice (seeds.2 (originalAddress alice)) false view =
          .activate owner at selected
      obtain ⟨bitEq, rfl, _enabled⟩ := (pollCommand_activation _ _ _ _ _).mp selected
      change 4 ∈ [0, if seeds.2 (originalAddress alice) then 6 else 4, 9]
      rw [bitEq]
      decide
    · change pollCommand alice (seeds.2 (originalAddress alice)) true view =
          .activate owner at selected
      obtain ⟨bitEq, rfl, _enabled⟩ := (pollCommand_activation _ _ _ _ _).mp selected
      change 6 ∈ [0, if seeds.2 (originalAddress alice) then 6 else 4, 9]
      rw [bitEq]
      decide
    · change activateReady alice aliceBinding view = .activate owner at selected
      obtain ⟨rfl, _enabled⟩ := (activateReady_activation _ _ _ _).mp selected
      change 9 ∈ [0, if seeds.2 (originalAddress alice) then 6 else 4, 9]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · change pollCommand bob (seeds.2 (originalAddress bob)) false view =
          .activate owner at selected
      obtain ⟨bitEq, rfl, _enabled⟩ := (pollCommand_activation _ _ _ _ _).mp selected
      change 12 ∈ [1, if seeds.2 (originalAddress bob) then 14 else 12, 17]
      rw [bitEq]
      decide
    · change pollCommand bob (seeds.2 (originalAddress bob)) true view =
          .activate owner at selected
      obtain ⟨bitEq, rfl, _enabled⟩ := (pollCommand_activation _ _ _ _ _).mp selected
      change 14 ∈ [1, if seeds.2 (originalAddress bob) then 14 else 12, 17]
      rw [bitEq]
      decide
    · change activateReady bob bobBinding view = .activate owner at selected
      obtain ⟨rfl, _enabled⟩ := (activateReady_activation _ _ _ _).mp selected
      change 17 ∈ [1, if seeds.2 (originalAddress bob) then 14 else 12, 17]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · intro member
    have owners : owner = alice ∨ owner = bob := by fin_cases owner <;> decide
    rcases owners with rfl | rfl
    · change ready alice aliceBinding view = true at readyOwner
      cases bitEq : seeds.2 (originalAddress alice)
      all_goals
        norm_num [originalTurns, bitEq] at member
        rcases member with rfl | rfl | rfl
        all_goals dsimp only [originalCommand]
        all_goals first
          | exact (activateReady_activation _ _ _ _).mpr ⟨rfl, readyOwner⟩
          | exact (pollCommand_activation _ _ _ _ _).mpr ⟨bitEq, rfl, readyOwner⟩
    · change ready bob bobBinding view = true at readyOwner
      cases bitEq : seeds.2 (originalAddress bob)
      all_goals
        norm_num [originalTurns, bitEq, alice, bob, Fin.ext_iff] at member
        rcases member with rfl | rfl | rfl
        all_goals dsimp only [originalCommand]
        all_goals first
          | exact (activateReady_activation _ _ _ _).mpr ⟨rfl, readyOwner⟩
          | exact (pollCommand_activation _ _ _ _ _).mpr ⟨bitEq, rfl, readyOwner⟩

open Classical in
def clockWord (coordinate : CommitAttemptEvent graph) (owner : Player)
    (past : List app.EnvironmentEntry) : List Nat :=
  (past.filter (fun entry => decide (PhaseSeedScheduler.callback runtime leaks coordinate owner
    entry))).map (fun entry => PhaseSeedScheduler.elapsed runtime leaks coordinate entry.beforeView)

open Classical in
theorem clockWord_snoc (coordinate : CommitAttemptEvent graph) (owner : Player)
    (past : List app.EnvironmentEntry) (entry : app.EnvironmentEntry) :
    clockWord coordinate owner (past ++ [entry]) = clockWord coordinate owner past ++
      if PhaseSeedScheduler.callback runtime leaks coordinate owner entry then
        [PhaseSeedScheduler.elapsed runtime leaks coordinate entry.beforeView] else [] := by
  classical
  by_cases callback : PhaseSeedScheduler.callback runtime leaks coordinate owner entry <;>
    simp [clockWord, callback]

theorem word_clock_projection (coordinate : CommitAttemptEvent graph) (owner : Player)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) :
    (PhaseSeedScheduler.word runtime leaks coordinate owner past view).map Prod.fst =
      clockWord coordinate owner past := by
  classical
  induction past using List.reverseRecOn generalizing view with
  | nil => rfl
  | append_singleton past entry ih =>
      rw [PhaseSeedScheduler.word_snoc, List.map_append, ih, clockWord_snoc]
      by_cases callback : PhaseSeedScheduler.callback runtime leaks coordinate owner entry <;>
        simp [callback]

theorem original_clock_words (menu : app.ResponseMenu) (seeds : Seeds) :
    ∀ {state} (_trace : (menu.protocol initial horizon (family seeds)).Trace state),
      state.elim True (fun current => ∀ owner,
        current.execution.application.SeedRequest owner (originalCoordinate owner) →
        clockWord (originalCoordinate owner) owner current.execution.environmentRecall =
          originalClockWord owner (seeds.2 (originalAddress owner))
            current.execution.environmentRecall.length) := by
  classical
  intro state trace
  induction trace with
  | start => trivial
  | @extend source target prior joint legal reached ih =>
      let targetTrace := prior.extend joint legal reached
      have kept : TracePrefix prior targetTrace := by
        change TracePrefix prior (prior.extend joint legal reached)
        exact .extend .refl joint legal reached
      change target ∈ (app.transition initial horizon (family seeds) source joint).support
        at reached
      cases source with
      | none =>
          obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
          rw [initial_eq_pure, PMF.mem_support_pure_iff] at supported
          subst state
          intro owner _request
          rfl
      | some current =>
          rcases current with ⟨remaining, active, execution⟩
          cases active with
          | some actor =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              intro owner request
              have before := original_binding_request_of_prefix menu seeds
                _ _ prior targetTrace kept
                owner request
              rw [app.respond_environmentRecall]
              exact ih owner before
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ := Set.mem_iUnion₂.mp
                    (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  intro owner request
                  have before := original_binding_request_of_prefix menu seeds _ _ prior targetTrace
                    kept owner request
                  have original : execution.application.attempt = originalAttempt := before.1.symm
                  have raw := menu.toRawTrace initial horizon (family seeds) prior
                  have valid := raw_native_valid (family seeds) _ raw
                  have publicRequest := (PhaseRuntimeState.requests_publicView _ valid owner
                    (originalCoordinate owner)).mpr before
                  have ownReady : ready owner (bindingEvent owner)
                      (execution.observeEnvironment app) = true := by
                    change decide (PhaseRuntimeState.requests execution.application.publicView owner
                      ⟨execution.application.attempt, bindingEvent owner⟩) = true
                    rw [original, decide_eq_true_eq]
                    exact publicRequest
                  have chosen : command = originalCommand seeds execution.environmentRecall.length
                      execution.environmentRecall (execution.observeEnvironment app) :=
                    ((PMF.mem_support_pure_iff _ _).mp selected).trans
                      (choose_original seeds _ _ original)
                  have callback : PhaseSeedScheduler.callback runtime leaks
                      (originalCoordinate owner) owner ⟨execution.observeEnvironment app, command⟩ ↔
                      execution.environmentRecall.length ∈
                        originalTurns owner (seeds.2 (originalAddress owner)) := by
                    have activation := original_command_activation seeds owner
                      execution.environmentRecall.length execution.environmentRecall
                      (execution.observeEnvironment app) ownReady
                    constructor
                    · intro actual
                      exact activation.mp (chosen.symm.trans actual.1)
                    · intro occurs
                      exact ⟨chosen.trans (activation.mpr occurs), publicRequest⟩
                  have binding : bindingEvent owner = aliceBinding ∨
                      bindingEvent owner = bobBinding := by
                    fin_cases owner
                    · exact Or.inl rfl
                    · exact Or.inr rfl
                  have stamp := original_timer (family seeds) _ raw original (bindingEvent owner)
                    binding before.2.2.1.1
                  have elapsed : PhaseSeedScheduler.elapsed runtime leaks (originalCoordinate owner)
                      (execution.observeEnvironment app) =
                        originalClock execution.environmentRecall.length := by
                    change execution.application.current.native.clock -
                      (execution.application.current.native.activatedAt (bindingEvent owner)).getD
                        execution.application.current.native.clock = _
                    rw [stamp, Option.getD_some, Nat.sub_zero,
                      original_clock_index seeds _ raw original]
                  rw [app.environmentStep_environmentRecall execution next command supported,
                    clockWord_snoc, List.length_append, List.length_singleton, originalClockWord,
                    ih owner before]
                  by_cases occurs : execution.environmentRecall.length ∈
                      originalTurns owner (seeds.2 (originalAddress owner))
                  · rw [ite_eq_left (callback.mpr occurs), ite_eq_left occurs, elapsed]
                  · rw [ite_eq_right (fun active => occurs (callback.mp active)),
                      ite_eq_right occurs]

private theorem active_clockWord (menu : app.ResponseMenu) (seeds : Seeds) (current : app.Control)
    (trace : (menu.protocol initial horizon (family seeds)).Trace (some current))
    (owner : Player) (active : current.actor = some owner)
    (coordinate : CommitAttemptEvent graph)
    (request : current.execution.application.SeedRequest owner coordinate) :
    PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner
      (current.execution.recall owner) (current.execution.observe app owner) =
        clockWord coordinate owner current.execution.environmentRecall := by
  classical
  rcases current with ⟨remaining, acting, execution⟩
  cases active
  obtain ⟨before, _word, _selected, moved, input⟩ :=
    PhaseSeedScheduler.active_informationInput_of_trace runtime leaks menu initial horizon
      (family seeds) remaining owner execution trace coordinate
  have application : execution.application = before.application := by
    obtain ⟨updated, reached, rfl⟩ := PMF.support_map .. ▸ moved
    obtain ⟨sample, _supported, rfl⟩ := PMF.support_map .. ▸ reached
    rfl
  have entries := app.environmentStep_environmentRecall before execution (.activate owner) moved
  have valid := raw_native_valid (family seeds) _
    (menu.toRawTrace initial horizon (family seeds) trace)
  have publicRequest := (PhaseRuntimeState.requests_publicView _ valid owner coordinate).mpr request
  rw [application] at publicRequest
  calc
    PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner (execution.recall owner)
        (execution.observe app owner) =
        (PhaseSeedScheduler.localInput runtime leaks coordinate owner before.environmentRecall
          (before.observeEnvironment app)).activationClocks ++
        [(PhaseSeedScheduler.localInput runtime leaks coordinate owner before.environmentRecall
          (before.observeEnvironment app)).elapsed] :=
      congrArg (fun query : PhaseSeedInput graph => query.activationClocks ++ [query.elapsed])
        input.symm
    _ = clockWord coordinate owner before.environmentRecall ++
        [PhaseSeedScheduler.elapsed runtime leaks coordinate (before.observeEnvironment app)] := by
      simp only [PhaseSeedScheduler.localInput_word, word_clock_projection]
    _ = clockWord coordinate owner execution.environmentRecall := by
      have callback : PhaseSeedScheduler.callback runtime leaks coordinate owner
          ⟨before.observeEnvironment app, .activate owner⟩ := ⟨rfl, publicRequest⟩
      rw [entries, clockWord_snoc, ite_eq_left callback]

/-- Every actual original callback reads a prefix of its owner's fixed local
clock calendar. The original private seed changes placement within a clock,
while full physical observations and all arbitrary menu-supported responses remain. -/
theorem original_service_clocks_prefix (menu : app.ResponseMenu)
    (seeds : Seeds) (current : app.Control)
    (trace : (menu.protocol initial horizon (family seeds)).Trace (some current))
    (owner : Player) (active : current.actor = some owner)
    (request : current.execution.application.SeedRequest owner (originalCoordinate owner)) :
    PhaseSeedScheduler.serviceClocks runtime leaks (originalCoordinate owner) owner
      (current.execution.recall owner) (current.execution.observe app owner) <+:
        if owner = alice then [0, 2, 3] else [0, 4, 5] := by
  rw [active_clockWord menu seeds current trace owner active (originalCoordinate owner) request,
    original_clock_words menu seeds trace owner request]
  have bound : current.execution.environmentRecall.length ≤ 22 := by
    by_contra late
    exact original_attempt_retired seeds current
      (menu.toRawTrace initial horizon (family seeds) trace) (by omega) request.1.symm
  generalize bitEq : seeds.2 (originalAddress owner) = bit
  generalize countEq : current.execution.environmentRecall.length = count at bound ⊢
  interval_cases count <;> fin_cases owner <;> cases bit <;> decide

end Vegas.Examples.CommitSeedSignalling
