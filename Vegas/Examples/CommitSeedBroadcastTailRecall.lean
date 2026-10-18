/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastCalendar
import Interaction.ReactiveRecordedResponse
import GameTheoryExtensions.Protocol.TracePrefix

/-! # No repeated own response for a continuation service coordinate -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem environment_prefix (menu : app.ResponseMenu)
    (seeds : Seeds) (before after : app.Control)
    (beforeTrace : (menu.protocol initial horizon (family seeds)).Trace (some before))
    (afterTrace : (menu.protocol initial horizon (family seeds)).Trace (some after))
    (retained : TracePrefix beforeTrace afterTrace) :
    before.execution.environmentRecall <+: after.execution.environmentRecall := by
  have along : ∀ {target}
      {trace : (menu.protocol initial horizon (family seeds)).Trace target},
      TracePrefix beforeTrace trace → ∃ next : app.Control, target = some next ∧
        before.execution.environmentRecall <+: next.execution.environmentRecall := by
    intro target trace kept
    induction kept with
    | refl => exact ⟨before, rfl, List.prefix_refl _⟩
    | @extend source target prior kept joint legal reached ih =>
        obtain ⟨middle, rfl, earlier⟩ := ih
        change target ∈ (app.transition initial horizon (family seeds) (some middle)
          joint).support at reached
        rcases middle with ⟨remaining, active, execution⟩
        cases active with
        | some owner =>
            cases (PMF.mem_support_pure_iff _ _).mp reached
            refine ⟨_, rfl, ?_⟩
            rw [app.respond_environmentRecall]
            exact earlier
        | none =>
            cases remaining with
            | zero =>
                cases (PMF.mem_support_pure_iff _ _).mp reached
                exact ⟨_, rfl, earlier⟩
            | succ remaining =>
                obtain ⟨command, _selected, moved⟩ := Set.mem_iUnion₂.mp
                  (PMF.support_bind .. ▸ reached)
                obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                refine ⟨_, rfl, earlier.trans ?_⟩
                rw [app.environmentStep_environmentRecall execution next command supported]
                exact List.prefix_append _ _
  obtain ⟨next, equal, keptEnv⟩ := along retained
  cases Option.some.inj equal
  exact keptEnv

private theorem active_callback_index (menu : app.ResponseMenu)
    (seeds : Seeds) (current : app.Control)
    (trace : (menu.protocol initial horizon (family seeds)).Trace (some current))
    (owner : Player) (active : current.actor = some owner)
    (coordinate : CommitAttemptEvent graph)
    (request : PhaseRuntimeState.requests
      (current.execution.observe app owner).application.2 owner coordinate) :
    ∃ index, current.execution.environmentRecall.length = index + 1 ∧
      ∃ bounded : index < current.execution.environmentRecall.length,
        PhaseSeedScheduler.callback runtime leaks coordinate owner
          current.execution.environmentRecall[index] := by
  rcases current with ⟨remaining, acting, execution⟩
  cases active
  obtain ⟨before, _word, _selected, reached, _input⟩ :=
    PhaseSeedScheduler.active_informationInput_of_trace runtime leaks menu initial horizon
      (family seeds) remaining owner execution trace coordinate
  have application : execution.application = before.application := by
    obtain ⟨updated, moved, rfl⟩ := PMF.support_map .. ▸ reached
    obtain ⟨seen, _supported, rfl⟩ := PMF.support_map .. ▸ moved
    rfl
  have entries := app.environmentStep_environmentRecall before execution (.activate owner) reached
  have requested : PhaseRuntimeState.requests
      (before.observeEnvironment app).application owner coordinate := by
    change PhaseRuntimeState.requests before.application.publicView owner coordinate
    change PhaseRuntimeState.requests execution.application.publicView owner coordinate at request
    rwa [application] at request
  refine ⟨before.environmentRecall.length, ?_, ?_⟩
  · rw [entries, List.length_append, List.length_singleton]
  · have bound : before.environmentRecall.length < execution.environmentRecall.length := by
      rw [entries, List.length_append, List.length_singleton]
      omega
    refine ⟨bound, ?_⟩
    have selected : execution.environmentRecall[before.environmentRecall.length]? =
        some ⟨before.observeEnvironment app, .activate owner⟩ := by
      rw [entries, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    have actualEntry := Option.some.inj ((List.getElem?_eq_getElem bound).symm.trans selected)
    rw [actualEntry]
    exact ⟨rfl, requested⟩

private theorem prefix_callback (first last : List app.EnvironmentEntry)
    (retainedEnv : first <+: last) (coordinate : CommitAttemptEvent graph) (owner : Player)
    (index : Nat) (bounded : index < first.length)
    (callback : PhaseSeedScheduler.callback runtime leaks coordinate owner first[index]) :
    ∃ bound : index < last.length,
      PhaseSeedScheduler.callback runtime leaks coordinate owner last[index] := by
  have bound : index < last.length := lt_of_lt_of_le bounded retainedEnv.length_le
  refine ⟨bound, ?_⟩
  exact retainedEnv.getElem bounded ▸ callback

/-- Two distinct entries of actual own recall cannot both be requested
responses for the same continuation coordinate. Arbitrary other owners' raw
actions and every retired namespace remain in the original physical history. -/
theorem tail_recalled_callbacks_no_repeat (menu : app.ResponseMenu)
    (silence : ∀ owner past view,
      (⟨none⟩ : app.Action) ∈ menu.actions owner past view) (seeds : Seeds) (current : app.Control)
    (trace : (menu.protocol initial horizon (family seeds)).Trace (some current))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (retired : coordinate.attempt ≠ originalAttempt)
    (earlier middle later : List app.PlayerEntry) (first second : app.PlayerEntry)
    (recalled : current.execution.recall owner = earlier ++ first :: (middle ++ second :: later))
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner coordinate)
    (secondRequest : PhaseRuntimeState.requests second.beforeView.application.2 owner coordinate) :
    False := by
  obtain ⟨left, right, leftTrace, rightTrace, leftRight, rightLast, leftActive, rightActive,
    leftRecall, rightRecall, leftView, rightView, _firstAvailable, _secondAvailable⟩ :=
      menu.recorded_responses_at initial horizon (family seeds) current trace owner
        earlier first middle second later recalled
  have leftRequest : PhaseRuntimeState.requests
      (left.execution.observe app owner).application.2 owner coordinate := leftView ▸ firstRequest
  have rightRequest : PhaseRuntimeState.requests
      (right.execution.observe app owner).application.2 owner coordinate :=
    rightView ▸ secondRequest
  obtain ⟨firstIndex, firstLength, firstBound, firstCallback⟩ :=
    active_callback_index menu seeds left leftTrace owner leftActive coordinate leftRequest
  obtain ⟨secondIndex, secondLength, secondBound, secondCallback⟩ :=
    active_callback_index menu seeds right rightTrace owner rightActive coordinate rightRequest
  have leftPrefix := environment_prefix menu seeds left right leftTrace rightTrace leftRight
  have rightPrefix := environment_prefix menu seeds right current rightTrace trace rightLast
  obtain ⟨firstFinalBound, firstFinalCallback⟩ := prefix_callback _ _
    (leftPrefix.trans rightPrefix) coordinate owner firstIndex firstBound firstCallback
  obtain ⟨secondFinalBound, secondFinalCallback⟩ := prefix_callback _ _ rightPrefix coordinate
    owner secondIndex secondBound secondCallback
  have sameIndex := tail_callback_index_unique menu silence seeds
    current trace coordinate owner retired
    firstIndex secondIndex firstFinalBound secondFinalBound firstFinalCallback secondFinalCallback
  have sameLength : left.execution.environmentRecall.length =
      right.execution.environmentRecall.length := by omega
  have sameEnvironment : left.execution.environmentRecall =
      right.execution.environmentRecall := leftPrefix.eq_of_length sameLength
  have leftCount := app.response_count_history initial horizon (family seeds) left
    (menu.toRawTrace initial horizon (family seeds) leftTrace) owner
  have rightCount := app.response_count_history initial horizon (family seeds) right
    (menu.toRawTrace initial horizon (family seeds) rightTrace) owner
  have sameActivations : app.activationHistory left.execution =
      app.activationHistory right.execution := by
    unfold ReactiveApplication.activationHistory
    rw [sameEnvironment]
  rw [leftActive, ite_eq_left rfl, leftRecall] at leftCount
  rw [rightActive, ite_eq_left rfl, rightRecall, List.length_append, List.length_cons]
    at rightCount
  rw [sameActivations] at leftCount
  omega

end Vegas.Examples.CommitSeedBroadcast
