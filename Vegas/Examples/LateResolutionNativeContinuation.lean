/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateResolutionNativeInformation
import Interaction.ReactiveResponseEvaluation

/-! # Late resolution play has no later strategic response

After the second owner response the concrete public service only includes,
ticks or expires. Its actual remaining execution law is independent of every
future player policy.
-/

noncomputable section

namespace Vegas.LateResolutionService

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory.Math.Probability

theorem late_stage_passive (stage : Nat) (late : 6 ≤ stage) (view : app.EnvironmentView) :
    (stageCommand stage view).actor? app = none := by
  by_cases high : 10 ≤ stage
  · obtain ⟨extra, equal⟩ := Nat.exists_eq_add_of_le high
    have shifted : stage = extra + 10 := by omega
    rw [shifted]
    rfl
  · have low : stage ≤ 9 := by omega
    interval_cases stage
    all_goals first
      | omega
      | rfl
      | (change (latestWithhold view).actor? app = none; unfold latestWithhold; split <;> rfl)

theorem late_round_policy_independent (players : Player → app.Policy)
    (execution : app.Execution) (late : 6 ≤ execution.environmentRecall.length) :
    app.round scheduler players execution =
      app.round scheduler (fun _ => app.silentPolicy) execution := by
  unfold ReactiveApplication.round scheduler
  rw [PMF.pure_bind, PMF.pure_bind]
  unfold ReactiveApplication.dispatch
  rw [late_stage_passive _ late]
  rfl

theorem late_rounds_policy_independent (players : Player → app.Policy) (count : Nat)
    (execution : app.Execution) (late : 6 ≤ execution.environmentRecall.length) :
    app.runRounds scheduler players count execution =
      app.runRounds scheduler (fun _ => app.silentPolicy) count execution := by
  induction count generalizing execution with
  | zero => rfl
  | succ count ih =>
      rw [ReactiveApplication.runRounds, ReactiveApplication.runRounds,
        late_round_policy_independent players execution late]
      apply bind_congr_on_support _
      intro middle supported
      obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      have appended := app.dispatch_environmentRecall (fun _ => app.silentPolicy) command
        execution middle moved
      have later : 6 ≤ middle.environmentRecall.length := by
        rw [appended, List.length_append, List.length_singleton]
        omega
      exact ih middle later

/-- Actual native terminal play from the late input first draws its available
response, then executes the same passive physical suffix. Arbitrary other
information-site policies remain in the native profile. -/
theorem late_native_run_state (bounds : MessageBounds nativeGraph)
    (profile : ∀ who, (nativeModel bounds).BehavioralPolicy who)
    (history : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).History)
    (execution : app.Execution) (current : history.state = some ⟨4, some owner, execution⟩)
    (position : execution.environmentRecall.length = 6) :
    ((nativeModel bounds).runBehavioralFrom profile 21 history).map
      GameTheory.Protocol.ExecutionProtocol.History.state =
    ((profile owner (some (execution.recall owner, execution.observe app owner))).map
      Subtype.val).bind (fun action =>
        (app.runRounds scheduler (fun _ => app.silentPolicy) 4
          (execution.respond app owner (action.getD ⟨none⟩))).map app.finished) := by
  rw [(nativeMenu bounds).run_eq_finish (initialLaw setup) horizon scheduler profile 21 history
    (by rw [current]; change (2 * 4 + 1 : Nat) ≤ 21; decide), current]
  let players := (nativeMenu bounds).decodeProfile (initialLaw setup) horizon scheduler profile
  change ((app.invoke players owner execution).bind
    (app.runRounds scheduler players 4)).map app.finished = _
  have response : players owner (execution.recall owner) (execution.observe app owner) =
      (profile owner (some (execution.recall owner, execution.observe app owner))).map
        (fun choice => choice.val.getD ⟨none⟩) := by
    simp only [players, ReactiveApplication.ResponseMenu.decodeProfile,
      ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
      PMF.map_comp]
    rfl
  rw [ReactiveApplication.invoke, response]
  simp only [PMF.map_bind, PMF.bind_map, Function.comp_def]
  apply bind_congr_on_support _
  intro action _
  rw [late_rounds_policy_independent players 4
    (execution.respond app owner (action.val.getD ⟨none⟩))
    (by rw [app.respond_environmentRecall, position])]

theorem late_native_response_value (bounds : MessageBounds nativeGraph)
    (profile : ∀ who, (nativeModel bounds).BehavioralPolicy who)
    (history : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).History)
    (execution : app.Execution) (current : history.state = some ⟨4, some owner, execution⟩)
    (position : execution.environmentRecall.length = 6) (response : app.Action)
    (chosen : (profile owner (some (execution.recall owner, execution.observe app owner))).map
      Subtype.val = PMF.pure (some response))
    (payoff : app.ProtocolState → ℝ) :
    expect ((nativeModel bounds).runBehavioralFrom profile 21 history)
      (fun final => payoff final.state) =
    expect ((app.runRounds scheduler (fun _ => app.silentPolicy) 4
      (execution.respond app owner response)).map app.finished) payoff := by
  calc
    _ = expect (((nativeModel bounds).runBehavioralFrom profile 21 history).map
        GameTheory.Protocol.ExecutionProtocol.History.state) payoff :=
      (expect_map (fun final :
        ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).History => final.state)
        _ payoff).symm
    _ = _ := by
      rw [late_native_run_state bounds profile history execution current position,
        chosen, PMF.pure_bind, Option.getD_some]

instance : leaks.FiniteSupport where
  support_finite := fun _ _ => by change (PMF.pure ∅).support.Finite; simp

instance : app.FiniteNature (initialLaw setup) scheduler where
  toFiniteEnvironment := inferInstance
  initial_finite := by
    change ((PMF.pure sourceInitial).map _).support.Finite
    rw [PMF.pure_map]
    simp
  scheduler_finite := fun _ _ => by
    change (PMF.pure _).support.Finite
    simp

def lateSite (bounds : MessageBounds nativeGraph) (execution : app.Execution)
    (trace : ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨4, some owner, execution⟩)) : (nativeModel bounds).InformationSite owner :=
  ⟨some (execution.recall owner, execution.observe app owner),
    late_decision_site bounds execution trace⟩

end Vegas.LateResolutionService
