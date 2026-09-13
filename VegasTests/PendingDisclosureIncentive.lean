/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedTimeoutDisclosure
import Interaction.MessageApplicationEnvironmentCommands
import VegasTests.PendingTimeout

/-! # Selective withholding at a compiled pending-message checkpoint

Both values have been committed. Player zero's opening is delivered to player
one before inclusion. Player one either opens the value it already committed
or waits. The same environment first includes timely openings, then advances
the clock and includes a preexisting expiration request. Every tested branch
resolves through the actual timed policy runner.
-/

noncomputable section

namespace VegasTests.PendingDisclosureIncentive

open Interaction GameTheory.Math.Probability
open Interaction.MessageApplication
open VegasTests.PendingSource VegasTests.PendingExecution
open VegasTests.PendingTimeout

abbrev App := timed.messageApplication (Value := Value)

def checkpoint (left right : Value) : TimedState :=
  timed.run (commitPrefix left right)
    [.submit 0 (.protocol (.opening 2 (0, 0) left)), .deliver 1 (0, 1), .submit 0 .expire]

theorem checkpoint_events (left right : Value) :
    (checkpoint left right).application.events =
      [.accepted 0 (0, 0), .accepted 1 (1, 1)] :=
  commitPrefix_events left right

theorem checkpoint_locked (left right : Value) :
    SealedTimeout.LockedOpening timed 1 1 right (checkpoint left right).application := by
  apply SealedTimeout.LockedOpening.of_pending
  · fin_cases left <;> fin_cases right <;> rfl
  · fin_cases left <;> fin_cases right <;> rfl
  · intro claimed
    rw [checkpoint_events]
    simp

/-- The observed opening is still pending when the responding player acts. -/
theorem checkpoint_pending_opening (left right : Value) :
    (checkpoint left right).pool.inbox 1 =
        [⟨(0, 1), .protocol (.opening 2 (0, 0) left)⟩] ∧
      SealedProgram.openedValue? 2 (checkpoint left right).application.events = none := by
  fin_cases left <;> fin_cases right <;> exact ⟨rfl, rfl⟩

def response (stop : Value → Bool) (bound : Value) : App.PlayerPolicy := fun _ view =>
  match view.messages.inbox.head? with
  | some ⟨_, .protocol (.opening 2 (0, 0) observed)⟩ =>
      if stop observed then FinDist.pure .wait
      else FinDist.pure (.submit (.protocol (.opening 3 (1, 1) bound)))
  | _ => FinDist.pure .wait

def environment : App.EnvironmentPolicy := fun history _ =>
  FinDist.pure <| match history.length with
  | 0 => .include (0, 1)
  | 1 => .include (1, 1)
  | 2 => .application (ULift.up 11)
  | _ => .include (0, 2)

def schedule : List (@Invocation Player) :=
  [.player 1, .environment, .environment, .environment, .environment]

def law (left right : Value) (stop : Value → Bool) : FinDist App.PolicyExecution :=
  (App.policyGame environment schedule (timed.toSharedState (checkpoint left right))).play
    (fun _ => response stop right)

def result (left right : Value) (stops : Bool) : TimedState :=
  timed.run (checkpoint left right)
    ((if stops then [] else [.submit 1 (.protocol (.opening 3 (1, 1) right))]) ++
      [.include (0, 1), .include (1, 1), .advance 11, .include (0, 2)])

private theorem service_native (players : Player → App.PlayerPolicy)
    (execution : App.PolicyExecution) (hcount : execution.environmentHistory.length = 0) :
    (App.runPolicies players environment
      [.environment, .environment, .environment, .environment] execution).map
        MessageInterface.PolicyExecution.native =
      App.run [.include (0, 1), .include (1, 1), .environment (ULift.up 11), .include (0, 2)]
        execution.native := by
  let commands : List App.EnvironmentPolicyCommand :=
    [.include (0, 1), .include (1, 1), .application (ULift.up 11), .include (0, 2)]
  have hpolicy : ∀ index command history view,
      commands[index]? = some command →
      history.length = execution.environmentHistory.length + index →
      environment history view = FinDist.pure command := by
    intro index command history view hcommand hlength
    rw [hcount, Nat.zero_add] at hlength
    rcases index with _ | (_ | (_ | (_ | index)))
    all_goals simp only [commands, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, Option.some.injEq] at hcommand
    all_goals first | contradiction | subst command; simp [environment, hlength]
  change (App.runPolicies players environment
    (List.replicate commands.length .environment) execution).map _ = _
  rw [App.runPolicies_environmentCommands players environment commands execution hpolicy,
    App.runEnvironmentCommands_native]
  rfl

private theorem reaction_native (state : TimedState) (right : Value) (stops : Bool)
    (players : Player → App.PlayerPolicy)
    (hresponse : players 1 [] (State.observe App (timed.toSharedState state) 1) =
      FinDist.pure (if stops then .wait
        else .submit (.protocol (.opening 3 (1, 1) right)))) :
    ((App.policyGame environment schedule (timed.toSharedState state)).play players).map
        (fun execution => execution.native) =
      FinDist.pure (timed.toSharedState (timed.run state
        ((if stops then [] else [.submit 1 (.protocol (.opening 3 (1, 1) right))]) ++
          [.include (0, 1), .include (1, 1), .advance 11, .include (0, 2)]))) := by
  let start := PolicyExecution.initial App (timed.toSharedState state)
  let command : App.PlayerCommand := if stops then .wait
    else .submit (.protocol (.opening 3 (1, 1) right))
  change (App.runPolicies players environment
    (.player 1 :: [.environment, .environment, .environment, .environment]) start).map _ = _
  rw [runPolicies, invoke]
  change players 1 (start.principalHistory 1) (State.observe App start.native 1) =
    FinDist.pure command at hresponse
  rw [hresponse, FinDist.pure_bind, FinDist.map_bind]
  have hservice := fun next hnext => service_native players next
    (show next.environmentHistory.length = 0 from by
      rw [App.playerStep_environmentHistory 1 start command next hnext]
      rfl)
  rw [FinDist.bind_congr hservice]
  rw [← FinDist.bind_map MessageInterface.PolicyExecution.native, App.playerStep_native]
  cases stops
  · change (App.step (timed.toSharedState state)
      (.submit 1 (.protocol (.opening 3 (1, 1) right)))).bind _ = _
    rw [SealedTimeout.step_shared, FinDist.pure_bind, SealedTimeout.run_shared_actions]
    rfl
  · change (FinDist.pure (timed.toSharedState state)).bind _ = _
    rw [FinDist.pure_bind, SealedTimeout.run_shared_actions]
    rfl

theorem law_native (left right : Value) (stop : Value → Bool) :
    (law left right stop).map (fun execution => execution.native) =
      FinDist.pure (timed.toSharedState (result left right (stop left))) := by
  apply reaction_native
  simp only [response, State.observe, MessagePool.observe,
    SealedTimeout.toSharedState, (checkpoint_pending_opening left right).1, List.head?_cons]
  cases stop left <;> rfl

theorem result_resolution (left right : Value) (stops : Bool) :
    (result left right stops).application.resolution =
      if stops then .expired else .completed := by
  fin_cases left <;> fin_cases right <;> cases stops <;> rfl

theorem law_disclosure (left right : Value) (stop : Value → Bool) :
    (law left right stop).map (fun execution =>
      timed.disclosureResult execution.native.application.application) =
        FinDist.pure (if stop left then DisclosureResult.expired else .opened right) := by
  have h := congrArg (FinDist.map (fun state : App.State =>
    timed.disclosureResult state.application.application)) (law_native left right stop)
  rw [FinDist.map_comp, FinDist.map_pure] at h
  refine h.trans ?_
  cases hstop : stop left <;> fin_cases left <;> fin_cases right <;> rfl

theorem law_resolved (left right : Value) (stop : Value → Bool)
    (execution : App.PolicyExecution) (hmem : execution ∈ (law left right stop).support) :
    execution.native.application.application.resolution ≠ .pending := by
  have hnative : execution.native ∈
      ((law left right stop).map (fun execution => execution.native)).support := by
    rw [FinDist.support_map]
    exact ⟨execution, hmem, rfl⟩
  rw [law_native] at hnative
  have heq := FinDist.mem_support_pure.mp hnative
  rw [heq]
  change (result left right (stop left)).application.resolution ≠ .pending
  rw [result_resolution]
  cases stop left <;> decide

/-- The abstract arbitrary-policy bound applies to the checked compiler's
native checkpoint; both the lock and resolution obligations are discharged. -/
theorem disclosure_utility_bound (left right : Value) (stop : Value → Bool)
    (utility : DisclosureResult Value → ℝ) (margin : ℝ)
    (hmargin : utility .expired + margin ≤ utility (.opened right)) :
    ((law left right stop).map (fun execution => timed.disclosureResult
      execution.native.application.application)).expect utility +
        margin * ((law left right stop).map (fun execution => decide
          (execution.native.application.application.resolution = .expired))).prob true ≤
      utility (.opened right) :=
  SealedTimeout.resolved_policy_utility_bound timed (checkpoint left right) 1 1 right [0, 1]
    rfl (checkpoint_locked left right) (fun _ => response stop right) environment schedule
    (law_resolved left right stop) utility margin hmargin

def fairBit : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num) (FinDist.pure false) (FinDist.pure true)

/-- A matching payoff with the programmer's penalty for either explicit
nullable decline or expired disclosure. The opponent's value is already fixed. -/
def payoff (penalty : ℝ) (left : Bool) (outcome : DisclosureResult Value) : ℝ :=
  match outcome with
  | .unresolved => 0
  | .expired | .opened none => penalty
  | .opened (some right) => if left = right then 1 else -1

/-- Average over the two players' independent, precommitted random choices.
The subsequent policy sees the opponent's pending opening. -/
def expectedPayoff (penalty : ℝ) (stop : Bool → Value → Bool) : ℝ :=
  fairBit.expect fun left => fairBit.expect fun right =>
    ((law (some left) (some right) (stop right)).map (fun execution =>
      timed.disclosureResult execution.native.application.application)).expect (payoff penalty left)

theorem expectedPayoff_eq (penalty : ℝ) (stop : Bool → Value → Bool) :
    expectedPayoff penalty stop =
      ((if stop false (some false) then penalty else 1) +
        (if stop true (some false) then penalty else -1) +
        (if stop false (some true) then penalty else -1) +
        (if stop true (some true) then penalty else 1)) / 4 := by
  simp only [expectedPayoff, law_disclosure, FinDist.expect_pure]
  simp only [fairBit, FinDist.expect_mix, FinDist.expect_pure]
  cases stop false (some false) <;>
    cases stop true (some false) <;>
    cases stop false (some true) <;>
    cases stop true (some true) <;>
    simp [payoff] <;> ring

/-- All informed stopping rules are unprofitable exactly when expiration is
no better than the losing committed continuation. -/
theorem all_stopping_unprofitable_iff (penalty : ℝ) :
    (∀ stop : Bool → Value → Bool, expectedPayoff penalty stop ≤ 0) ↔ penalty ≤ -1 := by
  constructor
  · intro h
    have hselect := h (fun right observed => decide (observed ≠ some right))
    rw [expectedPayoff_eq] at hselect
    norm_num at hselect
    linarith
  · intro hpenalty stop
    rw [expectedPayoff_eq]
    have hwin (b : Bool) : (if b then penalty else (1 : ℝ)) ≤ 1 := by
      cases b
      · simp
      · simp only [↓reduceIte]
        linarith
    have hlose (b : Bool) : (if b then penalty else (-1 : ℝ)) ≤ -1 := by
      cases b <;> simp [hpenalty]
    have h₁ := hwin (stop false (some false))
    have h₂ := hlose (stop true (some false))
    have h₃ := hlose (stop false (some true))
    have h₄ := hwin (stop true (some true))
    linarith

/-- Always quitting is worse than continuing on average, yet selectively
withholding losing commitments is profitable under this weaker penalty. -/
theorem ex_ante_quit_comparison_insufficient :
    expectedPayoff (-1 / 2) (fun _ _ => true) = -1 / 2 ∧
      expectedPayoff (-1 / 2) (fun _ _ => false) = 0 ∧
      expectedPayoff (-1 / 2) (fun right observed => decide (observed ≠ some right)) = 1 / 4 := by
  simp only [expectedPayoff_eq]
  norm_num

end VegasTests.PendingDisclosureIncentive

/-- info: 'VegasTests.PendingDisclosureIncentive.disclosure_utility_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingDisclosureIncentive.disclosure_utility_bound

/-- info: 'VegasTests.PendingDisclosureIncentive.all_stopping_unprofitable_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingDisclosureIncentive.all_stopping_unprofitable_iff
