/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyLaws
import Interaction.MessagePoolFreshness

/-! # An immediate submission and inclusion opportunity

The named principal submits through its own policy capability. The environment
then selects that principal's latest pending envelope using only its public
view. This two-invocation service reserves an inclusion opportunity; it does
not assert fairness of an arbitrary environment or application acceptance.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]
variable (app : MessageApplication Principal)

/-- Select the sender's newest allocated identifier only when it is pending.
No payload or application validator is inspected. -/
def latestSubmissionCommand (who : Principal) (view : app.EnvironmentObservation) :
    app.EnvironmentPolicyCommand :=
  match view.pool.nextSerial who with
  | 0 => .wait
  | serial + 1 =>
      if (view.pool.lookup (who, serial)).isSome then .include (who, serial) else .wait

def includeLatestFrom (who : Principal) : app.EnvironmentPolicy :=
  fun _ view => FinDist.pure (app.latestSubmissionCommand who view)

/-- Selection either waits or requests inclusion of an existing identifier. -/
theorem latestSubmissionCommand_cases (who : Principal) (view : app.EnvironmentObservation) :
    app.latestSubmissionCommand who view = .wait ∨
      ∃ id, app.latestSubmissionCommand who view = .include id := by
  unfold latestSubmissionCommand
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl

/-- A fresh native submission supplies the exact envelope selected next.
The rest of the pending pool can contain arbitrary unrelated traffic. -/
theorem latestSubmissionCommand_after_submit (state : app.State)
    (who : Principal) (payload : app.Payload)
    (hfresh : state.pool.lookup (who, state.pool.nextSerial who) = none) :
    app.latestSubmissionCommand who
      (State.environmentView app
        { state with pool := (state.pool.submit who payload).2 }) =
      .include (who, state.pool.nextSerial who) := by
  have hlookup := state.pool.lookup_submit_fresh who payload hfresh
  simp only [latestSubmissionCommand, State.environmentView, MessagePool.submit,
    ↓reduceIte]
  change (if (((state.pool.submit who payload).2.lookup
    (who, state.pool.nextSerial who)).isSome) then _ else _) = _
  rw [hlookup]
  rfl

/-- The reserved opportunity retains the complete execution law, including
both sampled observations, each principal's real history, and the native trace.
The command premise concerns this invocation, not application acceptance. -/
theorem submit_include (players : Principal → app.PlayerPolicy)
    (who : Principal) (payload : app.Payload) (execution : app.PolicyExecution)
    (hsubmit : players who (execution.principalHistory who)
      (State.observe app execution.native who) = FinDist.pure (.submit payload))
    (hfresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none) :
    let submitted :=
      { execution.native with pool := (execution.native.pool.submit who payload).2 }
    let id := (who, execution.native.pool.nextSerial who)
    app.runPolicies players (app.includeLatestFrom who) [.player who, .environment] execution =
      FinDist.pure
        { native := app.includePending submitted id
          principalHistory := fun other =>
            if other = who then execution.principalHistory who ++
              [⟨State.observe app execution.native who, .submit payload⟩]
            else execution.principalHistory other
          environmentHistory := execution.environmentHistory ++
            [⟨State.environmentView app submitted, .include id⟩]
          nativeTrace := execution.nativeTrace ++ [.submit who payload, .include id] } := by
  dsimp only
  simp only [runPolicies, invoke, hsubmit, FinDist.pure_bind, playerStep, advance,
    PlayerCommand.toAction, step]
  simp only [FinDist.pure_bind, includeLatestFrom]
  rw [app.latestSubmissionCommand_after_submit execution.native who payload hfresh]
  simp only [FinDist.pure_bind, environmentPolicyStep, advance,
    EnvironmentPolicyCommand.toAction, step, List.append_assoc, List.cons_append,
    List.nil_append]

/-- Native-state projection of the actual two-invocation policy law. -/
theorem submit_include_native (players : Principal → app.PlayerPolicy)
    (who : Principal) (payload : app.Payload) (execution : app.PolicyExecution)
    (hsubmit : players who (execution.principalHistory who)
      (State.observe app execution.native who) = FinDist.pure (.submit payload))
    (hfresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none) :
    (app.runPolicies players (app.includeLatestFrom who)
      [.player who, .environment] execution).map MessageInterface.PolicyExecution.native =
      FinDist.pure (app.includePending
        { execution.native with pool := (execution.native.pool.submit who payload).2 }
        (who, execution.native.pool.nextSerial who)) := by
  rw [app.submit_include players who payload execution hsubmit hfresh]
  simp only [FinDist.map_pure]

/-- Acceptance during the reserved opportunity records the actual sender and
fresh serial in both the ledger and successful receipt. -/
theorem submit_include_accepts (players : Principal → app.PlayerPolicy)
    (who : Principal) (payload : app.Payload) (execution : app.PolicyExecution)
    (next : app.Application)
    (hsubmit : players who (execution.principalHistory who)
      (State.observe app execution.native who) = FinDist.pure (.submit payload))
    (hfresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none)
    (hhandle : app.handle execution.native.application
      ⟨(who, execution.native.pool.nextSerial who), payload⟩ = some next) :
    (app.runPolicies players (app.includeLatestFrom who)
      [.player who, .environment] execution).map (fun out =>
        (out.native.application, out.native.pool.ledger, out.native.receipts)) =
      FinDist.pure (next,
        execution.native.pool.ledger ++ [⟨(who, execution.native.pool.nextSerial who), payload⟩],
        execution.native.receipts ++ [((who, execution.native.pool.nextSerial who), true)]) := by
  have hlaw := app.submit_include_native players who payload execution hsubmit hfresh
  have hlookup := execution.native.pool.lookup_submit_fresh who payload hfresh
  have hincluded := app.includePending_accept
    { execution.native with pool := (execution.native.pool.submit who payload).2 }
    (who, execution.native.pool.nextSerial who) _ next hlookup hhandle
  have hledger := MessagePool.include_ledger_of_lookup
    (execution.native.pool.submit who payload).2
    (who, execution.native.pool.nextSerial who) _ hlookup
  rw [hincluded] at hlaw
  have hmapped := congrArg
    (fun law => law.map fun state : app.State =>
      (state.application, state.pool.ledger, state.receipts)) hlaw
  simp only [FinDist.map_comp, Function.comp_def, FinDist.map_pure] at hmapped
  rw [hledger] at hmapped
  exact hmapped

end Interaction.MessageApplication

/-- info: 'Interaction.MessageApplication.submit_include_accepts' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.submit_include_accepts
