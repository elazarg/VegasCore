/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedRelayResolution
import Interaction.MessageApplicationEnvironmentPhases

/-! # Reserved expiry service for windowed applications

A service round advances the public clock beyond the active response window,
invokes a named permissionless relay, then includes its latest submission.
These are ordinary policies and invocations of the shared message runner.
Application readiness and fallback availability remain code-specific facts.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

def expiryAdvance (runtime : WindowedApplication P L) (state : State P L) : State P L :=
  match state.active with
  | none => state
  | some activation =>
      { state with
        base := state.base.advance (activation.since + runtime.windowOf activation.key + 1) }

def expiryRelay (runtime : WindowedApplication P L) : runtime.application.PlayerPolicy :=
  runtime.relayWhenWaiting (fun _ _ => FinDist.pure .wait)

/-- Even-numbered environment turns advance the active window; odd turns
reserve inclusion for the relay's latest actual envelope. -/
def expiryService (runtime : WindowedApplication P L) (who : P) :
    runtime.application.EnvironmentPolicy := fun history view =>
  if history.length % 2 = 0 then
    match view.application.2 with
    | none => FinDist.pure .wait
    | some activation => FinDist.pure (.application (.advance
        (activation.since + runtime.windowOf activation.key + 1)))
  else runtime.application.includeLatestFrom who history view

def expiryCycle (who : P) : List (@Invocation P) :=
  [.environment, .player who, .environment]

omit [DecidableEq P] in
theorem expiryAdvance_consistent (runtime : WindowedApplication P L) (state : State P L)
    (hstate : runtime.Consistent state) : runtime.Consistent (runtime.expiryAdvance state) := by
  cases hactive : state.active with
  | none => simpa only [expiryAdvance, hactive] using hstate
  | some activation =>
    simp only [expiryAdvance, hactive]
    refine ⟨?_, fun current hcurrent =>
      Nat.le_trans (hstate.2 current ?_) (Nat.le_max_left _ _)⟩
    · simpa only [hactive, ApplicationImage.activeAddress?, ApplicationImage.State.advance]
        using hstate.1
    · simpa only [hactive] using hcurrent

omit [DecidableEq P] in
theorem expiryAdvance_overdue (runtime : WindowedApplication P L) (state : State P L)
    (activation : Activation Nat) (hactive : state.active = some activation) :
    (runtime.expiryAdvance state).active = some activation ∧
      activation.since + runtime.windowOf activation.key <
        (runtime.expiryAdvance state).base.memory.clock := by
  simp only [expiryAdvance, hactive, ApplicationImage.State.advance]
  exact ⟨trivial, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)⟩

/-- One actual clock/relay/inclusion round realizes an enabled expiry handler.
The premise describes the handler after clock advancement, not service or
completion of any run. Freshness permits unrelated traffic in the pool. -/
theorem expiryCycle_accepts (runtime : WindowedApplication P L)
    (players : P → runtime.application.PlayerPolicy) (who : P)
    (hrelay : players who = runtime.expiryRelay)
    (execution : runtime.application.PolicyExecution)
    (heven : execution.environmentHistory.length % 2 = 0)
    (activation : Activation Nat) (hactive : execution.native.application.active = some activation)
    (payload : ApplicationImage.Payload P L) (next : State P L)
    (hdue : runtime.dueExpiry?
      ((runtime.expiryAdvance execution.native.application).base.memory, some activation) =
        some payload)
    (hfresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none)
    (hhandle : runtime.handle (runtime.expiryAdvance execution.native.application)
      ⟨(who, execution.native.pool.nextSerial who), payload⟩ = some next) :
    (runtime.application.runPolicies players (runtime.expiryService who)
      (expiryCycle who) execution).map (fun out => out.native.application) = FinDist.pure next := by
  let clock := activation.since + runtime.windowOf activation.key + 1
  let ticked : runtime.application.PolicyExecution :=
    { execution with
      native := { execution.native with
        application := runtime.expiryAdvance execution.native.application }
      environmentHistory := execution.environmentHistory ++
        [⟨State.environmentView runtime.application execution.native,
          .application (.advance clock)⟩]
      nativeTrace := execution.nativeTrace ++ [.environment (.advance clock)] }
  have htick : runtime.application.invoke players (runtime.expiryService who) execution
      .environment = FinDist.pure ticked := by
    simp only [MessageApplication.invoke, expiryService, State.environmentView, heven,
      ↓reduceIte, application, hactive, FinDist.pure_bind, environmentPolicyStep,
      MessageApplication.advance, EnvironmentPolicyCommand.toAction, MessageApplication.step,
      FinDist.map_pure, ApplicationImage.State.advance, environmentStep]
    simp only [ticked, expiryAdvance, hactive, clock, State.environmentView, application,
      ApplicationImage.State.advance]
  have hodd : ticked.environmentHistory.length % 2 = 1 := by
    simp only [ticked, List.length_append, List.length_singleton]
    omega
  have hservice : runtime.application.runPolicies players (runtime.expiryService who)
      [.player who, .environment] ticked = runtime.application.runPolicies players
        (runtime.application.includeLatestFrom who) [.player who, .environment] ticked := by
    apply runtime.application.runPolicies_environment_congr
    intro history view hlo hhi
    have hlength : history.length = ticked.environmentHistory.length := by
      simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
        Bool.false_eq_true, ↓reduceIte] at hhi
      omega
    simp only [expiryService, hlength, hodd, Nat.one_ne_zero, ↓reduceIte]
  have hsubmit : players who (ticked.principalHistory who)
      (State.observe runtime.application ticked.native who) = FinDist.pure (.submit payload) := by
    rw [hrelay]
    apply runtime.relayWhenWaiting_pure_wait _ _ _ payload rfl
    simpa only [ticked, State.observe, application, expiryAdvance, hactive] using hdue
  have hphase := runtime.application.submit_include_accepts players who payload ticked next
    hsubmit hfresh hhandle
  have hprojection := congrArg
    (fun law : FinDist (State P L × List (Message P (ApplicationImage.Payload P L)) ×
        List (MessageId P × Bool)) => law.map Prod.fst) hphase
  simp only [FinDist.map_comp, Function.comp_def, FinDist.map_pure] at hprojection
  change ((runtime.application.invoke players (runtime.expiryService who) execution
    .environment).bind (runtime.application.runPolicies players (runtime.expiryService who)
      [.player who, .environment])).map (fun out => out.native.application) = _
  rw [htick, FinDist.pure_bind, hservice]
  exact hprojection

private theorem includePending_inactive (runtime : WindowedApplication P L)
    (state : runtime.application.State) (hactive : state.application.active = none)
    (id : MessageId P) :
    (runtime.application.includePending state id).application = state.application := by
  cases hlookup : state.pool.lookup id with
  | none => rw [runtime.application.includePending_missing state id hlookup]
  | some message =>
    have hreject : runtime.application.handle state.application message = none := by
      simp only [application, handle, hactive, Option.bind_eq_bind, Option.bind_none]
    exact (runtime.application.includePending_reject_observations state id message
      hlookup hreject).1

/-- The expiry service leaves an inactive application unchanged. It may still
record a rejected replay of an earlier relay envelope in the public ledger. -/
theorem expiryCycle_inactive (runtime : WindowedApplication P L)
    (players : P → runtime.application.PlayerPolicy) (who : P)
    (hrelay : players who = runtime.expiryRelay)
    (execution : runtime.application.PolicyExecution)
    (heven : execution.environmentHistory.length % 2 = 0)
    (hactive : execution.native.application.active = none) :
    (runtime.application.runPolicies players (runtime.expiryService who)
      (expiryCycle who) execution).map (fun out => out.native.application) =
        FinDist.pure execution.native.application := by
  have hodd : (execution.environmentHistory.length + 1) % 2 ≠ 0 := by omega
  simp only [expiryCycle, MessageApplication.runPolicies, MessageApplication.invoke,
    expiryService, State.environmentView, application, heven, ↓reduceIte, hactive,
    FinDist.pure_bind, MessageApplication.environmentStep_wait, hrelay, expiryRelay,
    relayWhenWaiting, State.observe, dueExpiry?, Option.bind_eq_bind, Option.bind_none,
    FinDist.map_pure, relayCommand, MessageApplication.playerStep_wait,
    List.length_append, List.length_singleton, hodd, MessageApplication.includeLatestFrom]
  cases hserial : execution.native.pool.nextSerial who with
  | zero =>
    simp [MessageApplication.latestSubmissionCommand, State.environmentView, hserial,
      MessageApplication.environmentStep_wait]
  | succ serial =>
    simp only [MessageApplication.latestSubmissionCommand, hserial]
    split
    · simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
        EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.pure_bind, FinDist.map_pure]
      exact congrArg FinDist.pure
        (runtime.includePending_inactive execution.native hactive (who, serial))
    · simp [MessageApplication.environmentStep_wait]

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.expiryCycle_accepts' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.expiryCycle_accepts

/-- info: 'Vegas.WindowedApplication.expiryCycle_inactive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.expiryCycle_inactive
