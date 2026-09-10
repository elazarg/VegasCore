/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedExpiryService

/-! # Stability after windowed expiry completion

Repeated reserved expiry rounds preserve an already inactive native
application. The shared runner still retains every real policy and service
history entry; only the native application projection is constant.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

def expiryCycles (who : P) : Nat → List (@Invocation P)
  | 0 => []
  | n + 1 => expiryCycle who ++ expiryCycles who n

/-- Once the generated application has no active instruction, any number of
actual clock/relay/inclusion rounds preserves that native application. -/
theorem expiryCycles_inactive (runtime : WindowedApplication P L)
    (players : P → runtime.application.PlayerPolicy) (who : P)
    (hrelay : players who = runtime.expiryRelay)
    (n : Nat) (execution : runtime.application.PolicyExecution)
    (heven : execution.environmentHistory.length % 2 = 0)
    (hactive : execution.native.application.active = none) :
    (runtime.application.runPolicies players (runtime.expiryService who)
      (expiryCycles who n) execution).map (fun out => out.native.application) =
        FinDist.pure execution.native.application := by
  induction n generalizing execution with
  | zero => simp [expiryCycles, MessageApplication.runPolicies]
  | succ n ih =>
      rw [expiryCycles, MessageApplication.runPolicies_append, FinDist.map_bind]
      have hcycle := runtime.expiryCycle_inactive players who hrelay execution heven hactive
      calc
        _ = (runtime.application.runPolicies players (runtime.expiryService who)
            (expiryCycle who) execution).bind
              (fun middle => FinDist.pure middle.native.application) := by
          apply FinDist.bind_congr
          intro middle hmiddle
          have hprojection : middle.native.application = execution.native.application := by
            have hmem : middle.native.application ∈
                ((runtime.application.runPolicies players (runtime.expiryService who)
                  (expiryCycle who) execution).map
                    (fun out => out.native.application)).support := by
              rw [FinDist.support_map]
              exact ⟨middle, hmiddle, rfl⟩
            rw [hcycle, FinDist.mem_support_pure] at hmem
            exact hmem
          have hlength := runtime.application.runPolicies_environmentHistory_length
            players (runtime.expiryService who) (expiryCycle who) execution middle hmiddle
          have hmiddleEven : middle.environmentHistory.length % 2 = 0 := by
            simp only [expiryCycle, List.countP_cons, List.countP_nil,
              Invocation.isEnvironment, Bool.false_eq_true, ↓reduceIte] at hlength
            omega
          have hmiddleActive : middle.native.application.active = none := by
            rw [hprojection]
            exact hactive
          exact ih middle hmiddleEven hmiddleActive
        _ = (runtime.application.runPolicies players (runtime.expiryService who)
            (expiryCycle who) execution).map (fun out => out.native.application) := by
          rw [FinDist.map_eq_bind]
        _ = FinDist.pure execution.native.application := hcycle

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.expiryCycles_inactive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.expiryCycles_inactive
