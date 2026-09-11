/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies

/-! # Fixed environment-command sequences -/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]

/-- Execute fixed environment commands by folding the ordinary environment
policy step. This is notation for the existing runner semantics. -/
def runEnvironmentCommands (app : MessageApplication Principal) :
    List app.EnvironmentPolicyCommand → app.PolicyExecution → FinDist app.PolicyExecution
  | [], execution => FinDist.pure execution
  | command :: rest, execution =>
      (app.environmentPolicyStep execution command).bind
        (runEnvironmentCommands app rest)

/-- Fixed environment-command sequences do not change any principal history. -/
theorem runEnvironmentCommands_principalHistory
    (app : MessageApplication Principal) (commands : List app.EnvironmentPolicyCommand)
    (execution next : app.PolicyExecution)
    (hnext : next ∈ (app.runEnvironmentCommands commands execution).support)
    (who : Principal) :
    next.principalHistory who = execution.principalHistory who := by
  induction commands generalizing execution with
  | nil =>
      simp only [runEnvironmentCommands, FinDist.mem_support_pure] at hnext
      subst next
      rfl
  | cons command rest ih =>
      simp only [runEnvironmentCommands, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      exact (ih middle hnext).trans
        (congrFun (app.environmentStep_principalHistory execution command middle hmiddle) who)

/-- A native environment policy which supplies the indexed fixed command at
each actual environment-history coordinate executes exactly the command fold.
Application environment steps may themselves be probabilistic. -/
theorem runPolicies_environmentCommands
    (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (commands : List app.EnvironmentPolicyCommand) (execution : app.PolicyExecution)
    (hpolicy : ∀ index command history view,
      commands[index]? = some command →
      history.length = execution.environmentHistory.length + index →
      environment history view = FinDist.pure command) :
    app.runPolicies players environment
        (List.replicate commands.length Invocation.environment) execution =
      app.runEnvironmentCommands commands execution := by
  induction commands generalizing execution with
  | nil => rfl
  | cons first rest ih =>
      have hfirst := hpolicy 0 first execution.environmentHistory
        (State.environmentView app execution.native) (by simp) (by omega)
      simp only [List.length_cons, List.replicate_succ, runPolicies, invoke, hfirst,
        FinDist.pure_bind, runEnvironmentCommands]
      apply FinDist.bind_congr
      intro next hnext
      apply ih next
      intro index command history view hcommand hlength
      apply hpolicy (index + 1) command history view
      · simpa only [List.getElem?_cons_zero, List.getElem?_cons_succ] using hcommand
      · have hstepLength : next.environmentHistory.length =
            execution.environmentHistory.length + 1 := by
          simp only [environmentPolicyStep, FinDist.support_bind, Set.mem_iUnion] at hnext
          obtain ⟨advanced, _, hnext⟩ := hnext
          simp only [FinDist.mem_support_pure] at hnext
          subst next
          simp
        rw [hstepLength] at hlength
        omega

end Interaction.MessageApplication

/-- info: 'Interaction.MessageApplication.runPolicies_environmentCommands'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.runPolicies_environmentCommands
