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

/-- Repeated delivery of one selected identifier changes only recipient-local
inboxes and the recorded environment history. The statement permits repeated
recipients and unsuccessful deliveries. -/
theorem runEnvironmentCommands_deliver_frame
    (app : MessageApplication Principal) (recipients : List Principal)
    (id : MessageId Principal) (execution delivered : app.PolicyExecution)
    (hdelivered : delivered ∈ (app.runEnvironmentCommands
      (recipients.map fun recipient =>
        (MessageInterface.EnvironmentPolicyCommand.deliver recipient id)) execution).support) :
    delivered.native.application = execution.native.application ∧
      delivered.native.pool.pending = execution.native.pool.pending ∧
      delivered.native.pool.nextSerial = execution.native.pool.nextSerial ∧
      delivered.native.receipts = execution.native.receipts ∧
      delivered.principalHistory = execution.principalHistory ∧
      delivered.environmentHistory.length =
        execution.environmentHistory.length + recipients.length := by
  induction recipients generalizing execution with
  | nil =>
      simp only [List.map_nil, runEnvironmentCommands, FinDist.mem_support_pure] at hdelivered
      subst delivered
      exact ⟨rfl, rfl, rfl, rfl, rfl, by simp⟩
  | cons recipient rest ih =>
      simp only [List.map_cons, runEnvironmentCommands, FinDist.support_bind,
        Set.mem_iUnion] at hdelivered
      obtain ⟨middle, hmiddle, hdelivered⟩ := hdelivered
      have hmiddleNative : middle.native = { execution.native with
          pool := (execution.native.pool.deliver recipient id).state } := by
        have hstep := hmiddle
        simp only [environmentPolicyStep, advance,
          EnvironmentPolicyCommand.toAction, step, FinDist.pure_bind,
          FinDist.mem_support_pure] at hstep
        subst middle
        rfl
      obtain ⟨happlication, hpending, hserial, hreceipts, hprincipal, henvironment⟩ :=
        ih middle hdelivered
      refine ⟨happlication.trans ?_, hpending.trans ?_, hserial.trans ?_,
        hreceipts.trans ?_, hprincipal.trans ?_, ?_⟩
      · rw [hmiddleNative]
      · rw [hmiddleNative]
        exact MessagePool.deliver_preserves_pending execution.native.pool recipient id
      · rw [hmiddleNative]
        unfold MessagePool.deliver
        split <;> rfl
      · rw [hmiddleNative]
      · exact app.environmentStep_principalHistory execution (.deliver recipient id) middle
          hmiddle
      · rw [henvironment,
          app.environmentStep_history_length execution (.deliver recipient id) middle hmiddle,
          List.length_cons]
        omega

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

/-- info: 'Interaction.MessageApplication.runEnvironmentCommands_deliver_frame'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.runEnvironmentCommands_deliver_frame
