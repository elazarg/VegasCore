/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageApplicationPolicyTrace

/-! # Actual policy checkpoints for newly established facts

A command that is the only way to establish a fact must have been available
at a genuine policy input before the fact first holds. The checkpoint retains
the entire native snapshot, including pending messages and local histories.
It is a proof readout and does not add an invocation or player observation.
Selection uses command support at a snapshot, not the scheduled invocation
there. Relating its probability to a later actual call requires a separate law.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

variable {Principal : Type*} [DecidableEq Principal] (app : MessageApplication Principal)

/-- Lift a native private-command provenance fact to the policy input at
which that owner chose the command. Environment invocations cannot forge it. -/
theorem invoke_privateCommand_origin
    (reached : app.State → Prop) (owner : Principal) (request : app.PrivateCommand)
    (horigin : ∀ initial next action, next ∈ (app.step initial action).support →
      reached next → reached initial ∨ action = .privateCommand owner request)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (initial next : app.PolicyExecution) (invocation : @Invocation Principal)
    (hnext : next ∈ (app.invoke players environment initial invocation).support)
    (hnew : reached next.native) :
    reached initial.native ∨ .privateCommand request ∈
      (players owner (initial.principalHistory owner)
        (State.observe app initial.native owner)).support := by
  have hadvance (action : Option app.Action) (advanced : app.State × List app.Action)
      (hadvanced : advanced ∈ (app.advance initial action).support)
      (hnew : reached advanced.1) :
      reached initial.native ∨ action = some (.privateCommand owner request) := by
    cases action with
    | none =>
        simp only [advance, FinDist.mem_support_pure] at hadvanced
        subst advanced
        exact Or.inl hnew
    | some action =>
        simp only [advance, FinDist.support_bind, Set.mem_iUnion,
          FinDist.mem_support_pure] at hadvanced
        obtain ⟨state, hstate, rfl⟩ := hadvanced
        exact (horigin initial.native state action hstate hnew).imp_right (congrArg some)
  cases invocation with
  | player who =>
      simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨command, hcommand, hstep⟩ := hnext
      simp only [playerStep, FinDist.support_bind, Set.mem_iUnion,
        FinDist.mem_support_pure] at hstep
      obtain ⟨advanced, hadvanced, rfl⟩ := hstep
      rcases hadvance _ advanced hadvanced hnew with hprior | ha
      · exact Or.inl hprior
      · right
        cases command with
        | privateCommand actual =>
            simp only [PlayerCommand.toAction, Option.some.injEq,
              MessageInterface.Action.privateCommand.injEq] at ha
            obtain ⟨rfl, rfl⟩ := ha
            exact hcommand
        | submit | replay | wait =>
            simp only [PlayerCommand.toAction, Option.some.injEq] at ha
            cases ha
  | environment =>
      simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨command, _, hstep⟩ := hnext
      simp only [environmentPolicyStep, FinDist.support_bind, Set.mem_iUnion,
        FinDist.mem_support_pure] at hstep
      obtain ⟨advanced, hadvanced, rfl⟩ := hstep
      rcases hadvance _ advanced hadvanced hnew with hprior | ha
      · exact Or.inl hprior
      · cases command <;>
          simp only [EnvironmentPolicyCommand.toAction, Option.some.injEq] at ha <;> cases ha

/-- The earliest pre-cutoff snapshot at which the owner's policy supports
the queried command. This is defined even when no matching snapshot exists. -/
def commandCheckpoint (players : Principal → app.PlayerPolicy) (trace : app.PolicyTrace)
    (stop : app.PolicyExecution → Bool) (owner : Principal) (command : app.PlayerCommand) :
    app.PolicyExecution := by
  classical
  exact (trace.prefixThrough stop).firstRelease fun execution =>
    !stop execution && decide (command ∈
      (players owner (execution.principalHistory owner)
        (State.observe app execution.native owner)).support)

/-- If a fact absent initially is present at the cutoff, and establishing it
requires the queried command, its checkpoint is strictly before that cutoff.
Policies may be randomized and may use their entire declared observations. -/
theorem commandCheckpoint_selected_of_new_fact
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (reached : app.PolicyExecution → Prop) (owner : Principal) (command : app.PlayerCommand)
    (horigin : ∀ initial next invocation,
      next ∈ (app.invoke players environment initial invocation).support →
      reached next → reached initial ∨ command ∈
        (players owner (initial.principalHistory owner)
          (State.observe app initial.native owner)).support)
    (schedule : List (@Invocation Principal)) (initial : app.PolicyExecution)
    (trace : app.PolicyTrace)
    (htrace : trace ∈ (app.tracePolicies players environment schedule initial).support)
    (stop : app.PolicyExecution → Bool) (hinitial : ¬reached initial)
    (hfinal : reached (trace.prefixThrough stop).last) :
    let selected := app.commandCheckpoint players trace stop owner command
    stop selected = false ∧ command ∈
      (players owner (selected.principalHistory owner)
        (State.observe app selected.native owner)).support := by
  classical
  let select (execution : app.PolicyExecution) : Bool :=
    !stop execution && decide (command ∈
      (players owner (execution.principalHistory owner)
        (State.observe app execution.native owner)).support)
  have hselected : select ((trace.prefixThrough stop).firstRelease select) = true := by
    induction schedule generalizing initial trace with
    | nil =>
        simp only [tracePolicies, FinDist.mem_support_pure] at htrace
        subst trace
        exact False.elim (hinitial hfinal)
    | cons invocation rest ih =>
        simp only [tracePolicies, FinDist.support_bind, Set.mem_iUnion,
          FinDist.support_map, Set.mem_image] at htrace
        obtain ⟨next, hnext, tail, htail, rfl⟩ := htrace
        by_cases hstop : stop initial = true
        · simp only [PolicyTrace.prefixThrough, if_pos hstop, PolicyTrace.last] at hfinal
          exact False.elim (hinitial hfinal)
        · by_cases hselect : select initial = true
          · simpa only [PolicyTrace.prefixThrough, if_neg hstop, PolicyTrace.firstRelease,
              if_pos hselect] using hselect
          · have hnextAbsent : ¬reached next := by
              intro hnew
              rcases horigin initial next invocation hnext hnew with hprior | hcommand
              · exact hinitial hprior
              · apply hselect
                simp only [select, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
                  decide_eq_true_eq]
                exact ⟨Bool.eq_false_iff.mpr hstop, hcommand⟩
            have hlast : reached (tail.prefixThrough stop).last := by
              simpa only [PolicyTrace.prefixThrough, if_neg hstop, PolicyTrace.last] using hfinal
            simpa only [PolicyTrace.prefixThrough, if_neg hstop, PolicyTrace.firstRelease,
              if_neg hselect] using ih next tail htail hnextAbsent hlast
  simpa only [select, commandCheckpoint, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_true_eq] using hselected

end Interaction.MessageApplication

/-- info: 'Interaction.MessageApplication.commandCheckpoint_selected_of_new_fact'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.commandCheckpoint_selected_of_new_fact
