/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies
import Interaction.MessageApplicationLaws
import GameTheoryExtensions.Math.Probability.FinDist

/-! # Native support refinement for message-application policies -/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} (app : MessageApplication Principal)

/-- An action selected by a player invocation is recorded in every supported
successor, even if it leaves the application state unchanged. -/
theorem playerStep_action_mem [DecidableEq Principal]
    (who : Principal) (execution : app.PolicyExecution) (command : app.PlayerCommand)
    (action : app.Action) (haction : PlayerCommand.toAction app who command = some action)
    (next : app.PolicyExecution) (hnext : next ∈ (app.playerStep who execution command).support) :
    action ∈ next.nativeTrace := by
  simp only [playerStep, advance, haction, FinDist.bind_bind, FinDist.pure_bind,
    FinDist.support_bind, Set.mem_iUnion, FinDist.mem_support_pure] at hnext
  obtain ⟨_, _, rfl⟩ := hnext
  simp

private theorem advance_support [DecidableEq Principal]
    (execution : app.PolicyExecution) (action : Option app.Action)
    (advanced : app.State × List app.Action)
    (hadvanced : advanced ∈ (app.advance execution action).support) :
    ∃ suffix, advanced.2 = execution.nativeTrace ++ suffix ∧
      advanced.1 ∈ (app.run suffix execution.native).support := by
  cases action with
  | none =>
      simp only [advance, FinDist.mem_support_pure] at hadvanced
      subst advanced
      exact ⟨[], by simp⟩
  | some action =>
      simp only [advance, FinDist.support_bind, Set.mem_iUnion] at hadvanced
      rcases hadvanced with ⟨next, hnext, hadvanced⟩
      simp only [FinDist.mem_support_pure] at hadvanced
      subst advanced
      refine ⟨[action], rfl, ?_⟩
      simp only [run_cons, run_nil, FinDist.support_bind, Set.mem_iUnion]
      exact ⟨next, hnext, FinDist.mem_support_pure.mpr rfl⟩

/-- A player step appends exactly a supported native action suffix. -/
theorem playerStep_native_support [DecidableEq Principal]
    (who : Principal) (execution : app.PolicyExecution) (command : app.PlayerCommand)
    (next : app.PolicyExecution)
    (hnext : next ∈ (app.playerStep who execution command).support) :
    ∃ suffix, next.nativeTrace = execution.nativeTrace ++ suffix ∧
      next.native ∈ (app.run suffix execution.native).support := by
  simp only [playerStep, FinDist.support_bind, Set.mem_iUnion] at hnext
  rcases hnext with ⟨advanced, hadvanced, hnext⟩
  simp only [FinDist.mem_support_pure] at hnext
  subst next
  exact advance_support app execution _ advanced hadvanced

/-- An environment step appends exactly a supported native action suffix. -/
theorem environmentStep_native_support [DecidableEq Principal]
    (execution : app.PolicyExecution) (command : app.EnvironmentPolicyCommand)
    (next : app.PolicyExecution)
    (hnext : next ∈ (app.environmentPolicyStep execution command).support) :
    ∃ suffix, next.nativeTrace = execution.nativeTrace ++ suffix ∧
      next.native ∈ (app.run suffix execution.native).support := by
  simp only [environmentPolicyStep, FinDist.support_bind, Set.mem_iUnion] at hnext
  rcases hnext with ⟨advanced, hadvanced, hnext⟩
  simp only [FinDist.mem_support_pure] at hnext
  subst next
  exact advance_support app execution _ advanced hadvanced

/-- A supported policy invocation either waits or performs one supported
native action. The witness comes from the selected player's or environment's
command, and does not identify separate invocations with the same effect. -/
theorem invoke_native_step [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (execution next : app.PolicyExecution) (invocation : @Invocation Principal)
    (hnext : next ∈ (app.invoke players environment execution invocation).support) :
    next.native = execution.native ∨
      ∃ action, next.native ∈ (app.step execution.native action).support := by
  have hadvance (action : Option app.Action) (advanced : app.State × List app.Action)
      (hadvanced : advanced ∈ (app.advance execution action).support) :
      advanced.1 = execution.native ∨
        ∃ action, advanced.1 ∈ (app.step execution.native action).support := by
    cases action with
    | none =>
        simp only [advance, FinDist.mem_support_pure] at hadvanced
        subst advanced
        exact Or.inl rfl
    | some action =>
        simp only [advance, FinDist.support_bind, Set.mem_iUnion,
          FinDist.mem_support_pure] at hadvanced
        obtain ⟨state, hstate, rfl⟩ := hadvanced
        exact Or.inr ⟨action, hstate⟩
  cases invocation with
  | player who =>
      simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨command, _, hstep⟩ := hnext
      simp only [playerStep, FinDist.support_bind, Set.mem_iUnion,
        FinDist.mem_support_pure] at hstep
      obtain ⟨advanced, hadvanced, rfl⟩ := hstep
      exact hadvance _ advanced hadvanced
  | environment =>
      simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨command, _, hstep⟩ := hnext
      simp only [environmentPolicyStep, FinDist.support_bind, Set.mem_iUnion,
        FinDist.mem_support_pure] at hstep
      obtain ⟨advanced, hadvanced, rfl⟩ := hstep
      exact hadvance _ advanced hadvanced

/-- A policy invocation appends exactly a supported native action suffix. -/
theorem invoke_native_support [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (execution next : app.PolicyExecution) (invocation : @Invocation Principal)
    (hnext : next ∈ (app.invoke players environment execution invocation).support) :
    ∃ suffix, next.nativeTrace = execution.nativeTrace ++ suffix ∧
      next.native ∈ (app.run suffix execution.native).support := by
  cases invocation with
  | player who =>
      simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      rcases hnext with ⟨command, _, hstep⟩
      exact playerStep_native_support app who execution command next hstep
  | environment =>
      simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      rcases hnext with ⟨command, _, hstep⟩
      exact environmentStep_native_support app execution command next hstep

/-- Every supported policy outcome is supported by native execution of exactly
the action suffix appended to its proof-facing trace. -/
theorem runPolicies_native_support [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution next : app.PolicyExecution)
    (hnext : next ∈ (app.runPolicies players environment schedule execution).support) :
    ∃ suffix, next.nativeTrace = execution.nativeTrace ++ suffix ∧
      next.native ∈ (app.run suffix execution.native).support := by
  induction schedule generalizing execution with
  | nil =>
      simp only [runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact ⟨[], by simp⟩
  | cons invocation rest ih =>
      simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      rcases hnext with ⟨middle, hmiddle, hnext⟩
      rcases invoke_native_support app players environment execution middle invocation hmiddle with
        ⟨first, hfirstTrace, hfirstRun⟩
      rcases ih middle hnext with ⟨second, hsecondTrace, hsecondRun⟩
      refine ⟨first ++ second, ?_, ?_⟩
      · rw [hsecondTrace, hfirstTrace, List.append_assoc]
      · rw [app.run_append, FinDist.support_bind]
        simp only [Set.mem_iUnion]
        exact ⟨middle.native, hfirstRun, hsecondRun⟩

/-- From the canonical empty policy execution, the recorded native trace is
itself a native execution witnessing every supported outcome. -/
theorem runPolicies_initial_native_support [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (initial : app.State)
    (next : app.PolicyExecution)
    (hnext : next ∈ (app.runPolicies players environment schedule
      (PolicyExecution.initial app initial)).support) :
    next.native ∈ (app.run next.nativeTrace initial).support := by
  rcases runPolicies_native_support app players environment schedule
      (PolicyExecution.initial app initial) next hnext with ⟨suffix, htrace, hrun⟩
  simp only [PolicyExecution.initial, List.nil_append] at htrace
  rwa [htrace]

/-- Any application invariant preserved by the native hooks holds throughout
every supported policy run from an invariant initial application state. -/
theorem runPolicies_application_invariant [DecidableEq Principal]
    (invariant : app.Application → Prop)
    (hprivate : ∀ application who command, invariant application →
      invariant (app.privateStep application who command))
    (hsubmit : ∀ application who payload, invariant application →
      invariant (app.submitStep application who payload))
    (hhandler : ∀ application message next, invariant application →
      app.handle application message = some next → invariant next)
    (henvironment : ∀ application command next, invariant application →
      next ∈ (app.environmentStep application command).support → invariant next)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution next : app.PolicyExecution)
    (hinitial : invariant execution.native.application)
    (hnext : next ∈ (app.runPolicies players environment schedule execution).support) :
    invariant next.native.application := by
  obtain ⟨actions, _, hrun⟩ :=
    runPolicies_native_support app players environment schedule execution next hnext
  exact app.run_application_invariant invariant hprivate hsubmit hhandler henvironment
    execution.native next.native actions hinitial hrun

/-- Native application invariants hold from canonical policy initialization. -/
theorem runPolicies_initial_application_invariant [DecidableEq Principal]
    (invariant : app.Application → Prop)
    (hprivate : ∀ application who command, invariant application →
      invariant (app.privateStep application who command))
    (hsubmit : ∀ application who payload, invariant application →
      invariant (app.submitStep application who payload))
    (hhandler : ∀ application message next, invariant application →
      app.handle application message = some next → invariant next)
    (henvironment : ∀ application command next, invariant application →
      next ∈ (app.environmentStep application command).support → invariant next)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (initial : app.State)
    (next : app.PolicyExecution) (hinitial : invariant initial.application)
    (hnext : next ∈ (app.runPolicies players environment schedule
      (PolicyExecution.initial app initial)).support) :
    invariant next.native.application := by
  exact app.runPolicies_application_invariant invariant hprivate hsubmit hhandler henvironment
    players environment schedule (PolicyExecution.initial app initial) next hinitial hnext

/-- A support invariant preserved by each labelled invocation is preserved by
the policy run over the corresponding label plan.  Labels retain protocol
information which may be erased by their native invocation. -/
theorem runPolicies_map_invariant [DecidableEq Principal]
    {Label : Type*} (toInvocation : Label → @Invocation Principal)
    (invariant : app.PolicyExecution → Prop)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (preserve : ∀ label execution, invariant execution → ∀ next,
      next ∈ (app.invoke players environment execution (toInvocation label)).support →
        invariant next)
    (labels : List Label) (execution : app.PolicyExecution)
    (hinitial : invariant execution) :
    ∀ next, next ∈ (app.runPolicies players environment (labels.map toInvocation)
      execution).support → invariant next := by
  induction labels generalizing execution with
  | nil =>
      intro next supported
      simp only [List.map_nil, runPolicies, FinDist.mem_support_pure] at supported
      rwa [supported]
  | cons label rest ih =>
      intro next supported
      simp only [List.map_cons, runPolicies, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨middle, first, remaining⟩ := supported
      exact ih middle (preserve label execution hinitial middle first) next remaining

/-- Pointwise conservation at every actually reached labelled invocation
lifts to the complete finite policy run.  The residual law is defined only on
the invariant, and all compositions use support evidence; no off-support
fallback outcome is introduced. -/
theorem runPolicies_map_bindOnSupport_conservation [DecidableEq Principal]
    {Label Outcome : Type*} (toInvocation : Label → @Invocation Principal)
    (plan : List Label) (invariant : app.PolicyExecution → Prop)
    (residual : ∀ execution, invariant execution → FinDist Outcome)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (initial : app.PolicyExecution) (hinitial : invariant initial)
    (preserve : ∀ label execution, invariant execution → ∀ next,
      next ∈ (app.invoke players environment execution (toInvocation label)).support →
        invariant next)
    (conserve : ∀ before label after, plan = before ++ label :: after →
      ∀ execution, execution ∈ (app.runPolicies players environment
          (before.map toInvocation) initial).support →
        ∀ hexecution : invariant execution,
          (app.invoke players environment execution (toInvocation label)).bindOnSupport
              (fun next supported => residual next
                (preserve label execution hexecution next supported)) =
            residual execution hexecution) :
    (app.runPolicies players environment (plan.map toInvocation) initial).bindOnSupport
        (fun next supported => residual next
          (app.runPolicies_map_invariant toInvocation invariant players environment preserve
            plan initial hinitial next supported)) =
      residual initial hinitial := by
  have go : ∀ before after, plan = before ++ after →
      ∀ execution, execution ∈ (app.runPolicies players environment
          (before.map toInvocation) initial).support →
        ∀ hexecution : invariant execution,
          (app.runPolicies players environment (after.map toInvocation)
              execution).bindOnSupport
              (fun next supported => residual next
                (app.runPolicies_map_invariant toInvocation invariant players environment
                  preserve after execution hexecution next supported)) =
            residual execution hexecution := by
    intro before after split execution reached hexecution
    induction after generalizing before execution with
    | nil =>
        change (FinDist.pure execution).bindOnSupport _ = _
        rw [FinDist.pure_bindOnSupport]
    | cons label rest ih =>
        let stepLaw := app.invoke players environment execution (toInvocation label)
        let restLaw := app.runPolicies players environment (rest.map toInvocation)
        have totalPreserved : ∀ next ∈ (stepLaw.bind restLaw).support, invariant next := by
          intro next nextMem
          simp only [FinDist.support_bind, Set.mem_iUnion] at nextMem
          obtain ⟨middle, middleMem, restMem⟩ := nextMem
          exact app.runPolicies_map_invariant toInvocation invariant players environment
            preserve rest middle (preserve label execution hexecution middle middleMem)
            next restMem
        have normalized :
            (app.runPolicies players environment ((label :: rest).map toInvocation)
              execution).bindOnSupport
                (fun next supported => residual next
                  (app.runPolicies_map_invariant toInvocation invariant players environment
                    preserve (label :: rest) execution hexecution next supported)) =
              (stepLaw.bind restLaw).bindOnSupport fun next supported =>
                residual next (totalPreserved next supported) := by
          apply FinDist.bindOnSupport_congr_measure rfl
          intro next _ _
          congr
        rw [normalized]
        rw [FinDist.bind_bindOnSupport_assoc]
        calc
          _ = (app.invoke players environment execution
                (toInvocation label)).bindOnSupport
              (fun middle supported => residual middle
                (preserve label execution hexecution middle supported)) := by
              apply FinDist.bindOnSupport_congr
              intro middle middleMem
              apply ih (before ++ [label])
              · simpa [List.append_assoc] using split
              · simp only [List.map_append, app.runPolicies_append,
                  FinDist.support_bind, Set.mem_iUnion]
                exact ⟨execution, reached, by
                  simpa [runPolicies] using middleMem⟩
          _ = residual execution hexecution :=
            conserve before label rest split execution reached hexecution
  exact go [] plan (by simp) initial (by simp [runPolicies]) hinitial

private theorem advance_action_property [DecidableEq Principal]
    (property : app.Action → Prop) (execution : app.PolicyExecution)
    (action : Option app.Action) (advanced : app.State × List app.Action)
    (hinitial : ∀ action ∈ execution.nativeTrace, property action)
    (hcommand : ∀ emitted, action = some emitted → property emitted)
    (hadvanced : advanced ∈ (app.advance execution action).support) :
    ∀ action ∈ advanced.2, property action := by
  cases action with
  | none =>
      simp only [advance, FinDist.mem_support_pure] at hadvanced
      subst advanced
      exact hinitial
  | some action =>
      simp only [advance, FinDist.support_bind, Set.mem_iUnion] at hadvanced
      obtain ⟨next, _, hadvanced⟩ := hadvanced
      simp only [FinDist.mem_support_pure] at hadvanced
      subst advanced
      intro emitted hemitted
      rcases List.mem_append.mp hemitted with hprior | hnew
      · exact hinitial emitted hprior
      · have heq := List.mem_singleton.mp hnew
        exact heq ▸ hcommand action rfl

/-- A property of all commands admitted by the policies holds for every
recorded native action. Application transitions may remain randomized. -/
theorem runPolicies_action_property [DecidableEq Principal]
    (property : app.Action → Prop)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (hplayers : ∀ who history view command, command ∈ (players who history view).support →
      ∀ action, PlayerCommand.toAction app who command = some action → property action)
    (henvironment : ∀ history view command, command ∈ (environment history view).support →
      ∀ action, EnvironmentPolicyCommand.toAction app command = some action → property action)
    (schedule : List (@Invocation Principal)) (execution next : app.PolicyExecution)
    (hinitial : ∀ action ∈ execution.nativeTrace, property action)
    (hnext : next ∈ (app.runPolicies players environment schedule execution).support) :
    ∀ action ∈ next.nativeTrace, property action := by
  induction schedule generalizing execution with
  | nil =>
      simp only [runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact hinitial
  | cons invocation rest ih =>
      simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      apply ih middle ?_ hnext
      cases invocation with
      | player who =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, hcommand, hstep⟩ := hmiddle
          simp only [playerStep, FinDist.support_bind, Set.mem_iUnion] at hstep
          obtain ⟨advanced, hadvanced, hstep⟩ := hstep
          simp only [FinDist.mem_support_pure] at hstep
          subst middle
          exact advance_action_property app property execution _ advanced hinitial
            (hplayers who _ _ command hcommand) hadvanced
      | environment =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, hcommand, hstep⟩ := hmiddle
          simp only [environmentPolicyStep, FinDist.support_bind, Set.mem_iUnion] at hstep
          obtain ⟨advanced, hadvanced, hstep⟩ := hstep
          simp only [FinDist.mem_support_pure] at hstep
          subst middle
          exact advance_action_property app property execution _ advanced hinitial
            (henvironment _ _ command hcommand) hadvanced

end Interaction.MessageApplication
