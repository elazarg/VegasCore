/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedPreparedPolicies
import Interaction.MessageApplicationProjection

/-! # Policy execution under the candidate-host embedding

The embedding preserves every visible component and the proof-facing action
trace. Its preparation premise is proved for generated source policies in the
compiler. It is not imposed on arbitrary candidate-host deviations.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

def candidateNative (runtime : SealedResolution Principal Value)
    (state : runtime.messageApplication.State) : runtime.candidateApplication.State :=
  ⟨candidateState state.application, state.pool, state.receipts⟩

def candidateAction (runtime : SealedResolution Principal Value) :
    runtime.messageApplication.Action → runtime.candidateApplication.Action
  | .privateCommand who command => .privateCommand who command
  | .submit who payload => .submit who payload
  | .replay who id => .replay who id
  | .deliver who id => .deliver who id
  | .include id => .include id
  | .environment command => .environment command

def candidateEnvironmentCommand (runtime : SealedResolution Principal Value) :
    runtime.messageApplication.EnvironmentPolicyCommand →
      runtime.candidateApplication.EnvironmentPolicyCommand
  | .deliver who id => .deliver who id
  | .include id => .include id
  | .application command => .application command
  | .wait => .wait

def registeredEnvironmentCommand (runtime : SealedResolution Principal Value) :
    runtime.candidateApplication.EnvironmentPolicyCommand →
      runtime.messageApplication.EnvironmentPolicyCommand
  | .deliver who id => .deliver who id
  | .include id => .include id
  | .application command => .application command
  | .wait => .wait

def candidateExecution (runtime : SealedResolution Principal Value)
    (execution : runtime.messageApplication.PolicyExecution) :
    runtime.candidateApplication.PolicyExecution where
  native := runtime.candidateNative execution.native
  principalHistory who := (execution.principalHistory who).map fun entry =>
    ⟨⟨entry.beforeView.messages, entry.beforeView.application, entry.beforeView.receipts⟩,
      entry.command⟩
  environmentHistory := execution.environmentHistory.map fun entry =>
    ⟨⟨entry.beforeView.pool, entry.beforeView.application, entry.beforeView.receipts⟩,
      runtime.candidateEnvironmentCommand entry.command⟩
  nativeTrace := execution.nativeTrace.map runtime.candidateAction

/-- Retype only the policy interface; the player sees exactly the same data. -/
def candidatePlayerPolicy (runtime : SealedResolution Principal Value)
    (policy : runtime.messageApplication.PlayerPolicy) :
    runtime.candidateApplication.PlayerPolicy :=
  fun history view => policy
    (history.map fun entry =>
      ⟨⟨entry.beforeView.messages, entry.beforeView.application, entry.beforeView.receipts⟩,
        entry.command⟩)
    ⟨view.messages, view.application, view.receipts⟩

/-- Transport an adaptive environment policy without changing its observations
or its selection of wire actions and clock commands. -/
def candidateEnvironmentPolicy (runtime : SealedResolution Principal Value)
    (policy : runtime.messageApplication.EnvironmentPolicy) :
    runtime.candidateApplication.EnvironmentPolicy :=
  fun history view => (policy
    (history.map fun entry =>
      ⟨⟨entry.beforeView.pool, entry.beforeView.application, entry.beforeView.receipts⟩,
        runtime.registeredEnvironmentCommand entry.command⟩)
    ⟨view.pool, view.application, view.receipts⟩).map runtime.candidateEnvironmentCommand

/-- Retyping environment policies excludes no candidate-host environment.
In particular, the honest execution law does not restrict adaptive scheduling
by requiring it to be the image of an environment policy. -/
theorem candidateEnvironmentPolicy_surjective (runtime : SealedResolution Principal Value) :
    Function.Surjective runtime.candidateEnvironmentPolicy := by
  intro environment
  refine ⟨fun history view => (environment
    (history.map fun entry =>
      ⟨⟨entry.beforeView.pool, entry.beforeView.application, entry.beforeView.receipts⟩,
        runtime.candidateEnvironmentCommand entry.command⟩)
    ⟨view.pool, view.application, view.receipts⟩).map runtime.registeredEnvironmentCommand, ?_⟩
  have hcommand : ∀ command : runtime.candidateApplication.EnvironmentPolicyCommand,
      runtime.candidateEnvironmentCommand
        (runtime.registeredEnvironmentCommand command) = command := by
    intro command
    cases command <;> rfl
  have hentry : ∀ entry : runtime.candidateApplication.EnvironmentEntry,
      (⟨⟨entry.beforeView.pool, entry.beforeView.application, entry.beforeView.receipts⟩,
        entry.command⟩ : runtime.candidateApplication.EnvironmentEntry) = entry := by
    intro ⟨⟨_, _, _⟩, _⟩
    rfl
  funext history view
  cases view
  simp only [candidateEnvironmentPolicy, List.map_map, FinDist.map_comp, Function.comp_def,
    hcommand, hentry, List.map_id_fun', id_eq]
  exact FinDist.map_id _

private theorem candidateNative_includePending (runtime : SealedResolution Principal Value)
    (execution : runtime.messageApplication.PolicyExecution)
    (h : PreparedExecution runtime execution) (id : MessageId Principal) :
    runtime.candidateApplication.includePending (runtime.candidateNative execution.native) id =
      runtime.candidateNative (runtime.messageApplication.includePending execution.native id) := by
  cases hlookup : execution.native.pool.lookup id with
  | none =>
      rw [runtime.messageApplication.includePending_missing _ _ hlookup,
        runtime.candidateApplication.includePending_missing _ _ hlookup]
  | some message =>
      have hmessage := h.messages.1 message (List.mem_of_find?_eq_some hlookup)
      have hhandler := runtime.candidateHandle_prepared execution.native.application
        h.accepted message hmessage
      cases hresult : runtime.handle execution.native.application message with
      | none =>
          rw [hresult, Option.map_none] at hhandler
          rw [runtime.messageApplication.includePending_reject _ _ _ hlookup hresult,
            runtime.candidateApplication.includePending_reject
              (runtime.candidateNative execution.native) id message hlookup hhandler]
          rfl
      | some next =>
          rw [hresult, Option.map_some] at hhandler
          rw [runtime.messageApplication.includePending_accept _ _ _ _ hlookup hresult,
            runtime.candidateApplication.includePending_accept
              (runtime.candidateNative execution.native) id message (candidateState next)
              hlookup hhandler]
          rfl

private theorem candidate_step (runtime : SealedResolution Principal Value)
    (execution : runtime.messageApplication.PolicyExecution)
    (h : PreparedExecution runtime execution) (action : runtime.messageApplication.Action) :
    runtime.candidateApplication.step (runtime.candidateNative execution.native)
        (runtime.candidateAction action) =
      (runtime.messageApplication.step execution.native action).map runtime.candidateNative := by
  cases action with
  | privateCommand who command =>
      simp only [candidateAction, MessageApplication.step, FinDist.map_pure]
      exact congrArg (fun service => FinDist.pure
        (⟨⟨service, execution.native.application.visible⟩,
          execution.native.pool, execution.native.receipts⟩ : runtime.candidateApplication.State))
        (execution.native.application.service.candidates_sealValue
          who command.down.1 command.down.2).symm
  | submit | replay | deliver =>
      simp only [candidateAction, MessageApplication.step, FinDist.map_pure]
      rfl
  | «include» id =>
      simp only [candidateAction, MessageApplication.step, FinDist.map_pure,
        runtime.candidateNative_includePending execution h id]
  | environment command =>
      simp only [candidateAction, MessageApplication.step, candidateApplication,
        messageApplication, FinDist.map_pure]
      rfl

private theorem candidate_advance (runtime : SealedResolution Principal Value)
    (execution : runtime.messageApplication.PolicyExecution)
    (h : PreparedExecution runtime execution) (action : Option runtime.messageApplication.Action) :
    runtime.candidateApplication.advance (runtime.candidateExecution execution)
        (action.map runtime.candidateAction) =
      (runtime.messageApplication.advance execution action).map
        (fun next => (runtime.candidateNative next.1, next.2.map runtime.candidateAction)) := by
  cases action with
  | none => simp [advance, candidateExecution]
  | some action =>
      simp only [Option.map_some, advance, candidateExecution, runtime.candidate_step execution h,
        FinDist.bind_map, FinDist.map_bind, FinDist.map_pure, List.map_append, List.map_singleton]

private theorem candidate_playerStep (runtime : SealedResolution Principal Value)
    (execution : runtime.messageApplication.PolicyExecution)
    (h : PreparedExecution runtime execution) (who : Principal)
    (command : runtime.messageApplication.PlayerCommand) :
    runtime.candidateApplication.playerStep who (runtime.candidateExecution execution) command =
      (runtime.messageApplication.playerStep who execution command).map
        runtime.candidateExecution := by
  have haction : PlayerCommand.toAction runtime.candidateApplication who command =
      (PlayerCommand.toAction runtime.messageApplication who command).map
        runtime.candidateAction := by cases command <;> rfl
  simp only [MessageApplication.playerStep, haction,
    runtime.candidate_advance execution h, FinDist.bind_map, FinDist.map_bind, FinDist.map_pure]
  congr 1
  funext next
  congr 1
  simp only [candidateExecution, State.observe, candidateNative, candidateState,
    candidateApplication, messageApplication]
  congr 1
  funext other
  by_cases hother : other = who <;> simp [hother]

theorem environmentPolicyStep_candidates (runtime : SealedResolution Principal Value)
    (execution : runtime.messageApplication.PolicyExecution)
    (h : PreparedExecution runtime execution)
    (command : runtime.messageApplication.EnvironmentPolicyCommand) :
    runtime.candidateApplication.environmentPolicyStep (runtime.candidateExecution execution)
        (runtime.candidateEnvironmentCommand command) =
      (runtime.messageApplication.environmentPolicyStep execution command).map
        runtime.candidateExecution := by
  have haction : EnvironmentPolicyCommand.toAction runtime.candidateApplication
        (runtime.candidateEnvironmentCommand command) =
      (EnvironmentPolicyCommand.toAction runtime.messageApplication command).map
        runtime.candidateAction := by cases command <;> rfl
  simp only [environmentPolicyStep, haction, runtime.candidate_advance execution h,
    FinDist.bind_map, FinDist.map_bind, FinDist.map_pure]
  congr 1
  funext next
  congr 1
  simp only [candidateExecution, State.environmentView, candidateNative, candidateState,
    candidateApplication, messageApplication, List.map_append, List.map_singleton]

private theorem candidate_invoke (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (execution : runtime.messageApplication.PolicyExecution)
    (h : PreparedExecution runtime execution) (invocation : @Invocation Principal) :
    runtime.candidateApplication.invoke
        (fun who => runtime.candidatePlayerPolicy (players who))
        (runtime.candidateEnvironmentPolicy environment) (runtime.candidateExecution execution)
        invocation =
      (runtime.messageApplication.invoke players environment execution invocation).map
        runtime.candidateExecution := by
  cases invocation with
  | player who =>
      have hentry : ∀ entry : runtime.messageApplication.PlayerEntry,
          (⟨⟨entry.beforeView.messages, entry.beforeView.application, entry.beforeView.receipts⟩,
            entry.command⟩ : runtime.messageApplication.PlayerEntry) = entry := by
        intro ⟨⟨_, _, _⟩, _⟩
        rfl
      simp only [invoke, candidatePlayerPolicy, candidateExecution, State.observe, candidateNative,
        candidateState, candidateApplication, messageApplication, List.map_map]
      simp only [Function.comp_def, hentry, List.map_id_fun', id_eq]
      rw [FinDist.map_bind]
      apply FinDist.bind_congr
      intro command _
      exact runtime.candidate_playerStep execution h who command
  | environment =>
      have hentry : ∀ entry : runtime.messageApplication.EnvironmentEntry,
          (⟨⟨entry.beforeView.pool, entry.beforeView.application, entry.beforeView.receipts⟩,
            entry.command⟩ : runtime.messageApplication.EnvironmentEntry) = entry := by
        intro ⟨⟨_, _, _⟩, _⟩
        rfl
      have hroundtrip : ∀ command : runtime.messageApplication.EnvironmentPolicyCommand,
          runtime.registeredEnvironmentCommand
            (runtime.candidateEnvironmentCommand command) = command := by
        intro command
        cases command <;> rfl
      simp only [invoke, candidateEnvironmentPolicy, candidateExecution, State.environmentView,
        candidateNative, candidateState, candidateApplication, messageApplication, List.map_map]
      simp only [Function.comp_def, hroundtrip, hentry, List.map_id_fun', id_eq]
      rw [FinDist.bind_map, FinDist.map_bind]
      apply FinDist.bind_congr
      intro command _
      exact runtime.environmentPolicyStep_candidates execution h command

/-- Exact complete finite execution law under the prepared-message discipline.
The equality retains private preparations, public observations, histories,
receipts and native traces. It places no fairness restriction on the scheduler. -/
theorem runPolicies_candidates (runtime : SealedResolution Principal Value)
    (players : Principal → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (hsubmit : ∀ execution who payload,
      RegistrationMemory runtime execution →
      .submit payload ∈ (players who (execution.principalHistory who)
        (State.observe _ execution.native who)).support →
      ∀ serial, SealedProgram.PreparedSubmission execution.native.application.service
        ⟨(who, serial), payload⟩)
    (schedule : List (@Invocation Principal))
    (execution : runtime.messageApplication.PolicyExecution)
    (h : PreparedExecution runtime execution) :
    (runtime.messageApplication.runPolicies players environment schedule execution).map
        runtime.candidateExecution =
      runtime.candidateApplication.runPolicies
        (fun who => runtime.candidatePlayerPolicy (players who))
        (runtime.candidateEnvironmentPolicy environment) schedule
        (runtime.candidateExecution execution) := by
  apply MessageApplication.runPolicies_map_of_invoke players environment _ _
    runtime.candidateExecution (PreparedExecution runtime) ?_ ?_ schedule execution h
  · intro current invocation next hcurrent hnext
    apply runtime.runPolicies_prepared players environment hsubmit [invocation]
      current next hcurrent
    simpa only [runPolicies, FinDist.bind_pure] using hnext
  · intro current invocation hcurrent
    exact (runtime.candidate_invoke players environment current hcurrent invocation).symm

end Interaction.SealedResolution
