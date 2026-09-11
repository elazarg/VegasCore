/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPolicyProvenance
import Vegas.Compile.WindowedBindingProvenance
import Vegas.Compile.WindowedBlockService
import Vegas.Compile.WindowedSourceSafety

/-! # Source binding provenance for block-gated windowed policies

The block schedule may pad a lifted source policy with waits and genuine expiry
submissions.  Those commands cannot imitate a binding submission, so the
existing source registration proof supplies the windowed provenance invariant.
This is only a preparation/frozen-snapshot result, not a source-kernel law.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

omit [DecidableEq P] in
/-- Every payload selected by the expiry relay is one of the explicit
deadline-dependent requests. -/
theorem dueExpiry?_deadlineDependent (runtime : WindowedApplication P L)
    (view : ApplicationImage.Memory P L × Option (Activation Nat))
    (payload : ApplicationImage.Payload P L)
    (hpayload : runtime.dueExpiry? view = some payload) :
    ¬payload.DeadlineIndependent := by
  obtain ⟨_, instruction, _, _, _, _, hexpiry⟩ :=
    runtime.dueExpiry?_some view payload hpayload
  cases instruction with
  | sample code => simp [ApplicationInstruction.expiryPayload?] at hexpiry
  | bind code =>
      simp only [ApplicationInstruction.expiryPayload?] at hexpiry
      split at hexpiry <;> try contradiction
      cases hexpiry
      simp [ApplicationImage.Payload.DeadlineIndependent]
  | publicChoice code =>
      simp only [ApplicationInstruction.expiryPayload?] at hexpiry
      split at hexpiry <;> try contradiction
      cases hexpiry
      simp [ApplicationImage.Payload.DeadlineIndependent]
  | conditional code =>
      cases hexpiry
      simp [ApplicationImage.Payload.DeadlineIndependent]

/-- Erasing a command supported by a block-gated policy yields either a
command supported by the underlying policy at the actual erased history/view,
or a wait/expiry padding command. -/
theorem blockPlayer_supported (runtime : WindowedApplication P L) (who : P)
    (base : runtime.image.orderedApplication.PlayerPolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View)
    (command : runtime.application.PlayerCommand)
    (hcommand : command ∈
      (runtime.blockPlayer who (runtime.liftPlayerPolicy base) history view).support) :
    runtime.erasePlayerCommand command ∈
        (base (history.map runtime.erasePlayerEntry) (runtime.eraseView view)).support ∨
      runtime.image.IdleOrExpiryCommand (runtime.erasePlayerCommand command) := by
  unfold blockPlayer at hcommand
  cases hindex : runtime.image.instructions[history.length / 3]? with
  | none =>
      simp only [hindex, FinDist.mem_support_pure] at hcommand
      subst command
      exact Or.inr (runtime.image.idleOrExpiryCommand_wait)
  | some instruction =>
      simp only [hindex] at hcommand
      split at hcommand
      · split at hcommand
        · split at hcommand
          · unfold liftPlayerPolicy at hcommand
            rw [FinDist.support_map] at hcommand
            obtain ⟨baseCommand, hbase, rfl⟩ := hcommand
            exact Or.inl (by simpa using hbase)
          · simp only [FinDist.mem_support_pure] at hcommand
            subst command
            exact Or.inr (runtime.image.idleOrExpiryCommand_wait)
        · simp only [FinDist.mem_support_pure] at hcommand
          subst command
          cases hdue : runtime.dueExpiry? view.application with
          | none => exact Or.inr (runtime.image.idleOrExpiryCommand_wait)
          | some payload =>
              exact Or.inr (runtime.image.idleOrExpiryCommand_submit payload
                (runtime.dueExpiry?_deadlineDependent view.application payload hdue))
      · simp only [FinDist.mem_support_pure] at hcommand
        subst command
        exact Or.inr (runtime.image.idleOrExpiryCommand_wait)

end Vegas.WindowedApplication

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Any windowed player wrapper whose supported commands come from the lifted
source policy or are idle/expiry commands preserves typed accepted-binding
provenance throughout an actual run. -/
theorem windowed_registeredBindings_of_source_commands
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (profile : SourceBehavioralProfile prog) (owner : P)
    (players : P →
      (plan.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (hcommands : ∀ history view command, command ∈ (players owner history view).support →
      (plan.windowed deadlineOf binding choice windowOf).erasePlayerCommand command ∈
          (plan.liftProfile deadlineOf profile owner
            (history.map (plan.windowed deadlineOf binding choice windowOf).erasePlayerEntry)
            ((plan.windowed deadlineOf binding choice windowOf).eraseView view)).support ∨
        (plan.windowed deadlineOf binding choice windowOf).image.IdleOrExpiryCommand
          ((plan.windowed deadlineOf binding choice windowOf).erasePlayerCommand command))
    (environment : (plan.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (next : (plan.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hnext : next ∈ ((plan.windowed deadlineOf binding choice windowOf).application.runPolicies
      players environment schedule
      (PolicyExecution.initial
        (plan.windowed deadlineOf binding choice windowOf).application
        (MessageApplication.State.initial
          (plan.windowed deadlineOf binding choice windowOf).application
          ((plan.windowed deadlineOf binding choice windowOf).initial
            (ApplicationImage.State.initial
              (ApplicationImage.Memory.initial
                (compileCore prog fresh state).graph)))))).support) :
    let runtime := plan.windowed deadlineOf binding choice windowOf
    runtime.image.RegisteredBindings owner
      (fun slot typed => ∃ spec : FieldSpec P L,
        (compileCore prog fresh state).graph.field? slot = some spec ∧ typed.ty = spec.ty)
      ((next.principalHistory owner).map fun entry =>
        show runtime.image.application.PlayerEntry from runtime.erasePlayerEntry entry)
      next.native.application.base := by
  let runtime := plan.windowed deadlineOf binding choice windowOf
  apply runtime.runPolicies_registeredBindings_of_registered_submissions
    (ApplicationImage.Memory.initial (compileCore prog fresh state).graph)
    (by intro field; rfl) owner
    (fun slot typed => ∃ spec : FieldSpec P L,
      (compileCore prog fresh state).graph.field? slot = some spec ∧ typed.ty = spec.ty)
    players environment
    ?_ schedule next hnext
  intro history view address handle hsubmission
  rcases hcommands history view (.submit (.binding address handle)) hsubmission with
    hsource | hidle
  · change (.submit (.binding address handle) :
        (plan.image deadlineOf).application.PlayerCommand) ∈
      (plan.liftProfile deadlineOf profile owner
        (history.map runtime.erasePlayerEntry) (runtime.eraseView view)).support at hsource
    have hregistered := plan.liftProfileIn_binding_submission
      (plan.image deadlineOf) deadlineOf profile owner
      (history.map runtime.erasePlayerEntry) (runtime.eraseView view) address handle
      hsource
    obtain ⟨howner, value, hcache, hvalid⟩ := hregistered
    refine ⟨howner, value, ?_, hvalid⟩
    have hcacheEq : runtime.image.registrationCache handle.2
          (history.map fun entry =>
            show runtime.image.application.PlayerEntry from runtime.erasePlayerEntry entry) =
        (plan.image deadlineOf).registrationCache handle.2
          (history.map runtime.erasePlayerEntry) := by
      clear hsubmission hsource hcache hvalid value howner view
      induction history with
      | nil => rfl
      | cons entry rest ih =>
          rcases entry with ⟨beforeView, command⟩
          cases command with
          | privateCommand privateCommand =>
              cases privateCommand with
              | register slot value =>
                  simp only [ApplicationImage.registrationCache, ChoiceEncoding.cachedValue,
                    WindowedApplication.erasePlayerEntry,
                    WindowedApplication.erasePlayerCommand, ChoiceEncoding.privateCommand,
                    ApplicationImage.registrationEncoding, List.map_cons]
                  split <;> try rfl
                  exact ih
          | submit payload | replay id | wait =>
              simp only [ApplicationImage.registrationCache, ChoiceEncoding.cachedValue,
                WindowedApplication.erasePlayerEntry,
                WindowedApplication.erasePlayerCommand, ChoiceEncoding.privateCommand,
                List.map_cons]
              exact ih
    exact hcacheEq.trans hcache
  · exact False.elim (hidle trivial)

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.windowed_registeredBindings_of_source_commands' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.windowed_registeredBindings_of_source_commands
