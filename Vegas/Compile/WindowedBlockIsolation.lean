/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockService
import Vegas.Compile.ApplicationOrderPrefix
import Vegas.Compile.ApplicationImageStateRefinement
import Interaction.MessageApplicationLocality

/-! # Isolation of a resolved instruction's service block

Once a block's address is no longer active, its remaining environment slots
cannot change public application memory or activation. Player commands remain
arbitrary, including private registration, submission, and replay. Those
commands can still change preparation, pools, and histories; the theorem
preserves exactly the public application checkpoint, not the complete state.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Successful windowed handling finishes the current instruction and makes
its address inactive. This follows from the actual handler's completion effect,
including expiry handlers; it is not an assumed service postcondition. -/
theorem handle_resolves_active (runtime : WindowedApplication P L)
    (before after : WindowedApplication.State P L)
    (message : Message P (ApplicationImage.Payload P L))
    (hafter : runtime.handle before message = some after) :
    ∃ address, runtime.image.activeAddress? before.base.memory = some address ∧
      after.base.memory.done address = true ∧
      runtime.image.activeAddress? after.base.memory ≠ some address := by
  obtain ⟨activation, base, _, _, hbase, rfl⟩ :=
    runtime.handle_some before after message hafter
  obtain ⟨address, hactive, hdone, hinactive⟩ :=
    (runtime.atOrigin activation.since).ordered_handle_resolves before.base base message hbase
  simpa only [atOrigin, ApplicationImage.activeAddress?_withDeadlines, advanceTo] using
    (show ∃ address, (runtime.atOrigin activation.since).activeAddress? before.base.memory =
        some address ∧ base.memory.done address = true ∧
        (runtime.atOrigin activation.since).activeAddress? base.memory ≠ some address from
      ⟨address, hactive, hdone, hinactive⟩)

/-- Raw player commands cannot execute an application transition or advance
the public clock. Registration changes only private preparation. -/
theorem playerStep_publicState (runtime : WindowedApplication P L) (who : P)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand)
    (hnext : next ∈ (runtime.application.playerStep who execution command).support) :
    (next.native.application.base.memory, next.native.application.active) =
      (execution.native.application.base.memory, execution.native.application.active) := by
  have hnative : next.native ∈
      ((runtime.application.playerStep who execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [runtime.application.playerStep_native] at hnative
  cases command with
  | privateCommand command =>
      cases command with
      | register slot value =>
          simp only [PlayerCommand.toAction, MessageApplication.step, application,
            FinDist.mem_support_pure] at hnative
          rw [hnative]
          rfl
  | submit payload | replay id | wait =>
      simp only [PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]

/-- Any finite sequence of player polls preserves the public application
checkpoint. Each policy may still randomize and retain its actual commands. -/
theorem runPolicies_players_publicState (runtime : WindowedApplication P L)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (hplayers : Invocation.environment ∉ schedule)
    (execution next : runtime.application.PolicyExecution)
    (hnext : next ∈
      (runtime.application.runPolicies players environment schedule execution).support) :
    (next.native.application.base.memory, next.native.application.active) =
      (execution.native.application.base.memory, execution.native.application.active) := by
  induction schedule generalizing execution with
  | nil =>
      simp only [MessageApplication.runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      rfl
  | cons invocation rest ih =>
      simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      cases invocation with
      | environment => exact False.elim (hplayers (List.mem_cons_self ..))
      | player who =>
          simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          exact (ih (fun hmem => hplayers (List.mem_cons_of_mem _ hmem)) middle hnext).trans
            (runtime.playerStep_publicState who execution middle command hstep)

/-- Polling other principals before the owner preserves the owner's next
command kernel. The joint law retains all intervening native states and raw
traffic; it does not reset histories or discard the deviator's private memory. -/
theorem runPolicies_before_player (runtime : WindowedApplication P L) (who : P)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (before : List (@Invocation P))
    (henvironment : Invocation.environment ∉ before)
    (howner : Invocation.player who ∉ before)
    (execution : runtime.application.PolicyExecution) :
    runtime.application.runPolicies players environment (before ++ [.player who]) execution =
      (runtime.application.runPolicies players environment before execution).bind fun middle =>
        (players who (execution.principalHistory who)
          (MessageApplication.State.observe runtime.application execution.native who)).bind
            (runtime.application.playerStep who middle) := by
  rw [MessageApplication.runPolicies_append]
  apply FinDist.bind_congr
  intro middle hmiddle
  have hinput := runtime.application.runPolicies_other_input who
    (fun state actor command _ => by cases command; rfl)
    players environment before henvironment howner execution middle hmiddle
  have hhistory : middle.principalHistory who = execution.principalHistory who :=
    congrArg Prod.fst hinput
  have hview : MessageApplication.State.observe runtime.application middle.native who =
      MessageApplication.State.observe runtime.application execution.native who :=
    congrArg Prod.snd hinput
  simp only [MessageApplication.runPolicies, MessageApplication.invoke,
    FinDist.bind_pure, hhistory, hview]

/-- An invariant preserved by private preparation remains true throughout an
inactive block. Its environment slots execute waits; raw player policies still
retain all private-command, submission, and replay choices. -/
theorem runPolicies_block_inactive_invariant (runtime : WindowedApplication P L)
    (roster : List P) (players : P → runtime.application.PlayerPolicy)
    (schedule : List (@Invocation P))
    (execution next : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length + schedule.countP Invocation.isEnvironment →
      runtime.image.instructions[index / (roster.length + 2)]? = some instruction)
    (Invariant : WindowedApplication.State P L → Prop)
    (hprivate : ∀ state actor command, Invariant state →
      Invariant (runtime.application.privateStep state actor command))
    (hinactive : ∀ state, Invariant state →
      runtime.image.activeAddress? state.base.memory ≠ some instruction.address)
    (hinvariant : Invariant execution.native.application)
    (hnext : next ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) schedule execution).support) :
    Invariant next.native.application := by
  induction schedule generalizing execution with
  | nil =>
      simp only [MessageApplication.runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact hinvariant
  | cons invocation rest ih =>
      simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      have hmiddleInvariant : Invariant middle.native.application := by
        cases invocation with
        | player actor =>
            simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
            obtain ⟨command, _, hstep⟩ := hmiddle
            cases command with
            | privateCommand command =>
                simp only [MessageApplication.playerStep, PlayerCommand.toAction,
                  MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
                  FinDist.mem_support_pure] at hstep
                subst middle
                exact hprivate _ actor command hinvariant
            | submit payload | replay id | wait =>
                simp only [MessageApplication.playerStep, PlayerCommand.toAction,
                  MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
                  FinDist.mem_support_pure] at hstep
                subst middle
                exact hinvariant
        | environment =>
            have hpolicy := runtime.blockEnvironment_inactive roster execution.environmentHistory
              (MessageApplication.State.environmentView runtime.application execution.native)
              instruction (hindex _ (Nat.le_refl _) (by
                simp [Invocation.isEnvironment])) (hinactive _ hinvariant)
            simp only [MessageApplication.invoke, hpolicy, FinDist.pure_bind,
              MessageApplication.environmentStep_wait, FinDist.mem_support_pure] at hmiddle
            subst middle
            exact hinvariant
      have hlength := runtime.application.runPolicies_environmentHistory_length players
        (runtime.blockEnvironment roster) [invocation] execution middle
          (by simpa [MessageApplication.runPolicies] using hmiddle)
      apply ih middle ?_ hmiddleInvariant hnext
      intro index hlo hhi
      apply hindex index <;>
        cases invocation <;>
        simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
          Bool.false_eq_true, ↓reduceIte] at hlength ⊢ <;> omega

/-- A suffix whose environment slots all belong to a resolved address has
no public application effect, even with arbitrary policies for every player.
The history-range premise is a finite schedule fact, not a progress premise. -/
theorem runPolicies_block_inactive (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy)
    (schedule : List (@Invocation P)) (execution next : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length + schedule.countP Invocation.isEnvironment →
      runtime.image.instructions[index / (roster.length + 2)]? = some instruction)
    (hinactive : runtime.image.activeAddress? execution.native.application.base.memory ≠
      some instruction.address)
    (hnext : next ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) schedule execution).support) :
    (next.native.application.base.memory, next.native.application.active) =
      (execution.native.application.base.memory, execution.native.application.active) := by
  apply runtime.runPolicies_block_inactive_invariant roster players schedule execution next
    instruction hindex
    (fun state => (state.base.memory, state.active) =
      (execution.native.application.base.memory, execution.native.application.active))
  · intro state actor command hstate
    cases command with
    | register slot value => exact hstate
  · intro state hstate
    have hmemory : state.base.memory = execution.native.application.base.memory :=
      congrArg Prod.fst hstate
    rwa [hmemory]
  · rfl
  · exact hnext

/-- An aligned inactive suffix preserves the same source refinement even when
raw private preparation changes. The accepted frozen values remain intact. -/
theorem runPolicies_block_inactive_refines (runtime : WindowedApplication P L)
    {G : EventGraph.Graph P L} (cfg : EventGraph.Config G)
    (roster : List P) (players : P → runtime.application.PlayerPolicy)
    (schedule : List (@Invocation P))
    (execution next : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length + schedule.countP Invocation.isEnvironment →
      runtime.image.instructions[index / (roster.length + 2)]? = some instruction)
    (hinactive : runtime.image.activeAddress? execution.native.application.base.memory ≠
      some instruction.address)
    (hrefines : execution.native.application.base.Refines cfg)
    (hnext : next ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) schedule execution).support) :
    next.native.application.base.Refines cfg := by
  have hresult := runtime.runPolicies_block_inactive_invariant roster players schedule
    execution next instruction hindex
    (fun state => state.base.Refines cfg ∧
      runtime.image.activeAddress? state.base.memory ≠ some instruction.address)
    (by
      intro state actor command hstate
      cases command with
      | register slot value => exact ⟨hstate.1.register actor slot value, hstate.2⟩)
    (fun _ hstate => hstate.2) ⟨hrefines, hinactive⟩ hnext
  exact hresult.1

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.runPolicies_block_inactive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_block_inactive
