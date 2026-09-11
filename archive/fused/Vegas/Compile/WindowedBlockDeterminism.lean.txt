/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockAlignment

/-! # Determinism inside a pure deviator's instruction block

A fixed pure raw player policy may use every native command and its complete
local history. During that player's instruction block, the gated reference
policies of other players only wait or relay expiry. No source chance kernel
is invoked by this block. Its full native execution is therefore deterministic
from its starting checkpoint, not merely deterministic after outcome decoding.
-/

noncomputable section

namespace Vegas.WindowedApplication

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem playerStep_eq_pure (runtime : WindowedApplication P L) (who : P)
    (execution : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand) :
    ∃ next, runtime.application.playerStep who execution command = FinDist.pure next := by
  cases command <;>
    simp only [MessageApplication.playerStep, MessageApplication.advance,
      PlayerCommand.toAction, MessageApplication.step, FinDist.pure_bind] <;>
    exact ⟨_, rfl⟩

private theorem environmentPolicyStep_eq_pure (runtime : WindowedApplication P L)
    (execution : runtime.application.PolicyExecution)
    (command : runtime.application.EnvironmentPolicyCommand)
    (hcommand : ∀ address, command ≠ .application (.sample address)) :
    ∃ next, runtime.application.environmentPolicyStep execution command =
      FinDist.pure next := by
  cases command with
  | deliver who id | «include» id | wait =>
      simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
        EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind]
      exact ⟨_, rfl⟩
  | application command =>
      cases command with
      | sample address => exact False.elim (hcommand address rfl)
      | advance clock =>
          simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
            EnvironmentPolicyCommand.toAction, MessageApplication.step,
            application_advance, FinDist.map_pure, FinDist.pure_bind]
          exact ⟨_, rfl⟩

/-- Another owner's block never calls the supplied source policy. Its actual
command is deterministic, including any overdue relay submission. -/
theorem blockPlayer_other_eq_pure (runtime : WindowedApplication P L)
    (owner actor : P) (hne : actor ≠ owner) (base : runtime.application.PlayerPolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View)
    (instruction : ApplicationInstruction P L)
    (hindex : runtime.image.instructions[history.length / 3]? = some instruction)
    (howner : instruction.submitter = some owner) :
    ∃ command, runtime.blockPlayer actor base history view = FinDist.pure command := by
  simp only [blockPlayer, hindex]
  split
  · split
    · simp only [howner, Option.some.injEq, Ne.symm hne, ↓reduceIte]
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

private theorem latestSubmissionCommand_not_sample (runtime : WindowedApplication P L)
    (actor : P) (view : runtime.application.EnvironmentObservation) (address : Nat) :
    runtime.application.latestSubmissionCommand actor view ≠ .application (.sample address) := by
  rcases runtime.application.latestSubmissionCommand_cases actor view with hwait | ⟨id, hinclude⟩
  · rw [hwait]; simp
  · rw [hinclude]; simp

private theorem serviceCommand_not_sample (runtime : WindowedApplication P L)
    (instruction : ApplicationInstruction P L) (owner : P)
    (howner : instruction.submitter = some owner)
    (view : runtime.application.EnvironmentObservation) (address : Nat) :
    runtime.liftEnvironmentCommand
        (runtime.image.serviceCommand instruction (runtime.eraseEnvironmentView view)) ≠
      .application (.sample address) := by
  cases instruction with
  | sample code => cases howner
  | bind code | publicChoice code | conditional code =>
      simp only [ApplicationImage.serviceCommand, MessageApplication.latestSubmissionCommand]
      split
      · simp [liftEnvironmentCommand]
      · split <;> simp [liftEnvironmentCommand]

/-- The service of a player-owned instruction never requests source chance,
including in its ordinary, clock, and relay slots. -/
theorem blockEnvironment_noSample (runtime : WindowedApplication P L)
    (roster : List P) (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation)
    (instruction : ApplicationInstruction P L) (owner : P)
    (hindex : runtime.image.instructions[history.length / (roster.length + 2)]? =
      some instruction)
    (howner : instruction.submitter = some owner)
    (command : runtime.application.EnvironmentPolicyCommand)
    (hcommand : command ∈ (runtime.blockEnvironment roster history view).support) :
    ∀ address, command ≠ .application (.sample address) := by
  simp only [blockEnvironment, hindex, FinDist.mem_support_pure] at hcommand
  subst command
  intro address
  split
  · split
    · exact runtime.serviceCommand_not_sample instruction owner howner _ address
    · split
      · simp
      · split <;> simp
    · split
      · simp
      · exact runtime.latestSubmissionCommand_not_sample _ _ address
  · simp

/-- Every environment invocation in an owned block has a point-mass law.
The environment may include malformed traffic or advance the clock; it cannot
replace or pre-draw a source chance instruction through these slots. -/
theorem blockEnvironment_invoke_eq_pure (runtime : WindowedApplication P L)
    (roster : List P) (players : P → runtime.application.PlayerPolicy)
    (execution : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L) (owner : P)
    (hindex : runtime.image.instructions[execution.environmentHistory.length /
      (roster.length + 2)]? = some instruction)
    (howner : instruction.submitter = some owner) :
    ∃ next, runtime.application.invoke players (runtime.blockEnvironment roster)
      execution .environment = FinDist.pure next := by
  obtain ⟨command, hcommand⟩ : ∃ command,
      runtime.blockEnvironment roster execution.environmentHistory
        (State.environmentView runtime.application execution.native) =
          FinDist.pure command := ⟨_, rfl⟩
  simp only [MessageApplication.invoke, hcommand, FinDist.pure_bind]
  apply runtime.environmentPolicyStep_eq_pure
  exact runtime.blockEnvironment_noSample roster execution.environmentHistory
    (State.environmentView runtime.application execution.native) instruction owner hindex howner
    command (by rw [hcommand]; exact FinDist.mem_support_pure.mpr rfl)

/-- A block owned by a fixed pure raw policy has a point-mass law on complete
native executions. Only other players' reference policies are gated. Static
history ranges identify this instruction throughout the supplied block suffix;
no resolution, legality, or terminal-outcome premise is used. -/
theorem runPolicies_owner_block_eq_pure (runtime : WindowedApplication P L)
    (roster : List P) (owner : P)
    (replacement : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (base players : P → runtime.application.PlayerPolicy)
    (hfocal : players owner = fun history view => FinDist.pure (replacement history view))
    (hothers : ∀ actor, actor ≠ owner → players actor = runtime.blockPlayer actor (base actor))
    (instruction : ApplicationInstruction P L) (howner : instruction.submitter = some owner)
    (schedule : List (@Invocation P)) (execution : runtime.application.PolicyExecution)
    (hplayerIndex : ∀ actor index, (execution.principalHistory actor).length ≤ index →
      index < (execution.principalHistory actor).length +
        schedule.countP (fun call => match call with
          | .player who => decide (who = actor)
          | .environment => false) →
      runtime.image.instructions[index / 3]? = some instruction)
    (henvironmentIndex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length + schedule.countP Invocation.isEnvironment →
      runtime.image.instructions[index / (roster.length + 2)]? = some instruction) :
    ∃ next, runtime.application.runPolicies players (runtime.blockEnvironment roster)
      schedule execution = FinDist.pure next := by
  induction schedule generalizing execution with
  | nil => exact ⟨execution, rfl⟩
  | cons invocation rest ih =>
      have hfirst : ∃ middle, runtime.application.invoke players
          (runtime.blockEnvironment roster) execution invocation = FinDist.pure middle := by
        cases invocation with
        | environment =>
            apply runtime.blockEnvironment_invoke_eq_pure roster players execution instruction owner
            · exact henvironmentIndex _ (Nat.le_refl _) (by simp [Invocation.isEnvironment])
            · exact howner
        | player actor =>
            obtain ⟨command, hcommand⟩ : ∃ command,
                players actor (execution.principalHistory actor)
                  (State.observe runtime.application execution.native actor) =
                    FinDist.pure command := by
              by_cases hactor : actor = owner
              · subst actor
                exact ⟨_, congrFun (congrFun hfocal _) _⟩
              · rw [hothers actor hactor]
                apply runtime.blockPlayer_other_eq_pure owner actor hactor (base actor)
                  _ _ instruction
                · exact hplayerIndex actor _ (Nat.le_refl _) (by simp)
                · exact howner
            simp only [MessageApplication.invoke, hcommand, FinDist.pure_bind]
            exact runtime.playerStep_eq_pure actor execution command
      obtain ⟨middle, hmiddle⟩ := hfirst
      have hsupported : middle ∈ (runtime.application.runPolicies players
          (runtime.blockEnvironment roster) [invocation] execution).support := by
        simp only [MessageApplication.runPolicies, hmiddle, FinDist.pure_bind,
          FinDist.mem_support_pure]
      obtain ⟨next, hnext⟩ := ih middle
        (fun actor index hlo hhi => by
          have hlength : (middle.principalHistory actor).length =
              (execution.principalHistory actor).length + [invocation].countP
                (fun call => match call with
                | .player who => decide (who = actor)
                | .environment => false) :=
            runtime.application.runPolicies_principalHistory_length actor players
              (runtime.blockEnvironment roster) [invocation] execution middle hsupported
          apply hplayerIndex actor index
          · omega
          · change index < (execution.principalHistory actor).length +
              ([invocation] ++ rest).countP (fun call => match call with
                | .player who => decide (who = actor)
                | .environment => false)
            rw [List.countP_append]
            omega)
        (fun index hlo hhi => by
          have hlength := runtime.application.runPolicies_environmentHistory_length players
            (runtime.blockEnvironment roster) [invocation] execution middle hsupported
          apply henvironmentIndex index
          · omega
          · change index < execution.environmentHistory.length +
              ([invocation] ++ rest).countP Invocation.isEnvironment
            rw [List.countP_append]
            omega)
      exact ⟨next, by rw [MessageApplication.runPolicies, hmiddle, FinDist.pure_bind, hnext]⟩

/-- The fixed polling block discharges the history-range premises from its
actual roster counts. This applies at every aligned checkpoint, irrespective
of pending raw traffic or hidden preparation. -/
theorem runPolicies_block_eq_pure (runtime : WindowedApplication P L)
    (roster : List P) (hroster : roster.Nodup) (owner : P)
    (replacement : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (base players : P → runtime.application.PlayerPolicy)
    (hfocal : players owner = fun history view => FinDist.pure (replacement history view))
    (hothers : ∀ actor, actor ≠ owner → players actor = runtime.blockPlayer actor (base actor))
    (instruction : ApplicationInstruction P L) (howner : instruction.submitter = some owner)
    (block : Nat) (execution : runtime.application.PolicyExecution)
    (hindex : runtime.image.instructions[block]? = some instruction)
    (hplayers : ∀ actor ∈ roster, (execution.principalHistory actor).length = 3 * block)
    (henvironment : execution.environmentHistory.length = block * (roster.length + 2)) :
    ∃ next, runtime.application.runPolicies players (runtime.blockEnvironment roster)
      (blockInvocations roster) execution = FinDist.pure next := by
  apply runtime.runPolicies_owner_block_eq_pure roster owner replacement base players
    hfocal hothers instruction howner
  · intro actor index hlo hhi
    have hcount : (blockInvocations roster).countP (fun call => match call with
        | .player who => decide (who = actor)
        | .environment => false) = if actor ∈ roster then 3 else 0 :=
      blockInvocations_player_count roster hroster actor
    rw [hcount] at hhi
    by_cases hmem : actor ∈ roster
    · simp only [hmem, ↓reduceIte] at hhi
      have hlength := hplayers actor hmem
      have hquotient : index / 3 = block := by omega
      rw [hquotient]
      exact hindex
    · simp only [hmem, ↓reduceIte, Nat.add_zero] at hhi
      omega
  · intro index hlo hhi
    rw [blockInvocations_environment_count, henvironment] at hhi
    rw [henvironment] at hlo
    have hquotient : index / (roster.length + 2) = block :=
      Nat.div_eq_of_lt_le (by simpa [Nat.mul_comm] using hlo)
        (by nlinarith)
    rw [hquotient]
    exact hindex

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.runPolicies_owner_block_eq_pure' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_owner_block_eq_pure

/-- info: 'Vegas.WindowedApplication.runPolicies_block_eq_pure' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_block_eq_pure
