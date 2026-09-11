/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockService
import Interaction.MessageApplicationHistoryCounts

/-! # Windowed block history alignment

The fixed block schedule advances every roster member by three player-policy
entries and advances the environment by the block width. Consequently the
history quotients used by the block policies select the same block index.
-/

noncomputable section

namespace Vegas.WindowedApplication

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

omit [DecidableEq P] in
/-- Each relay pair contains one environment invocation. -/
theorem relayInvocations_environment_count (roster : List P) :
    (roster.flatMap (fun actor =>
      [Invocation.player actor, Invocation.environment])).countP Invocation.isEnvironment =
        roster.length := by
  induction roster with
  | nil => rfl
  | cons actor rest ih => simp [List.flatMap_cons, Invocation.isEnvironment, ih]

/-- The ordinary phase polls each roster member twice. -/
theorem ordinaryPolls_player_count (roster : List P) (hroster : roster.Nodup)
    (who : P) :
    (roster.flatMap (fun actor =>
      [Invocation.player actor, Invocation.player actor])).countP (fun call => match call with
      | .player actor => decide (actor = who)
      | .environment => false) = if who ∈ roster then 2 else 0 := by
  induction roster with
  | nil => rfl
  | cons actor rest ih =>
      rw [List.nodup_cons] at hroster
      by_cases hactor : actor = who
      · subst actor
        simp [List.flatMap_cons, hroster.1, ih hroster.2]
      · have hactor' : who ≠ actor := Ne.symm hactor
        simp [List.flatMap_cons, hactor, hactor', ih hroster.2]

/-- The relay phase polls each roster member once. -/
theorem relayInvocations_player_count (roster : List P) (hroster : roster.Nodup)
    (who : P) :
    (roster.flatMap (fun actor =>
      [Invocation.player actor, Invocation.environment])).countP (fun call => match call with
      | .player actor => decide (actor = who)
      | .environment => false) = if who ∈ roster then 1 else 0 := by
  induction roster with
  | nil => rfl
  | cons actor rest ih =>
      rw [List.nodup_cons] at hroster
      by_cases hactor : actor = who
      · subst actor
        simp [List.flatMap_cons, hroster.1, ih hroster.2]
      · have hactor' : who ≠ actor := Ne.symm hactor
        simp [List.flatMap_cons, hactor, hactor', ih hroster.2]

/-- One complete block invokes each member of a duplicate-free roster exactly
three times and invokes principals outside the roster zero times. -/
theorem blockInvocations_player_count (roster : List P) (hroster : roster.Nodup)
    (who : P) :
    (blockInvocations roster).countP (fun invocation =>
      match invocation with
      | .player actor => decide (actor = who)
      | .environment => false) = if who ∈ roster then 3 else 0 := by
  have hnormal := ordinaryPolls_player_count roster hroster who
  have hrelay := relayInvocations_player_count roster hroster who
  by_cases hwho : who ∈ roster
  · simp [blockInvocations, List.countP_append, hnormal, hrelay, hwho]
  · simp [blockInvocations, List.countP_append, hnormal, hrelay, hwho]

/-- Repeating complete blocks multiplies each roster member's three slots. -/
theorem repeatedBlockInvocations_player_count (roster : List P)
    (hroster : roster.Nodup) (who : P) (hwho : who ∈ roster) (count : Nat) :
    (List.replicate count (blockInvocations roster)).flatten.countP (fun invocation =>
      match invocation with
      | .player actor => decide (actor = who)
      | .environment => false) = 3 * count := by
  induction count with
  | zero => simp
  | succ count ih =>
      simp [List.replicate_succ, List.countP_append,
        blockInvocations_player_count roster hroster who, hwho, ih]
      omega

omit [DecidableEq P] in
/-- Repeating complete blocks multiplies the environment block width. -/
theorem repeatedBlockInvocations_environment_count (roster : List P) (count : Nat) :
    (List.replicate count (blockInvocations roster)).flatten.countP
      Invocation.isEnvironment = count * (roster.length + 2) := by
  induction count with
  | zero => simp
  | succ count ih =>
      simp [List.replicate_succ, List.countP_append,
        blockInvocations_environment_count, ih, Nat.succ_mul, Nat.add_comm]

/-- Supported runs from an initial execution keep player and environment
history lengths aligned on the same completed-block index. -/
theorem runPolicies_repeatedBlocks_history_alignment
    (runtime : WindowedApplication P L) (roster : List P) (hroster : roster.Nodup)
    (who : P) (hwho : who ∈ roster)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (count : Nat) (initial : runtime.application.State)
    (next : runtime.application.PolicyExecution)
    (hnext : next ∈ (runtime.application.runPolicies players environment
      (List.replicate count (blockInvocations roster)).flatten
      (PolicyExecution.initial runtime.application initial)).support) :
    (next.principalHistory who).length = 3 * count ∧
      next.environmentHistory.length = count * (roster.length + 2) ∧
      (next.principalHistory who).length / 3 = count ∧
      next.environmentHistory.length / (roster.length + 2) = count := by
  have hplayer := runtime.application.runPolicies_principalHistory_length who players
    environment (List.replicate count (blockInvocations roster)).flatten
    (PolicyExecution.initial runtime.application initial) next hnext
  have henvironment := runtime.application.runPolicies_environmentHistory_length players
    environment (List.replicate count (blockInvocations roster)).flatten
    (PolicyExecution.initial runtime.application initial) next hnext
  simp only [PolicyExecution.initial, List.length_nil, Nat.zero_add] at hplayer henvironment
  have hplayerCount := repeatedBlockInvocations_player_count roster hroster who hwho count
  have henvironmentCount := repeatedBlockInvocations_environment_count roster count
  have hplayerLength : (next.principalHistory who).length = 3 * count :=
    hplayer.trans hplayerCount
  have henvironmentLength : next.environmentHistory.length =
      count * (roster.length + 2) := henvironment.trans henvironmentCount
  refine ⟨hplayerLength, henvironmentLength, ?_, ?_⟩
  · rw [hplayerLength]
    omega
  · rw [henvironmentLength]
    have hpositive : 0 < roster.length + 2 := by omega
    rw [Nat.mul_comm count (roster.length + 2)]
    exact Nat.mul_div_right count hpositive

/-- After the ordinary polls, the remaining player invocations occupy only
relay slots. This depends on the schedule and history counts, not on policies. -/
theorem runPolicies_polls_relay_slots
    (runtime : WindowedApplication P L) (roster : List P) (hroster : roster.Nodup)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy) (blockIndex : Nat)
    (execution polled : runtime.application.PolicyExecution)
    (hstart : ∀ actor ∈ roster, (execution.principalHistory actor).length = 3 * blockIndex)
    (hpolled : polled ∈ (runtime.application.runPolicies players environment
      (roster.flatMap fun actor => [Invocation.player actor, .player actor]) execution).support) :
    ∀ actor index, (polled.principalHistory actor).length ≤ index →
      index < (polled.principalHistory actor).length +
        ([Invocation.environment, .environment] ++
          roster.flatMap fun actor => [Invocation.player actor, .environment]).countP
            (fun call : @Invocation P => match call with
              | .player who => decide (who = actor)
              | .environment => false) → index % 3 = 2 := by
  intro actor index hlo hhi
  have hcount := relayInvocations_player_count roster hroster actor
  simp only [List.countP_append, List.countP_cons, List.countP_nil, Bool.false_eq_true,
    ↓reduceIte, Nat.zero_add, hcount] at hhi
  by_cases hmem : actor ∈ roster
  · simp only [hmem, ↓reduceIte] at hhi
    have hlength := runtime.application.runPolicies_principalHistory_length actor players
      environment _ execution polled hpolled
    have hlength' := hlength.trans
      (congrArg (fun count => (execution.principalHistory actor).length + count)
        (ordinaryPolls_player_count roster hroster actor))
    simp only [if_pos hmem, hstart actor hmem] at hlength'
    omega
  · simp only [hmem, ↓reduceIte, Nat.add_zero] at hhi
    omega

end Vegas.WindowedApplication
