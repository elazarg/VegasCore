/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedDeliveryService
import Vegas.Compile.WindowedBlockAlignment

/-! # Delivery-block history alignment

The delivery-enabled schedule gives every roster member four player turns.
After its two ordinary turns a member is at reaction slot two; after the
reaction phase it is at relay slot three. Delivery slots advance only the
environment history by the fixed recipient count.
-/

noncomputable section

namespace Vegas.WindowedApplication

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem reactionInvocations_player_count (roster : List P)
    (hroster : roster.Nodup) (who : P) :
    (roster.map Invocation.player).countP (fun invocation => match invocation with
      | .player actor => decide (actor = who)
      | .environment => false) = if who ∈ roster then 1 else 0 := by
  induction roster with
  | nil => rfl
  | cons actor rest ih =>
      rw [List.nodup_cons] at hroster
      by_cases hactor : actor = who
      · subst actor
        simp [hroster.1, ih hroster.2]
      · simp [hactor, Ne.symm hactor, ih hroster.2]

omit [DecidableEq P] in
private theorem deliveryInvocations_environment_count (recipients : List P) :
    (recipients.map fun _ => (Invocation.environment : @Invocation P)).countP
      Invocation.isEnvironment =
      recipients.length := by
  induction recipients with
  | nil => rfl
  | cons recipient rest ih =>
      simp only [List.map_cons, List.countP_cons, Invocation.isEnvironment, ↓reduceIte, ih,
        List.length_cons]

private theorem deliveryInvocations_player_count (recipients : List P) (who : P) :
    (recipients.map fun _ => (Invocation.environment : @Invocation P)).countP (fun invocation =>
      match invocation with
      | .player actor => decide (actor = who)
      | .environment => false) = 0 := by
  induction recipients with
  | nil => rfl
  | cons recipient rest ih =>
      simp only [List.map_cons, List.countP_cons, Bool.false_eq_true, ↓reduceIte, ih]

/-- A complete delivery block invokes each member of a duplicate-free roster
four times and every principal outside the roster zero times. -/
theorem deliveryBlockInvocations_player_count (roster recipients : List P)
    (hroster : roster.Nodup) (who : P) :
    (deliveryBlockInvocations roster recipients).countP (fun invocation =>
      match invocation with
      | .player actor => decide (actor = who)
      | .environment => false) = if who ∈ roster then 4 else 0 := by
  have hpolls := ordinaryPolls_player_count roster hroster who
  have hrelays := relayInvocations_player_count roster hroster who
  have hreactions := reactionInvocations_player_count roster hroster who
  have hdeliveries := deliveryInvocations_player_count recipients who
  simp only [deliveryBlockInvocations, List.countP_append]
  erw [hpolls, hdeliveries, hreactions, hrelays]
  by_cases hwho : who ∈ roster <;> simp [hwho]

/-- Repeating delivery blocks gives each roster member four policy entries per
completed block. -/
theorem repeatedDeliveryBlockInvocations_player_count (roster recipients : List P)
    (hroster : roster.Nodup) (who : P) (hwho : who ∈ roster) (count : Nat) :
    (List.replicate count (deliveryBlockInvocations roster recipients)).flatten.countP
      (fun invocation => match invocation with
        | .player actor => decide (actor = who)
        | .environment => false) = 4 * count := by
  induction count with
  | zero => simp
  | succ count ih =>
      simp [List.replicate_succ, List.countP_append,
        deliveryBlockInvocations_player_count roster recipients hroster who, hwho, ih]
      omega

omit [DecidableEq P] in
/-- Repeating delivery blocks multiplies their fixed environment width. -/
theorem repeatedDeliveryBlockInvocations_environment_count
    (roster recipients : List P) (count : Nat) :
    (List.replicate count (deliveryBlockInvocations roster recipients)).flatten.countP
      Invocation.isEnvironment = count * (recipients.length + roster.length + 2) := by
  induction count with
  | zero => simp
  | succ count ih =>
      simp [List.replicate_succ, List.countP_append,
        deliveryBlockInvocations_environment_count, ih, Nat.succ_mul, Nat.add_comm]

/-- Supported repeated delivery blocks align both policy histories with the
same completed-block coordinate. -/
theorem runPolicies_repeatedDeliveryBlocks_history_alignment
    (runtime : WindowedApplication P L) (roster recipients : List P)
    (hroster : roster.Nodup) (who : P) (hwho : who ∈ roster)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (count : Nat) (initial : runtime.application.State)
    (next : runtime.application.PolicyExecution)
    (hnext : next ∈ (runtime.application.runPolicies players environment
      (List.replicate count (deliveryBlockInvocations roster recipients)).flatten
      (PolicyExecution.initial runtime.application initial)).support) :
    (next.principalHistory who).length = 4 * count ∧
      next.environmentHistory.length = count * (recipients.length + roster.length + 2) ∧
      (next.principalHistory who).length / 4 = count ∧
      next.environmentHistory.length / (recipients.length + roster.length + 2) = count := by
  have hplayer := runtime.application.runPolicies_principalHistory_length who players
    environment _ (PolicyExecution.initial runtime.application initial) next hnext
  have henvironment := runtime.application.runPolicies_environmentHistory_length players
    environment _ (PolicyExecution.initial runtime.application initial) next hnext
  simp only [PolicyExecution.initial, List.length_nil, Nat.zero_add] at hplayer henvironment
  have hpcount := repeatedDeliveryBlockInvocations_player_count roster recipients hroster
    who hwho count
  have hecount := repeatedDeliveryBlockInvocations_environment_count roster recipients count
  have hp : (next.principalHistory who).length = 4 * count := hplayer.trans hpcount
  have he : next.environmentHistory.length =
      count * (recipients.length + roster.length + 2) := henvironment.trans hecount
  refine ⟨hp, he, ?_, ?_⟩
  · rw [hp]
    omega
  · rw [he]
    rw [Nat.mul_comm count (recipients.length + roster.length + 2)]
    exact Nat.mul_div_right count (by omega)

/-- Starting at a delivery-block boundary, the ordinary two-poll phase leaves
each roster member exactly at reaction slot two. -/
theorem runPolicies_deliveryOrdinary_reaction_slot
    (runtime : WindowedApplication P L) (roster : List P) (hroster : roster.Nodup)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy) (blockIndex : Nat)
    (execution polled : runtime.application.PolicyExecution)
    (hstart : ∀ actor ∈ roster,
      (execution.principalHistory actor).length = 4 * blockIndex)
    (hpolled : polled ∈ (runtime.application.runPolicies players environment
      (roster.flatMap fun actor => [.player actor, .player actor]) execution).support) :
    ∀ actor ∈ roster, (polled.principalHistory actor).length % 4 = 2 := by
  intro actor hactor
  have hlength := runtime.application.runPolicies_principalHistory_length actor players
    environment _ execution polled hpolled
  have hcount : (roster.flatMap fun actor => [.player actor, .player actor]).countP
      (fun call : @Invocation P => match call with
        | .player who => decide (who = actor)
        | .environment => false) = 2 :=
    (ordinaryPolls_player_count roster hroster actor).trans (if_pos hactor)
  have hlength' : (polled.principalHistory actor).length = 4 * blockIndex + 2 := by
    have hadd := congrArg
      (fun count => (execution.principalHistory actor).length + count) hcount
    calc
      _ = (execution.principalHistory actor).length + _ := hlength
      _ = (execution.principalHistory actor).length + 2 := hadd
      _ = 4 * blockIndex + 2 := by rw [hstart actor hactor]
  rw [hlength']
  omega

/-- The reaction phase contributes one further turn to every roster member,
leaving it exactly at relay slot three. -/
theorem runPolicies_deliveryReactions_relay_slot
    (runtime : WindowedApplication P L) (roster : List P) (hroster : roster.Nodup)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy) (blockIndex : Nat)
    (execution reacted : runtime.application.PolicyExecution)
    (hstart : ∀ actor ∈ roster,
      (execution.principalHistory actor).length = 4 * blockIndex + 2)
    (hreacted : reacted ∈ (runtime.application.runPolicies players environment
      (roster.map Invocation.player) execution).support) :
    ∀ actor ∈ roster, (reacted.principalHistory actor).length % 4 = 3 := by
  intro actor hactor
  have hlength := runtime.application.runPolicies_principalHistory_length actor players
    environment _ execution reacted hreacted
  have hcount : (roster.map Invocation.player).countP (fun invocation => match invocation with
      | .player who => decide (who = actor)
      | .environment => false) = 1 :=
    (reactionInvocations_player_count roster hroster actor).trans (if_pos hactor)
  have hlength' : (reacted.principalHistory actor).length = 4 * blockIndex + 3 := by
    have hadd := congrArg
      (fun count => (execution.principalHistory actor).length + count) hcount
    calc
      _ = (execution.principalHistory actor).length + _ := hlength
      _ = (execution.principalHistory actor).length + 1 := hadd
      _ = 4 * blockIndex + 3 := by rw [hstart actor hactor]
  rw [hlength']
  omega

/-- From an aligned block boundary, the recipient delivery slots advance the
environment history by exactly the recipient count. -/
theorem runPolicies_deliverySlots_environment_alignment
    (runtime : WindowedApplication P L) (roster recipients : List P)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy) (blockIndex : Nat)
    (execution delivered : runtime.application.PolicyExecution)
    (hstart : execution.environmentHistory.length =
      blockIndex * (recipients.length + roster.length + 2))
    (hdelivered : delivered ∈ (runtime.application.runPolicies players environment
      (recipients.map fun _ => (Invocation.environment : @Invocation P)) execution).support) :
    delivered.environmentHistory.length =
      blockIndex * (recipients.length + roster.length + 2) + recipients.length := by
  have hlength := runtime.application.runPolicies_environmentHistory_length players
    environment _ execution delivered hdelivered
  rw [deliveryInvocations_environment_count recipients, hstart] at hlength
  exact hlength

end Vegas.WindowedApplication
