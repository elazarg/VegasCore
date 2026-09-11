/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedDeliveryIsolation
import Vegas.Compile.WindowedDeliveryAlignment
import Interaction.MessageApplicationEnvironmentCommands
import Interaction.MessageApplicationArrival

/-! # Delivery-block prefix preservation

The prefix before a block's normal service coordinate consists of two raw
polls per roster member, recipient delivery slots, and one reaction poll per
roster member. It cannot include or advance the active instruction.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

def deliveryPreparation (roster recipients : List P) : List (@Invocation P) :=
  roster.flatMap (fun actor => [.player actor, .player actor]) ++
    recipients.map (fun _ => .environment) ++ roster.map Invocation.player

omit [DecidableEq P] in
/-- The preparation phase has one environment delivery coordinate per recipient. -/
theorem deliveryPreparation_environment_count (roster recipients : List P) :
    (deliveryPreparation roster recipients).countP Invocation.isEnvironment =
      recipients.length := by
  have hpolls : (roster.flatMap (fun actor => [Invocation.player actor,
      Invocation.player actor])).countP Invocation.isEnvironment = 0 := by
    induction roster with
    | nil => rfl
    | cons actor rest ih => simp [List.flatMap_cons, Invocation.isEnvironment, ih]
  have hdeliveries : (recipients.map (fun _ =>
      (Invocation.environment : @Invocation P))).countP Invocation.isEnvironment =
        recipients.length := by
    rw [List.countP_map]
    simp [Function.comp_def, Invocation.isEnvironment]
  have hreactions : (roster.map Invocation.player).countP Invocation.isEnvironment = 0 := by
    induction roster with
    | nil => rfl
    | cons actor rest ih => simp [Invocation.isEnvironment]
  simp only [deliveryPreparation, List.countP_append, hpolls, hdeliveries, hreactions,
    Nat.zero_add, Nat.add_zero]

/-- Every roster member has two ordinary polls and one reaction poll during preparation. -/
theorem deliveryPreparation_player_count (roster recipients : List P)
    (hroster : roster.Nodup) (actor : P) :
    (deliveryPreparation roster recipients).countP (fun invocation =>
      match invocation with
      | .player who => decide (who = actor)
      | .environment => false) = if actor ∈ roster then 3 else 0 := by
  let predicate : @Invocation P → Bool := fun invocation =>
    match invocation with
    | .player who => decide (who = actor)
    | .environment => false
  change (deliveryPreparation roster recipients).countP predicate = _
  have hpolls : (roster.flatMap (fun who =>
      [Invocation.player who, .player who])).countP predicate =
        if actor ∈ roster then 2 else 0 := by
    induction roster with
    | nil => simp
    | cons who rest ih =>
        have hnot : who ∉ rest := List.nodup_cons.mp hroster |>.1
        have hrest : rest.Nodup := List.nodup_cons.mp hroster |>.2
        rw [List.flatMap_cons, List.countP_append, ih hrest]
        by_cases hwho : who = actor
        · subst actor
          simp [predicate, hnot]
        · simp [predicate, hwho, Ne.symm hwho]
  have hdeliveries : (recipients.map (fun _ =>
      (Invocation.environment : @Invocation P))).countP predicate = 0 := by
    induction recipients with
    | nil => rfl
    | cons recipient rest ih => simp [predicate]
  have hreactions : (roster.map Invocation.player).countP predicate =
      if actor ∈ roster then 1 else 0 := by
    clear hpolls hdeliveries
    induction roster with
    | nil => simp
    | cons who rest ih =>
        have hnot : who ∉ rest := List.nodup_cons.mp hroster |>.1
        have hrest : rest.Nodup := List.nodup_cons.mp hroster |>.2
        rw [List.map_cons, List.countP_cons, ih hrest]
        by_cases hwho : who = actor
        · subst actor
          simp [predicate, hnot]
        · simp [predicate, hwho, Ne.symm hwho]
  simp only [deliveryPreparation, List.countP_append]
  rw [hpolls, hdeliveries, hreactions]
  split <;> omega

/-- Before normal service, arbitrary player traffic and recipient delivery
slots preserve the public application state and its source refinement. The
result also records activation invariants and exact policy-history growth. -/
theorem runPolicies_deliveryPreparation
    (runtime : WindowedApplication P L) (roster recipients : List P)
    (hroster : roster.Nodup)
    (players : P → runtime.application.PlayerPolicy)
    (execution final : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L) (blockIndex : Nat)
    (hstart : execution.environmentHistory.length =
      blockIndex * (recipients.length + roster.length + 2))
    (hindex : runtime.image.instructions[blockIndex]? = some instruction)
    {G : Graph P L} {cfg : Config G}
    (hrefines : execution.native.application.base.Refines cfg)
    (hfresh : execution.native.application.FreshActivation)
    (hconsistent : runtime.Consistent execution.native.application)
    (hfinal : final ∈ (runtime.application.runPolicies players
      (runtime.deliveryBlockEnvironment roster recipients)
      (deliveryPreparation roster recipients) execution).support) :
    final.native.application.base.Refines cfg ∧
      (final.native.application.base.memory, final.native.application.active) =
        (execution.native.application.base.memory, execution.native.application.active) ∧
      final.native.application.FreshActivation ∧
      runtime.Consistent final.native.application ∧
      (∀ actor, (final.principalHistory actor).length =
        (execution.principalHistory actor).length + if actor ∈ roster then 3 else 0) ∧
      final.environmentHistory.length =
        execution.environmentHistory.length + recipients.length := by
  have hpublic : final.native.application.base.Refines cfg ∧
      (final.native.application.base.memory, final.native.application.active) =
        (execution.native.application.base.memory, execution.native.application.active) := by
    have hcount := deliveryPreparation_environment_count roster recipients
    refine (runtime.application.arrival_phase
      (fun application => application.base.Refines cfg ∧
        (application.base.memory, application.active) =
          (execution.native.application.base.memory, execution.native.application.active))
      ?_ players (fun index => execution.environmentHistory.length ≤ index ∧
        index < execution.environmentHistory.length + recipients.length)
      (runtime.deliveryBlockEnvironment roster recipients) ?_
      (deliveryPreparation roster recipients) execution final ?_ ⟨hrefines, rfl⟩ hfinal).1
    · intro application actor command hinvariant
      cases command with
      | register slot value => exact ⟨hinvariant.1.register actor slot value, hinvariant.2⟩
    · intro history view command hrange hcommand
      have hquotient : history.length /
          (recipients.length + roster.length + 2) = blockIndex := by
        apply Nat.div_eq_of_lt_le
        · rw [← hstart]
          exact hrange.1
        · rw [Nat.add_mul, Nat.one_mul, ← hstart]
          exact lt_of_lt_of_le hrange.2 (by omega)
      have hmodDecomp := Nat.mod_add_div history.length
        (recipients.length + roster.length + 2)
      have hslotRange : history.length %
          (recipients.length + roster.length + 2) < recipients.length := by
        rw [hquotient] at hmodDecomp
        rw [Nat.mul_comm (recipients.length + roster.length + 2) blockIndex] at hmodDecomp
        rw [hstart] at hrange
        omega
      let recipient := recipients[history.length %
        (recipients.length + roster.length + 2)]
      have hrecipient : recipients[history.length %
          (recipients.length + roster.length + 2)]? = some recipient :=
        List.getElem?_eq_getElem hslotRange
      have hallowed := runtime.deliveryBlockEnvironment_recipient_only roster recipients
        history view
        instruction (history.length % (recipients.length + roster.length + 2)) recipient command
        (by rw [hquotient]; exact hindex) rfl hslotRange hrecipient hcommand
      rcases hallowed with hwait | ⟨id, hdeliver⟩
      · exact Or.inl hwait
      · exact Or.inr ⟨recipient, id, hdeliver⟩
    · intro offset hoffset
      constructor
      · omega
      · rw [hcount] at hoffset
        omega
  have hprincipal : ∀ actor, (final.principalHistory actor).length =
      (execution.principalHistory actor).length + if actor ∈ roster then 3 else 0 := by
    intro actor
    have hlength := runtime.application.runPolicies_principalHistory_length actor players
      (runtime.deliveryBlockEnvironment roster recipients) _ execution final hfinal
    calc
      _ = (execution.principalHistory actor).length +
          (deliveryPreparation roster recipients).countP (fun invocation =>
            match invocation with
            | .player who => decide (who = actor)
            | .environment => false) := hlength
      _ = _ := congrArg ((execution.principalHistory actor).length + ·)
        (deliveryPreparation_player_count roster recipients hroster actor)
  have henvironment := runtime.application.runPolicies_environmentHistory_length players
    (runtime.deliveryBlockEnvironment roster recipients) _ execution final hfinal
  rw [deliveryPreparation_environment_count roster recipients] at henvironment
  exact ⟨hpublic.1, hpublic.2, hfresh.of_publicState_eq hpublic.2,
    runtime.runPolicies_consistent players _ _ execution final hconsistent hfinal,
    hprincipal, henvironment⟩

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.runPolicies_deliveryPreparation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_deliveryPreparation
