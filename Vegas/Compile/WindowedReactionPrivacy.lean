/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedPolicyPrivacy
import Interaction.MessageApplicationEnvironmentCommands
import Interaction.MessageApplicationHistoryCounts

/-! # Information coupling through public delivery and reaction rounds -/

noncomputable section

namespace Vegas.WindowedApplication.PolicyAgreement

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {runtime : WindowedApplication P L} {focal : P}

/-- Synchronized delivery of the same identifier to the same recipients
preserves the focal policy input. The identifier may be missing; equal pools
make that outcome agree as well. -/
theorem runEnvironmentCommands_deliver_agreement
    {left right leftFinal rightFinal : runtime.application.PolicyExecution}
    (agreement : PolicyAgreement runtime focal left right)
    (id : MessageId P) (recipients : List P)
    (hleft : leftFinal ∈ (runtime.application.runEnvironmentCommands
      (recipients.map fun recipient => .deliver recipient id) left).support)
    (hright : rightFinal ∈ (runtime.application.runEnvironmentCommands
      (recipients.map fun recipient => .deliver recipient id) right).support) :
    PolicyAgreement runtime focal leftFinal rightFinal := by
  induction recipients generalizing left right with
  | nil =>
      simp only [List.map, MessageApplication.runEnvironmentCommands,
        FinDist.mem_support_pure] at hleft hright
      subst leftFinal
      subst rightFinal
      exact agreement
  | cons recipient rest ih =>
      simp only [List.map, MessageApplication.runEnvironmentCommands,
        FinDist.support_bind, Set.mem_iUnion] at hleft hright
      obtain ⟨leftDelivered, hleftDelivered, hleft⟩ := hleft
      obtain ⟨rightDelivered, hrightDelivered, hright⟩ := hright
      exact ih
        (agreement.environmentPolicyStep_deliver recipient id leftDelivered rightDelivered
          hleftDelivered hrightDelivered)
        hleft hright

/-- A player-only reaction sequence preserves agreement when the focal uses
one fixed pure raw policy and every nonfocal invocation waits. Policies may be
given on a larger player domain; only scheduled coordinates are constrained. -/
theorem runPolicies_reactions
    {left right leftFinal rightFinal : runtime.application.PolicyExecution}
    (agreement : PolicyAgreement runtime focal left right)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (hfocal : players focal = fun history view => FinDist.pure (command history view))
    (starts limits : P → Nat)
    (hothers : ∀ actor history view, actor ≠ focal →
      starts actor ≤ history.length → history.length < limits actor →
      players actor history view = FinDist.pure .wait)
    (schedule : List (@Invocation P))
    (henvironment : Invocation.environment ∉ schedule)
    (hleftRange : ∀ actor,
      starts actor ≤ (left.principalHistory actor).length ∧
        (left.principalHistory actor).length + schedule.countP (fun call =>
          match call with
          | .player who => decide (who = actor)
          | .environment => false) = limits actor)
    (hrightRange : ∀ actor,
      starts actor ≤ (right.principalHistory actor).length ∧
        (right.principalHistory actor).length + schedule.countP (fun call =>
          match call with
          | .player who => decide (who = actor)
          | .environment => false) = limits actor)
    (hleft : leftFinal ∈
      (runtime.application.runPolicies players environment schedule left).support)
    (hright : rightFinal ∈
      (runtime.application.runPolicies players environment schedule right).support) :
    PolicyAgreement runtime focal leftFinal rightFinal := by
  induction schedule generalizing left right with
  | nil =>
      simp only [MessageApplication.runPolicies, FinDist.mem_support_pure] at hleft hright
      subst leftFinal
      subst rightFinal
      exact agreement
  | cons invocation rest ih =>
      have hrest : Invocation.environment ∉ rest := fun hmem =>
        henvironment (List.mem_cons_of_mem invocation hmem)
      cases invocation with
      | environment => exact False.elim (henvironment List.mem_cons_self)
      | player actor =>
          simp only [MessageApplication.runPolicies, FinDist.support_bind,
            Set.mem_iUnion] at hleft hright
          obtain ⟨leftReacted, hleftReacted, hleft⟩ := hleft
          obtain ⟨rightReacted, hrightReacted, hright⟩ := hright
          have reactedAgreement :
              PolicyAgreement runtime focal leftReacted rightReacted := by
            by_cases heq : actor = focal
            · subst actor
              exact agreement.invoke_player_pure command players players environment environment
                hfocal hfocal leftReacted rightReacted hleftReacted hrightReacted
            · have hleftLt : (left.principalHistory actor).length < limits actor := by
                have := (hleftRange actor).2
                simp only [List.countP_cons, decide_true, ↓reduceIte] at this
                omega
              have hrightLt : (right.principalHistory actor).length < limits actor := by
                have := (hrightRange actor).2
                simp only [List.countP_cons, decide_true, ↓reduceIte] at this
                omega
              simp only [MessageApplication.invoke,
                hothers actor _ _ heq (hleftRange actor).1 hleftLt,
                hothers actor _ _ heq (hrightRange actor).1 hrightLt,
                FinDist.pure_bind] at hleftReacted hrightReacted
              exact agreement.playerStep_wait_other actor heq leftReacted rightReacted
                hleftReacted hrightReacted
          have hleftPrefix : leftReacted ∈
              (runtime.application.runPolicies players environment [Invocation.player actor]
                left).support := by
            simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hleftReacted
          have hrightPrefix : rightReacted ∈
              (runtime.application.runPolicies players environment [Invocation.player actor]
                right).support := by
            simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hrightReacted
          apply ih reactedAgreement hrest
          · intro candidate
            have hlength := runtime.application.runPolicies_principalHistory_length candidate
              players environment [Invocation.player actor] left leftReacted hleftPrefix
            constructor
            · rw [hlength]
              exact Nat.le_add_right_of_le (hleftRange candidate).1
            · rw [hlength]
              have := (hleftRange candidate).2
              by_cases heq : actor = candidate
              · subst candidate
                simp at this ⊢
                omega
              · simp [heq] at this ⊢
                omega
          · intro candidate
            have hlength := runtime.application.runPolicies_principalHistory_length candidate
              players environment [Invocation.player actor] right rightReacted hrightPrefix
            constructor
            · rw [hlength]
              exact Nat.le_add_right_of_le (hrightRange candidate).1
            · rw [hlength]
              have := (hrightRange candidate).2
              by_cases heq : actor = candidate
              · subst candidate
                simp at this ⊢
                omega
              · simp [heq] at this ⊢
                omega
          · exact hleft
          · exact hright

/-- A genuine public-delivery then player-reaction phase preserves focal
agreement. The focal sees its delivered inbox before selecting its reaction. -/
theorem deliveries_then_reactions
    {left right leftFinal rightFinal : runtime.application.PolicyExecution}
    (agreement : PolicyAgreement runtime focal left right)
    (id : MessageId P) (recipients : List P)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (hfocal : players focal = fun history view => FinDist.pure (command history view))
    (starts limits : P → Nat)
    (hothers : ∀ actor history view, actor ≠ focal →
      starts actor ≤ history.length → history.length < limits actor →
      players actor history view = FinDist.pure .wait)
    (reactions : List (@Invocation P))
    (henvironment : Invocation.environment ∉ reactions)
    (hleftRange : ∀ actor,
      starts actor ≤ (left.principalHistory actor).length ∧
        (left.principalHistory actor).length + reactions.countP (fun call =>
          match call with
          | .player who => decide (who = actor)
          | .environment => false) = limits actor)
    (hrightRange : ∀ actor,
      starts actor ≤ (right.principalHistory actor).length ∧
        (right.principalHistory actor).length + reactions.countP (fun call =>
          match call with
          | .player who => decide (who = actor)
          | .environment => false) = limits actor)
    (hleft : leftFinal ∈
      ((runtime.application.runEnvironmentCommands
        (recipients.map fun recipient => .deliver recipient id) left).bind fun delivered =>
        runtime.application.runPolicies players environment reactions delivered).support)
    (hright : rightFinal ∈
      ((runtime.application.runEnvironmentCommands
        (recipients.map fun recipient => .deliver recipient id) right).bind fun delivered =>
        runtime.application.runPolicies players environment reactions delivered).support) :
    PolicyAgreement runtime focal leftFinal rightFinal := by
  simp only [FinDist.support_bind, Set.mem_iUnion] at hleft hright
  obtain ⟨leftDelivered, hleftDelivered, hleft⟩ := hleft
  obtain ⟨rightDelivered, hrightDelivered, hright⟩ := hright
  have hleftHistory : ∀ actor, leftDelivered.principalHistory actor =
      left.principalHistory actor := fun actor =>
    runtime.application.runEnvironmentCommands_principalHistory _ left leftDelivered
      hleftDelivered actor
  have hrightHistory : ∀ actor, rightDelivered.principalHistory actor =
      right.principalHistory actor := fun actor =>
    runtime.application.runEnvironmentCommands_principalHistory _ right rightDelivered
      hrightDelivered actor
  have hleftDeliveredRange : ∀ actor,
      starts actor ≤ (leftDelivered.principalHistory actor).length ∧
        (leftDelivered.principalHistory actor).length + reactions.countP (fun call =>
          match call with
          | .player who => decide (who = actor)
          | .environment => false) = limits actor := by
    intro actor
    rw [hleftHistory actor]
    exact hleftRange actor
  have hrightDeliveredRange : ∀ actor,
      starts actor ≤ (rightDelivered.principalHistory actor).length ∧
        (rightDelivered.principalHistory actor).length + reactions.countP (fun call =>
          match call with
          | .player who => decide (who = actor)
          | .environment => false) = limits actor := by
    intro actor
    rw [hrightHistory actor]
    exact hrightRange actor
  exact (agreement.runEnvironmentCommands_deliver_agreement id recipients
    hleftDelivered hrightDelivered)
    |>.runPolicies_reactions command players environment hfocal starts limits hothers reactions
      henvironment hleftDeliveredRange hrightDeliveredRange hleft hright

end Vegas.WindowedApplication.PolicyAgreement

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.deliveries_then_reactions'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.PolicyAgreement.deliveries_then_reactions
