/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedOwnedPlayers
import Vegas.Compile.WindowedBlockIsolation

/-! # Paired execution through generated nonowner gates -/

noncomputable section

namespace Vegas.WindowedApplication.PolicyAgreement

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {runtime : WindowedApplication P L} {focal : P}
variable {left right : runtime.application.PolicyExecution}

/-- Equal public runtime state and block coordinates determine the same
environment command law; environment histories themselves need not agree. -/
theorem blockEnvironment_eq (agreement : PolicyAgreement runtime focal left right)
    (roster : List P) (hlength : left.environmentHistory.length = right.environmentHistory.length) :
    runtime.blockEnvironment roster left.environmentHistory
        (State.environmentView runtime.application left.native) =
      runtime.blockEnvironment roster right.environmentHistory
        (State.environmentView runtime.application right.native) := by
  simp only [WindowedApplication.blockEnvironment, hlength, State.environmentView,
    WindowedApplication.application, agreement.state.base.memory, agreement.state.active,
    agreement.pool, agreement.receipts]

/-- Count the scheduled polls of one principal. -/
def playerCountFor (actor : P) : @Invocation P → Bool
  | .player who => decide (who = actor)
  | .environment => false

/-- A player-only schedule that never polls the current instruction's
nonfocal owner preserves focal information. The focal raw policy is fixed and
pure; every other listed actor is blocked by the public ownership gate. -/
theorem runPolicies_players_gated
    (agreement : PolicyAgreement runtime focal left right)
    (replacement : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (base players : P → runtime.application.PlayerPolicy)
    (hfocal : players focal = fun history view => FinDist.pure (replacement history view))
    (hothers : ∀ actor, actor ≠ focal →
      players actor = runtime.blockPlayer actor (base actor))
    (instruction : ApplicationInstruction P L)
    (schedule : List (@Invocation P))
    (hplayers : ∀ invocation ∈ schedule, ∃ actor, invocation = .player actor)
    (hgate : ∀ actor, Invocation.player actor ∈ schedule → actor ≠ focal →
      instruction.submitter ≠ some actor)
    (environment : runtime.application.EnvironmentPolicy)
    (hplayerLengths : ∀ actor, (left.principalHistory actor).length =
      (right.principalHistory actor).length)
    (hplayerIndex : ∀ actor index, (left.principalHistory actor).length ≤ index →
      index < (left.principalHistory actor).length +
        schedule.countP (playerCountFor actor) →
      runtime.image.instructions[index / 3]? = some instruction)
    (finalLeft finalRight : runtime.application.PolicyExecution)
    (hleft : finalLeft ∈
      (runtime.application.runPolicies players environment schedule left).support)
    (hright : finalRight ∈
      (runtime.application.runPolicies players environment schedule right).support) :
    PolicyAgreement runtime focal finalLeft finalRight := by
  induction schedule generalizing left right with
  | nil =>
      simp only [MessageApplication.runPolicies, FinDist.mem_support_pure] at hleft hright
      subst finalLeft
      subst finalRight
      exact agreement
  | cons invocation rest ih =>
      obtain ⟨actor, rfl⟩ := hplayers invocation List.mem_cons_self
      simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion]
        at hleft hright
      obtain ⟨middleLeft, hfirstLeft, hleft⟩ := hleft
      obtain ⟨middleRight, hfirstRight, hright⟩ := hright
      have hfirst := agreement.invoke_player_gated actor replacement base players
        hfocal hothers environment environment instruction
        (fun hother => hgate actor List.mem_cons_self hother)
        (hplayerLengths actor)
        (hplayerIndex actor _ (Nat.le_refl _) (by simp [playerCountFor]))
        middleLeft middleRight hfirstLeft hfirstRight
      have hprefixLeft : middleLeft ∈
          (runtime.application.runPolicies players environment [.player actor] left).support := by
        simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hfirstLeft
      have hprefixRight : middleRight ∈
          (runtime.application.runPolicies players environment [.player actor] right).support := by
        simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hfirstRight
      have hcounts := runtime.application.runPolicies_principalHistory_length
      apply ih hfirst
        (fun invocation hinv => hplayers invocation (List.mem_cons_of_mem _ hinv))
        (fun candidate hinv hother =>
          hgate candidate (List.mem_cons_of_mem _ hinv) hother) _ _ hleft hright
      · intro candidate
        rw [hcounts candidate players environment [.player actor] left middleLeft hprefixLeft,
          hcounts candidate players environment [.player actor] right middleRight hprefixRight,
          hplayerLengths]
      · intro candidate index hlo hhi
        have hlength := hcounts candidate players environment [.player actor]
          left middleLeft hprefixLeft
        change (middleLeft.principalHistory candidate).length =
          (left.principalHistory candidate).length +
            [Invocation.player actor].countP (playerCountFor candidate) at hlength
        rw [hlength] at hhi
        apply hplayerIndex candidate index
        · omega
        · change index < (left.principalHistory candidate).length +
            ([Invocation.player actor] ++ rest).countP (playerCountFor candidate)
          rw [List.countP_append]
          simpa only [Nat.add_assoc] using hhi

/-- Once a block address is inactive, its synchronized environment invocation
is a wait on both sides. Equality of public state and the environment-history
coordinate determines the same gate without equating the histories. -/
theorem invoke_environment_inactive
    (agreement : PolicyAgreement runtime focal left right)
    (roster : List P) (players : P → runtime.application.PlayerPolicy)
    (instruction : ApplicationInstruction P L)
    (hindex : runtime.image.instructions[left.environmentHistory.length /
      (roster.length + 2)]? = some instruction)
    (hlength : left.environmentHistory.length = right.environmentHistory.length)
    (hinactive : runtime.image.activeAddress? left.native.application.base.memory ≠
      some instruction.address)
    (nextLeft nextRight : runtime.application.PolicyExecution)
    (hleft : nextLeft ∈ (runtime.application.invoke players
      (runtime.blockEnvironment roster) left .environment).support)
    (hright : nextRight ∈ (runtime.application.invoke players
      (runtime.blockEnvironment roster) right .environment).support) :
    PolicyAgreement runtime focal nextLeft nextRight := by
  have hpolicies := agreement.blockEnvironment_eq roster hlength
  have hleftWait := runtime.blockEnvironment_inactive roster left.environmentHistory
    (State.environmentView runtime.application left.native) instruction hindex hinactive
  have hrightWait := hpolicies.symm.trans hleftWait
  simp only [MessageApplication.invoke, hleftWait, hrightWait, FinDist.pure_bind] at hleft hright
  exact agreement.environmentPolicyStep_wait nextLeft nextRight hleft hright

/-- Synchronized supported suffixes preserve focal agreement after a generated
instruction has become inactive. The focal raw policy remains arbitrary and
pure; every nonfocal policy is gated away from the instruction. -/
theorem runPolicies_inactive_gated
    (agreement : PolicyAgreement runtime focal left right)
    (roster : List P)
    (replacement : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (base players : P → runtime.application.PlayerPolicy)
    (hfocal : players focal = fun history view => FinDist.pure (replacement history view))
    (hothers : ∀ actor, actor ≠ focal →
      players actor = runtime.blockPlayer actor (base actor))
    (instruction : ApplicationInstruction P L)
    (hgate : ∀ actor, actor ≠ focal → instruction.submitter ≠ some actor)
    (schedule : List (@Invocation P))
    (hplayerLengths : ∀ actor, (left.principalHistory actor).length =
      (right.principalHistory actor).length)
    (henvironmentLength : left.environmentHistory.length = right.environmentHistory.length)
    (hplayerIndex : ∀ actor index, (left.principalHistory actor).length ≤ index →
      index < (left.principalHistory actor).length +
        schedule.countP (fun call => match call with
          | .player who => decide (who = actor)
          | .environment => false) →
      runtime.image.instructions[index / 3]? = some instruction)
    (henvironmentIndex : ∀ index, left.environmentHistory.length ≤ index →
      index < left.environmentHistory.length + schedule.countP Invocation.isEnvironment →
      runtime.image.instructions[index / (roster.length + 2)]? = some instruction)
    (hinactive : runtime.image.activeAddress? left.native.application.base.memory ≠
      some instruction.address)
    (finalLeft finalRight : runtime.application.PolicyExecution)
    (hleft : finalLeft ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) schedule left).support)
    (hright : finalRight ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) schedule right).support) :
    PolicyAgreement runtime focal finalLeft finalRight := by
  induction schedule generalizing left right with
  | nil =>
      simp only [MessageApplication.runPolicies, FinDist.mem_support_pure] at hleft hright
      subst finalLeft
      subst finalRight
      exact agreement
  | cons invocation rest ih =>
      simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion]
        at hleft hright
      obtain ⟨middleLeft, hfirstLeft, hleft⟩ := hleft
      obtain ⟨middleRight, hfirstRight, hright⟩ := hright
      have hfirst : PolicyAgreement runtime focal middleLeft middleRight := by
        cases invocation with
        | player actor =>
            exact agreement.invoke_player_gated actor replacement base players hfocal hothers
              (runtime.blockEnvironment roster) (runtime.blockEnvironment roster) instruction
              (hgate actor) (hplayerLengths actor)
              (hplayerIndex actor _ (Nat.le_refl _) (by simp))
              middleLeft middleRight hfirstLeft hfirstRight
        | environment =>
            exact agreement.invoke_environment_inactive roster players instruction
              (henvironmentIndex _ (Nat.le_refl _) (by simp [Invocation.isEnvironment]))
              henvironmentLength hinactive middleLeft middleRight hfirstLeft hfirstRight
      have hprefixLeft : middleLeft ∈ (runtime.application.runPolicies players
          (runtime.blockEnvironment roster) [invocation] left).support := by
        simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hfirstLeft
      have hprefixRight : middleRight ∈ (runtime.application.runPolicies players
          (runtime.blockEnvironment roster) [invocation] right).support := by
        simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hfirstRight
      have hleftCounts := runtime.application.runPolicies_principalHistory_length
      have hleftEnv := runtime.application.runPolicies_environmentHistory_length players
        (runtime.blockEnvironment roster) [invocation] left middleLeft hprefixLeft
      have hrightEnv := runtime.application.runPolicies_environmentHistory_length players
        (runtime.blockEnvironment roster) [invocation] right middleRight hprefixRight
      have hmiddleInactive : runtime.image.activeAddress?
          middleLeft.native.application.base.memory ≠ some instruction.address := by
        have hpublic := runtime.runPolicies_block_inactive roster players [invocation]
          left middleLeft instruction (by
            intro index hlo hhi
            apply henvironmentIndex index hlo
            cases invocation <;>
              simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
                Bool.false_eq_true, ↓reduceIte] at hhi ⊢ <;> omega)
          hinactive hprefixLeft
        have hmemory : middleLeft.native.application.base.memory =
            left.native.application.base.memory :=
          congrArg (fun pair : ApplicationImage.Memory P L × Option (Activation Nat) => pair.1)
            hpublic
        intro hactive
        apply hinactive
        rwa [← hmemory]
      apply ih hfirst _ _ _ _ hmiddleInactive hleft hright
      · intro actor
        rw [hleftCounts actor players (runtime.blockEnvironment roster)
            [invocation] left middleLeft hprefixLeft,
          hleftCounts actor players (runtime.blockEnvironment roster)
            [invocation] right middleRight hprefixRight, hplayerLengths]
      · omega
      · intro actor index hlo hhi
        have hlength : (middleLeft.principalHistory actor).length =
            (left.principalHistory actor).length +
              [invocation].countP (fun call => match call with
                | .player who => decide (who = actor)
                | .environment => false) := by
          convert hleftCounts actor players (runtime.blockEnvironment roster)
            [invocation] left middleLeft hprefixLeft using 1
          rfl
        rw [hlength] at hhi
        apply hplayerIndex actor index
        · omega
        · change index < (left.principalHistory actor).length +
            ([invocation] ++ rest).countP (fun call => match call with
              | .player who => decide (who = actor)
              | .environment => false)
          rw [List.countP_append]
          omega
      · intro index hlo hhi
        apply henvironmentIndex index
        · omega
        · change index < left.environmentHistory.length +
            ([invocation] ++ rest).countP Invocation.isEnvironment
          rw [List.countP_append]
          omega

end Vegas.WindowedApplication.PolicyAgreement

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.runPolicies_players_gated'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.PolicyAgreement.runPolicies_players_gated

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.runPolicies_inactive_gated'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.PolicyAgreement.runPolicies_inactive_gated
