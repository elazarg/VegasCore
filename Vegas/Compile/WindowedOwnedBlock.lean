/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockDeterminism
import Vegas.Compile.WindowedGatedExecution
import Vegas.Compile.WindowedOwnedPrivacy

/-! # Paired execution of a focal player's service block

The environment consults the public application state, message pool, and its
history length. Its earlier private bookkeeping is irrelevant to command
selection. The focal raw policy receives its full actual history and view.
-/

noncomputable section

namespace Vegas.WindowedApplication.PolicyAgreement

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {runtime : WindowedApplication P L} {focal : P}
variable {left right : runtime.application.PolicyExecution}

/-- The actual service invocation preserves focal information in a focal-owned
block. An inactive block waits; an active one may include any selected packet
or advance the public clock. It cannot execute a source chance instruction. -/
theorem invoke_environment_owned (agreement : PolicyAgreement runtime focal left right)
    (roster : List P) (players : P → runtime.application.PlayerPolicy)
    (instruction : ApplicationInstruction P L)
    (howner : instruction.submitter = some focal)
    (hlookup : runtime.image.lookup instruction.address = some instruction)
    (hindex : runtime.image.instructions[left.environmentHistory.length /
      (roster.length + 2)]? = some instruction)
    (hconsistent : runtime.Consistent left.native.application)
    (hlength : left.environmentHistory.length = right.environmentHistory.length)
    (nextLeft nextRight : runtime.application.PolicyExecution)
    (hleft : nextLeft ∈ (runtime.application.invoke players (runtime.blockEnvironment roster)
      left .environment).support)
    (hright : nextRight ∈ (runtime.application.invoke players (runtime.blockEnvironment roster)
      right .environment).support) :
    PolicyAgreement runtime focal nextLeft nextRight := by
  have hpolicies := agreement.blockEnvironment_eq roster hlength
  by_cases hactive : runtime.image.activeAddress? left.native.application.base.memory =
      some instruction.address
  · have hmap := hconsistent.1.trans hactive
    obtain ⟨activation, hactivation⟩ : ∃ activation,
        left.native.application.active = some activation := by
      cases hactivation : left.native.application.active with
      | none => simp [hactivation] at hmap
      | some activation => exact ⟨activation, rfl⟩
    have hkey : activation.key = instruction.address := by
      simpa only [hactivation, Option.map_some, Option.some.injEq] using hmap
    obtain ⟨command, hcommand⟩ : ∃ command,
        runtime.blockEnvironment roster left.environmentHistory
          (State.environmentView runtime.application left.native) = FinDist.pure command :=
      ⟨_, rfl⟩
    have hrightCommand := hpolicies.symm.trans hcommand
    have hnoSample := runtime.blockEnvironment_noSample roster left.environmentHistory
      (State.environmentView runtime.application left.native) instruction focal hindex howner
      command (by rw [hcommand]; exact FinDist.mem_support_pure.mpr rfl)
    simp only [MessageApplication.invoke, hcommand, hrightCommand,
      FinDist.pure_bind] at hleft hright
    cases command with
    | «include» id =>
        exact agreement.environmentPolicyStep_include_of_active_submitter activation instruction
          hactivation hkey hactive hlookup howner id nextLeft nextRight hleft hright
    | deliver recipient id =>
        exact agreement.environmentPolicyStep_deliver recipient id nextLeft nextRight hleft hright
    | wait => exact agreement.environmentPolicyStep_wait nextLeft nextRight hleft hright
    | application command =>
        cases command with
        | sample address => exact False.elim (hnoSample address rfl)
        | advance clock =>
            exact agreement.environmentPolicyStep_advance clock nextLeft nextRight hleft hright
  · have hwait := runtime.blockEnvironment_inactive roster left.environmentHistory
      (State.environmentView runtime.application left.native) instruction hindex hactive
    have hrightWait := hpolicies.symm.trans hwait
    simp only [MessageApplication.invoke, hwait, hrightWait, FinDist.pure_bind] at hleft hright
    exact agreement.environmentPolicyStep_wait nextLeft nextRight hleft hright

/-- Synchronized supported executions of a focal-owned block suffix preserve
focal information. The two executions may differ in every other player's
hidden values and history entries; only the schedule's history lengths agree.
Every command of the fixed pure raw focal policy remains available. -/
theorem runPolicies_owned (agreement : PolicyAgreement runtime focal left right)
    (roster : List P)
    (replacement : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (base players : P → runtime.application.PlayerPolicy)
    (hfocal : players focal = fun history view => FinDist.pure (replacement history view))
    (hothers : ∀ actor, actor ≠ focal → players actor = runtime.blockPlayer actor (base actor))
    (instruction : ApplicationInstruction P L) (howner : instruction.submitter = some focal)
    (hlookup : runtime.image.lookup instruction.address = some instruction)
    (schedule : List (@Invocation P))
    (hconsistent : runtime.Consistent left.native.application)
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
              (fun hactor hsubmitter =>
                hactor (Option.some.inj (hsubmitter.symm.trans howner))) (hplayerLengths actor)
              (hplayerIndex actor _ (Nat.le_refl _) (by simp))
              middleLeft middleRight hfirstLeft hfirstRight
        | environment =>
            exact agreement.invoke_environment_owned roster players instruction howner hlookup
              (henvironmentIndex _ (Nat.le_refl _) (by simp [Invocation.isEnvironment]))
              hconsistent henvironmentLength middleLeft middleRight hfirstLeft hfirstRight
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
      apply ih hfirst
        (runtime.runPolicies_consistent players (runtime.blockEnvironment roster)
          [invocation] left middleLeft hconsistent hprefixLeft) _ _ _ _ hleft hright
      · intro actor
        rw [hleftCounts actor players (runtime.blockEnvironment roster)
            [invocation] left middleLeft hprefixLeft,
          hleftCounts actor players (runtime.blockEnvironment roster)
            [invocation] right middleRight hprefixRight, hplayerLengths]
      · omega
      · intro actor index hlo hhi
        have hlength : (middleLeft.principalHistory actor).length =
            (left.principalHistory actor).length + [invocation].countP
              (fun call => match call with
                | .player who => decide (who = actor)
                | .environment => false) :=
          hleftCounts actor players (runtime.blockEnvironment roster)
            [invocation] left middleLeft hprefixLeft
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

/-- The complete generated block discharges all instruction-range premises
from the roster counts and starting block coordinate. No source successor or
settlement witness is assumed. -/
theorem block_owned (agreement : PolicyAgreement runtime focal left right)
    (roster : List P) (hroster : roster.Nodup)
    (replacement : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (base players : P → runtime.application.PlayerPolicy)
    (hfocal : players focal = fun history view => FinDist.pure (replacement history view))
    (hothers : ∀ actor, actor ≠ focal → players actor = runtime.blockPlayer actor (base actor))
    (instruction : ApplicationInstruction P L) (howner : instruction.submitter = some focal)
    (hlookup : runtime.image.lookup instruction.address = some instruction)
    (block : Nat) (hindex : runtime.image.instructions[block]? = some instruction)
    (hconsistent : runtime.Consistent left.native.application)
    (hplayerLengths : ∀ actor, (left.principalHistory actor).length =
      (right.principalHistory actor).length)
    (henvironmentLength : left.environmentHistory.length = right.environmentHistory.length)
    (hplayers : ∀ actor ∈ roster, (left.principalHistory actor).length = 3 * block)
    (henvironment : left.environmentHistory.length = block * (roster.length + 2))
    (finalLeft finalRight : runtime.application.PolicyExecution)
    (hleft : finalLeft ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) (blockInvocations roster) left).support)
    (hright : finalRight ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) (blockInvocations roster) right).support) :
    PolicyAgreement runtime focal finalLeft finalRight := by
  apply agreement.runPolicies_owned roster replacement base players hfocal hothers instruction
    howner hlookup (blockInvocations roster) hconsistent hplayerLengths henvironmentLength
    _ _ finalLeft finalRight hleft hright
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
      Nat.div_eq_of_lt_le (by simpa [Nat.mul_comm] using hlo) (by nlinarith)
    rw [hquotient]
    exact hindex

end Vegas.WindowedApplication.PolicyAgreement

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.invoke_environment_owned' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.PolicyAgreement.invoke_environment_owned

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.runPolicies_owned' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.PolicyAgreement.runPolicies_owned

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.block_owned' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.PolicyAgreement.block_owned
