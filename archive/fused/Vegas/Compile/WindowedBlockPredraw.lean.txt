/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPredraw
import Vegas.Compile.WindowedBlockDeterminism

/-! # Predrawing a randomized owner inside one polling block -/

noncomputable section

namespace Vegas.WindowedApplication

open Interaction Interaction.MessageApplication GameTheory GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A randomized raw replacement for the owner of an aligned block is a finite
mixture of pure raw policies. Every policy in that mixture makes the complete
native block execution a point mass; unchanged players retain their gated
reference policies in every branch. -/
theorem exists_pure_policy_mixture_block (runtime : WindowedApplication P L)
    (roster : List P) (hroster : roster.Nodup) (owner : P)
    (replacement : runtime.application.PlayerPolicy)
    (base players : P → runtime.application.PlayerPolicy)
    (hothers : ∀ actor, actor ≠ owner → players actor = runtime.blockPlayer actor (base actor))
    (instruction : ApplicationInstruction P L) (howner : instruction.submitter = some owner)
    (block : Nat) (execution : runtime.application.PolicyExecution)
    (hindex : runtime.image.instructions[block]? = some instruction)
    (hplayers : ∀ actor ∈ roster, (execution.principalHistory actor).length = 3 * block)
    (henvironment : execution.environmentHistory.length = block * (roster.length + 2)) :
    ∃ mixture : FinDist runtime.application.PlayerPolicy,
      (∀ purePolicy ∈ mixture.support,
        runtime.application.IsPurePlayerPolicy purePolicy) ∧
      mixture.bind (fun purePolicy => runtime.application.runPolicies
        (Profile.update
          (sig := MessageApplication.policySignature P runtime.application)
          players owner purePolicy)
        (runtime.blockEnvironment roster) (blockInvocations roster) execution) =
        runtime.application.runPolicies
          (Profile.update
            (sig := MessageApplication.policySignature P runtime.application)
            players owner replacement)
          (runtime.blockEnvironment roster) (blockInvocations roster) execution ∧
      ∀ purePolicy ∈ mixture.support, ∃ next,
        runtime.application.runPolicies
          (Profile.update
            (sig := MessageApplication.policySignature P runtime.application)
            players owner purePolicy)
          (runtime.blockEnvironment roster) (blockInvocations roster) execution =
          FinDist.pure next := by
  obtain ⟨mixture, hpure, hlaw⟩ :=
    runtime.application.exists_native_policy_mixture_runPolicies players
      (runtime.blockEnvironment roster) owner (blockInvocations roster) execution replacement
  refine ⟨mixture, hpure, ?_, ?_⟩
  · exact hlaw
  · intro purePolicy hpurePolicy
    let pureCommand history view := (hpure purePolicy hpurePolicy history view).choose
    have hpureCommand history view := (hpure purePolicy hpurePolicy history view).choose_spec
    apply runtime.runPolicies_block_eq_pure roster hroster owner pureCommand base
      (Profile.update
        (sig := MessageApplication.policySignature P runtime.application)
        players owner purePolicy)
    · simpa [Profile.update_same] using funext fun history =>
        funext fun view => hpureCommand history view
    · intro actor hactor
      simp [Profile.update_of_ne _ _ hactor, hothers actor hactor]
    · exact howner
    · exact hindex
    · exact hplayers
    · exact henvironment

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.exists_pure_policy_mixture_block' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.exists_pure_policy_mixture_block
