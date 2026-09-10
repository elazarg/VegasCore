/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedController
import Interaction.MessageApplicationPolicyTrace

/-! # Trace law after the commit controller reaches its opening phase -/

noncomputable section

namespace Interaction.SealedProgram

open GameTheory GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

private theorem invoke_owner_history_length [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (players : Principal → (program.messageApplication (Value := Value)).PlayerPolicy)
    (environment : (program.messageApplication (Value := Value)).EnvironmentPolicy)
    (owner : Principal)
    (execution next : (program.messageApplication (Value := Value)).PolicyExecution)
    (invocation : @MessageApplication.Invocation Principal)
    (hlength : 2 ≤ (execution.principalHistory owner).length)
    (hnext : next ∈
      ((program.messageApplication (Value := Value)).invoke
        players environment execution invocation).support) :
    2 ≤ (next.principalHistory owner).length := by
  cases invocation with
  | environment =>
      simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨command, _, hstep⟩ := hnext
      have hhistory := MessageApplication.environmentStep_principalHistory
        (app := program.messageApplication (Value := Value)) execution command next hstep
      rw [congrFun hhistory owner]
      exact hlength
  | player who =>
      simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨command, _, hstep⟩ := hnext
      by_cases hwho : owner = who
      · subst who
        rw [(program.messageApplication (Value := Value)).playerStep_history_self
          owner execution command next hstep]
        simp only [List.length_append, List.length_singleton]
        omega
      · rw [(program.messageApplication (Value := Value)).playerStep_other_history
          who owner hwho execution command next hstep]
        exact hlength

/-- Once the owner's first two invocations are recorded, its complete
commit/open policy and its opening-only policy induce exactly the same complete
trace law on every remaining fixed schedule. -/
theorem tracePolicies_commitOpen_eq_opening_of_two_le
    [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (environment : (program.messageApplication (Value := Value)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution : (program.messageApplication (Value := Value)).PolicyExecution)
    (players : Profile (MessageApplication.policySignature Principal
      (program.messageApplication (Value := Value))))
    (owner : Principal) (commitNode revealNode : Nat) (value : Value)
    (hlength : 2 ≤ (execution.principalHistory owner).length) :
    (program.messageApplication (Value := Value)).tracePolicies
        (Profile.update (sig := MessageApplication.policySignature Principal
          (program.messageApplication (Value := Value))) players owner
          (commitOpenPolicy program owner commitNode revealNode value))
        environment schedule execution =
      (program.messageApplication (Value := Value)).tracePolicies
        (Profile.update (sig := MessageApplication.policySignature Principal
          (program.messageApplication (Value := Value))) players owner
          (openingPolicy program owner revealNode value))
        environment schedule execution := by
  induction schedule generalizing execution with
  | nil => rfl
  | cons invocation rest ih =>
      simp only [MessageApplication.tracePolicies]
      have hinvoke :
          (program.messageApplication (Value := Value)).invoke
              (Profile.update (sig := MessageApplication.policySignature Principal
                (program.messageApplication (Value := Value))) players owner
                (commitOpenPolicy program owner commitNode revealNode value))
              environment execution invocation =
            (program.messageApplication (Value := Value)).invoke
              (Profile.update (sig := MessageApplication.policySignature Principal
                (program.messageApplication (Value := Value))) players owner
                (openingPolicy program owner revealNode value))
              environment execution invocation := by
        cases invocation with
        | environment => rfl
        | player who =>
            by_cases hwho : who = owner
            · subst who
              simp only [MessageApplication.invoke, Profile.update_same]
              unfold commitOpenPolicy
              split <;> try omega
              rfl
            · simp [MessageApplication.invoke, Profile.update_of_ne _ _ hwho]
      rw [hinvoke]
      exact FinDist.bind_congr fun next hnext => by
        rw [ih next (invoke_owner_history_length program _ environment owner
          execution next invocation hlength hnext)]

end Interaction.SealedProgram
