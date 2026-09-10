/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedApplicationPolicyLaws
import Interaction.MessageApplicationPolicyTrace
import Interaction.SealedBinding

/-! # Commitment persistence in complete policy traces

An occupied ideal-service slot at any selected release snapshot retains the
same value at the end of that very execution trace. The release predicate is
arbitrary; no monotonicity or progress property is required.
-/

noncomputable section

namespace Interaction.SealedProgram

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

/-- The native binding invariant lifts through every supported bounded policy
execution from an invariant initial shared state. -/
theorem runPolicies_bindingInvariant (program : SealedProgram Principal)
    (players : Principal → (program.messageApplication (Value := Value)).PlayerPolicy)
    (environment : (program.messageApplication (Value := Value)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (state : (program.messageApplication (Value := Value)).State)
    (execution : (program.messageApplication (Value := Value)).PolicyExecution)
    (invariant : BindingInvariant program (program.eraseReceipts state))
    (hmem : execution ∈
      ((program.messageApplication (Value := Value)).runPolicies players environment schedule
        (MessageApplication.PolicyExecution.initial _ state)).support) :
    BindingInvariant program (program.eraseReceipts execution.native) := by
  rw [runPolicies_eraseReceipts_eq_run_trace program players environment schedule state
    execution hmem]
  exact invariant.run (execution.nativeTrace.map program.nativeAction)

/-- Every first-release snapshot selected from an actual complete policy trace
satisfies the binding invariant when the initial shared state does. -/
theorem tracePolicies_firstRelease_bindingInvariant (program : SealedProgram Principal)
    (players : Principal → (program.messageApplication (Value := Value)).PlayerPolicy)
    (environment : (program.messageApplication (Value := Value)).EnvironmentPolicy)
    (release : (program.messageApplication (Value := Value)).PolicyExecution → Bool)
    (schedule : List (@MessageApplication.Invocation Principal))
    (state : (program.messageApplication (Value := Value)).State)
    (trace : (program.messageApplication (Value := Value)).PolicyTrace)
    (invariant : BindingInvariant program (program.eraseReceipts state))
    (htrace : trace ∈
      ((program.messageApplication (Value := Value)).tracePolicies players environment schedule
        (MessageApplication.PolicyExecution.initial _ state)).support) :
    BindingInvariant program (program.eraseReceipts (trace.firstRelease release).native) := by
  obtain ⟨front, _suffix, _hsplit, hprefix, _hsuffix⟩ :=
    (program.messageApplication (Value := Value)).tracePolicies_firstRelease_split
      players environment release schedule
      (MessageApplication.PolicyExecution.initial _ state) trace htrace
  exact runPolicies_bindingInvariant program players environment front state
    (trace.firstRelease release) invariant hprefix

/-- The last snapshot of every supported complete policy trace also satisfies
the initial shared state's binding invariant. -/
theorem tracePolicies_last_bindingInvariant (program : SealedProgram Principal)
    (players : Principal → (program.messageApplication (Value := Value)).PlayerPolicy)
    (environment : (program.messageApplication (Value := Value)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (state : (program.messageApplication (Value := Value)).State)
    (trace : (program.messageApplication (Value := Value)).PolicyTrace)
    (invariant : BindingInvariant program (program.eraseReceipts state))
    (htrace : trace ∈
      ((program.messageApplication (Value := Value)).tracePolicies players environment schedule
        (MessageApplication.PolicyExecution.initial _ state)).support) :
    BindingInvariant program (program.eraseReceipts trace.last.native) := by
  rw [← trace.firstRelease_false_eq_last]
  exact tracePolicies_firstRelease_bindingInvariant program players environment
    (fun _ => false) schedule state trace invariant htrace

/-- Every supported policy run preserves an already occupied sealed slot. -/
theorem runPolicies_lookup_of_eq_some (program : SealedProgram Principal)
    (players : Principal → (program.messageApplication (Value := Value)).PlayerPolicy)
    (environment : (program.messageApplication (Value := Value)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (execution next : (program.messageApplication (Value := Value)).PolicyExecution)
    (handle : CommitmentHandle Principal Nat) (value : Value)
    (hlookup : (program.eraseReceipts execution.native).service.lookup handle = some value)
    (hnext : next ∈
      ((program.messageApplication (Value := Value)).runPolicies players environment schedule
        execution).support) :
    (program.eraseReceipts next.native).service.lookup handle = some value := by
  obtain ⟨suffix, _htrace, hrun⟩ :=
    (program.messageApplication (Value := Value)).runPolicies_native_support
      players environment schedule execution next hnext
  have herased : program.eraseReceipts next.native ∈
      (((program.messageApplication (Value := Value)).run suffix execution.native).map
        program.eraseReceipts).support := by
    rw [FinDist.support_map]
    exact ⟨next.native, hrun, rfl⟩
  rw [program.run_eraseReceipts] at herased
  simp only [FinDist.mem_support_pure] at herased
  rw [herased]
  exact run_lookup_of_eq_some program (program.eraseReceipts execution.native)
    (suffix.map program.nativeAction) handle value hlookup

/-- An occupied slot at the start of a supported complete trace has the same
value in its last snapshot. -/
theorem tracePolicies_last_lookup_of_eq_some (program : SealedProgram Principal)
    (players : Principal → (program.messageApplication (Value := Value)).PlayerPolicy)
    (environment : (program.messageApplication (Value := Value)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (initial : (program.messageApplication (Value := Value)).PolicyExecution)
    (trace : (program.messageApplication (Value := Value)).PolicyTrace)
    (handle : CommitmentHandle Principal Nat) (value : Value)
    (htrace : trace ∈
      ((program.messageApplication (Value := Value)).tracePolicies players environment schedule
        initial).support)
    (hlookup : (program.eraseReceipts initial.native).service.lookup handle = some value) :
    (program.eraseReceipts trace.last.native).service.lookup handle = some value := by
  have hlast : trace.last ∈
      ((program.messageApplication (Value := Value)).runPolicies players environment schedule
        initial).support := by
    rw [← (program.messageApplication (Value := Value)).tracePolicies_last,
      FinDist.support_map]
    exact ⟨trace, htrace, rfl⟩
  exact runPolicies_lookup_of_eq_some program players environment schedule initial trace.last
    handle value hlookup hlast

/-- A value present at the first release-selected snapshot persists to the
last snapshot of the same supported complete policy trace. -/
theorem tracePolicies_firstRelease_lookup_persists (program : SealedProgram Principal)
    (players : Principal → (program.messageApplication (Value := Value)).PlayerPolicy)
    (environment : (program.messageApplication (Value := Value)).EnvironmentPolicy)
    (release : (program.messageApplication (Value := Value)).PolicyExecution → Bool)
    (schedule : List (@MessageApplication.Invocation Principal))
    (initial : (program.messageApplication (Value := Value)).PolicyExecution)
    (trace : (program.messageApplication (Value := Value)).PolicyTrace)
    (handle : CommitmentHandle Principal Nat) (value : Value)
    (htrace : trace ∈
      ((program.messageApplication (Value := Value)).tracePolicies players environment schedule
        initial).support)
    (hlookup : (program.eraseReceipts (trace.firstRelease release).native).service.lookup handle =
      some value) :
    (program.eraseReceipts trace.last.native).service.lookup handle = some value := by
  obtain ⟨_front, suffix, _hsplit, _hprefix, hsuffix⟩ :=
    (program.messageApplication (Value := Value)).tracePolicies_firstRelease_split
      players environment release schedule initial trace htrace
  exact runPolicies_lookup_of_eq_some program players environment suffix
    (trace.firstRelease release) trace.last handle value hlookup hsuffix

end Interaction.SealedProgram
