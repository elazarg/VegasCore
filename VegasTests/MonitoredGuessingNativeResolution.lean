/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativeResponses
import Vegas.Pending.ReactiveAssociationPersistence
import Vegas.EventGraph.ResolutionProvenance
import Vegas.EventGraph.PrivateInputs

/-! # Fixed meanings and possible publications at every native history

These invariants permit every raw response in the native menu. Initial
bindings and their accepted handles remain fixed, and successful publication
cannot change their values.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def NativeFixed (bit : Bool) (state : State nativeGraph) : Prop :=
  state.Invariant (nativeInputs bit) ∧ state.BindingInvariant ∧
    state.accepted (.inl aliceInput) = some aliceHandle ∧
    state.accepted (.inl bobInput) = some bobHandle

theorem native_fixed_invariant (bit : Bool) : nativeApp.Invariant (NativeFixed bit) where
  submit state who material valid := by
    have a := (nativeRuntime.reactiveAssociationInvariant nativeLeaks
      (.inl aliceInput) aliceHandle).submit state who material ⟨valid.2.1, valid.2.2.1⟩
    have b := (nativeRuntime.reactiveAssociationInvariant nativeLeaks
      (.inl bobInput) bobHandle).submit state who material ⟨valid.2.1, valid.2.2.2⟩
    exact ⟨(nativeRuntime.reactiveStateInvariant nativeLeaks (nativeInputs bit)).submit
      state who material valid.1, a.1, a.2, b.2⟩
  handle state message next valid accepted := by
    have a := (nativeRuntime.reactiveAssociationInvariant nativeLeaks
      (.inl aliceInput) aliceHandle).handle state message next
        ⟨valid.2.1, valid.2.2.1⟩ accepted
    have b := (nativeRuntime.reactiveAssociationInvariant nativeLeaks
      (.inl bobInput) bobHandle).handle state message next
        ⟨valid.2.1, valid.2.2.2⟩ accepted
    exact ⟨(nativeRuntime.reactiveStateInvariant nativeLeaks (nativeInputs bit)).handle
      state message next valid.1 accepted, a.1, a.2, b.2⟩
  environment state command next valid reached := by
    have a := (nativeRuntime.reactiveAssociationInvariant nativeLeaks
      (.inl aliceInput) aliceHandle).environment state command next
        ⟨valid.2.1, valid.2.2.1⟩ reached
    have b := (nativeRuntime.reactiveAssociationInvariant nativeLeaks
      (.inl bobInput) bobHandle).environment state command next
        ⟨valid.2.1, valid.2.2.2⟩ reached
    exact ⟨(nativeRuntime.reactiveStateInvariant nativeLeaks (nativeInputs bit)).environment
      state command next valid.1 reached, a.1, a.2, b.2⟩

theorem native_initial_fixed (bit : Bool) : NativeFixed bit (nativeInitial bit) :=
  ⟨State.initial_invariant (nativeInputs bit), State.initial_bindingInvariant (nativeInputs bit),
    initial_alice_handle bit, initial_bob_handle bit⟩

theorem native_history_fixed (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) :
    ∃ bit, NativeFixed bit control.execution.application := by
  let invariant : nativeApp.Invariant (fun state => ∃ bit, NativeFixed bit state) := {
    submit := by
      rintro state who material ⟨bit, valid⟩
      exact ⟨bit, (native_fixed_invariant bit).submit state who material valid⟩
    handle := by
      rintro state message next ⟨bit, valid⟩ accepted
      exact ⟨bit, (native_fixed_invariant bit).handle state message next valid accepted⟩
    environment := by
      rintro state command next ⟨bit, valid⟩ reached
      exact ⟨bit, (native_fixed_invariant bit).environment state command next valid reached⟩ }
  exact invariant.history nativeInitialLaw nativeHorizon nativeScheduler (by
    intro state member
    obtain ⟨bit, _, rfl⟩ := FinDist.support_map .. ▸ member
    exact ⟨bit, native_initial_fixed bit⟩)
    (nativeMenu.toRawTrace nativeInitialLaw nativeHorizon nativeScheduler trace)

theorem NativeFixed.alice_stored {bit : Bool} {state : State nativeGraph}
    (valid : NativeFixed bit state) :
    aliceBindingRef.get? state.config.store = some (.success bit) := by
  have inputs := valid.1.reachable.inputs_eq
  change some (state.config.inputs aliceInput) = _
  rw [inputs]
  rfl

theorem NativeFixed.bob_stored {bit : Bool} {state : State nativeGraph}
    (valid : NativeFixed bit state) :
    bobBindingRef.get? state.config.store = some (.success true) := by
  have inputs := valid.1.reachable.inputs_eq
  change some (state.config.inputs bobInput) = _
  rw [inputs]
  rfl

theorem NativeFixed.alice_candidate {bit : Bool} {state : State nativeGraph}
    (valid : NativeFixed bit state) :
    state.candidates.lookup aliceHandle = .openable ⟨.bool, bit⟩ := by
  obtain ⟨candidate, accepted, _, verified⟩ :=
    valid.2.1.success_provenance aliceBindingRef bit valid.alice_stored
  change state.accepted (.inl aliceInput) = some candidate at accepted
  rw [valid.2.2.1] at accepted
  cases Option.some.inj accepted
  exact verified

theorem NativeFixed.bob_candidate {bit : Bool} {state : State nativeGraph}
    (valid : NativeFixed bit state) :
    state.candidates.lookup bobHandle = .openable ⟨.bool, true⟩ := by
  obtain ⟨candidate, accepted, _, verified⟩ :=
    valid.2.1.success_provenance bobBindingRef true valid.bob_stored
  change state.accepted (.inl bobInput) = some candidate at accepted
  rw [valid.2.2.2] at accepted
  cases Option.some.inj accepted
  exact verified

theorem NativeFixed.alice_publication {bit value : Bool} {state : State nativeGraph}
    (valid : NativeFixed bit state)
    (published : alicePublicationRef.get? state.config.store = some (.success value)) :
    value = bit := by
  have stored := valid.1.reachable.publication_binding alicePublication alice .bool
    aliceBindingRef [] rfl rfl value published
  rw [valid.alice_stored] at stored
  exact (PublicationResult.success.inj (Option.some.inj stored)).symm

theorem NativeFixed.bob_publication {bit value : Bool} {state : State nativeGraph}
    (valid : NativeFixed bit state)
    (published : bobPublicationRef.get? state.config.store = some (.success value)) :
    value = true := by
  have stored := valid.1.reachable.publication_binding bobPublication bob .bool
    bobBindingRef [] rfl rfl value published
  rw [valid.bob_stored] at stored
  exact (PublicationResult.success.inj (Option.some.inj stored)).symm

theorem NativeFixed.alice_results {bit : Bool} {state : State nativeGraph}
    (valid : NativeFixed bit state) :
    (nativeResults state.config).alice = .failure ∨
      (nativeResults state.config).alice = .success bit := by
  cases result : alicePublicationRef.get? state.config.store with
  | none => exact Or.inl (by simp [nativeResults, result])
  | some resultValue =>
      cases resultValue with
      | failure => exact Or.inl (by simp [nativeResults, result])
      | success value =>
          have same := valid.alice_publication result
          exact Or.inr (by simp [nativeResults, result, same])

theorem NativeFixed.bob_results {bit : Bool} {state : State nativeGraph}
    (valid : NativeFixed bit state) :
    (nativeResults state.config).bob = .failure ∨
      (nativeResults state.config).bob = .success true := by
  cases result : bobPublicationRef.get? state.config.store with
  | none => exact Or.inl (by simp [nativeResults, result])
  | some resultValue =>
      cases resultValue with
      | failure => exact Or.inl (by simp [nativeResults, result])
      | success value =>
          have same := valid.bob_publication result
          exact Or.inr (by simp [nativeResults, result, same])

theorem native_observed_alice_bit (bit : Bool) (execution : nativeApp.Execution)
    (valid : NativeFixed bit execution.application) :
    observedAliceBit (execution.observe nativeApp alice) = bit := by
  change (match execution.application.candidates.lookup aliceHandle with
    | .openable raw => (raw.as? .bool).getD false
    | _ => false) = _
  rw [valid.alice_candidate]
  rfl

theorem native_alice_response_eq (bit : Bool) (execution : nativeApp.Execution)
    (valid : NativeFixed bit execution.application)
    (grant : execution.application.serviceGrant = some alicePublication) :
    nativeAliceResponse (execution.observe nativeApp alice) =
      nativeOpeningAction alicePublication aliceHandle bit := by
  unfold nativeAliceResponse
  rw [native_observed_alice_bit bit execution valid]
  exact ite_eq_left grant

end VegasTests.MonitoredGuessing
