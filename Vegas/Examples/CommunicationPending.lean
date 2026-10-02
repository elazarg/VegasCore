/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommunicationNative

/-! # A raw pending opening is not independently authenticated

The same claimed opening can be leaked under either immutable binding.
The sender deliberately requests no opening evidence. Bob cannot distinguish
a true uncertified claim from a false one. Certified packets instead carry
independently verifiable candidate evidence, tested in `ReactiveWitnessedEvidence`.
-/

noncomputable section

namespace Vegas.Examples.CommunicationPending

open Vegas Vegas.EventGraphRuntime Interaction
open SequentialValidation

def leaks : MessageNetwork.ObservationRule Bool (WitnessedPacket nativeGraph) :=
  fun _ _ => PMF.pure {(false, 0)}

private theorem initial_public_eq : (nativeStart true).publicView =
    (nativeStart false).publicView := by
  unfold State.publicView
  congr 1
  apply EventGraph.PublicObservation.ext
  · rfl
  · funext field
    cases field with
    | inl input => fin_cases input <;> rfl
    | inr event => rfl

private theorem initial_bob_eq :
    (nativeRuntime.reactiveApplication leaks).observePlayer (nativeStart true) true =
      (nativeRuntime.reactiveApplication leaks).observePlayer (nativeStart false) true := by
  dsimp only [reactiveApplication]
  congr 1
  · exact initial_public_eq
  · apply EventGraph.PlayerObservation.ext
    · rfl
    · funext field
      cases field with
      | inl input => fin_cases input <;> rfl
      | inr event => rfl
    · rfl
  · funext slot
    cases slot with
    | prepared serial => rfl
    | initial input => fin_cases input <;> rfl

def submittedClaim (bit : Bool) : (nativeRuntime.reactiveApplication leaks).Execution :=
  (ReactiveApplication.Execution.initial (nativeRuntime.reactiveApplication leaks)
    (nativeStart bit)).respond (nativeRuntime.reactiveApplication leaks) false
      ⟨some (.submit ⟨secretOpening true, .none⟩)⟩

def leakedClaim (bit : Bool) : (nativeRuntime.reactiveApplication leaks).Execution :=
  { submittedClaim bit with network := (submittedClaim bit).network.learn true {(false, 0)} }

theorem activation_view (bit : Bool) :
    ((submittedClaim bit).environmentStep (nativeRuntime.reactiveApplication leaks)
      (.activate true)).map
        (fun next => next.observe (nativeRuntime.reactiveApplication leaks) true) =
      PMF.pure
        ((leakedClaim bit).observe (nativeRuntime.reactiveApplication leaks) true) := by
  simp only [ReactiveApplication.Execution.environmentStep, reactiveApplication, leaks,
    PMF.pure_map]
  rfl

theorem same_view :
    (leakedClaim true).observe (nativeRuntime.reactiveApplication leaks) true =
      (leakedClaim false).observe (nativeRuntime.reactiveApplication leaks) true := by
  change ReactiveApplication.PlayerView.mk _ _ _ = ReactiveApplication.PlayerView.mk _ _ _
  congr 1
  exact initial_bob_eq

theorem claim_visible (bit : Bool) :
    ((leakedClaim bit).observe (nativeRuntime.reactiveApplication leaks) true).messages.leaked =
      [⟨(false, 0), ⟨(secretOpening true).packet, none, none⟩⟩] := by rfl

theorem actual_binding (bit : Bool) :
    (leakedClaim bit).application.candidates.lookup (false, .initial secretInput) =
      .openable ⟨.bool, bit⟩ := by rfl

def bobInformation (bit : Bool) :=
  ((leakedClaim bit).recall true,
    (leakedClaim bit).observe (nativeRuntime.reactiveApplication leaks) true)

theorem same_information : bobInformation true = bobInformation false := by
  change ([], _) = ([], _)
  rw [same_view]

/-- No function of the receiver view authenticates an uncertified claim in
both states. The sender's choice to omit evidence is available under either bit. -/
theorem no_view_verifier :
    ¬ ∃ verify : (List (nativeRuntime.reactiveApplication leaks).PlayerEntry ×
        (nativeRuntime.reactiveApplication leaks).PlayerView) → Bool,
      verify (bobInformation true) = true ∧ verify (bobInformation false) = false := by
  rintro ⟨verify, correct, incorrect⟩
  rw [same_information, incorrect] at correct
  cases correct

end Vegas.Examples.CommunicationPending
