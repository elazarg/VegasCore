/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationHarmonic
import VegasTests.DisclosureOwnerSettlement

/-! # Public signal law under arbitrary disclosure policies -/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

/-- Before sampling, the continuation signal law is the source coin; after
sampling, it is the realized signal. -/
private def signalContinuation (state : DisclosureState) : FinDist Bool :=
  match state.signal with
  | none => fairCoin.denote
  | some signal => FinDist.pure signal

private def signalKernel (state : (application window).State) : FinDist Bool :=
  signalContinuation state.application

private theorem step_signal_harmonic (state : (application window).State)
    (action : (application window).Action) :
    ((application window).step state action).bind signalKernel = signalKernel state := by
  cases action with
  | privateCommand who command =>
      simp only [MessageApplication.step, FinDist.pure_bind]
      rfl
  | submit who payload =>
      simp only [MessageApplication.step, FinDist.pure_bind]
      rfl
  | replay who id =>
      simp only [MessageApplication.step, FinDist.pure_bind]
      rfl
  | deliver who id =>
      simp only [MessageApplication.step, FinDist.pure_bind]
      rfl
  | «include» id =>
      simp only [MessageApplication.step, FinDist.pure_bind]
      unfold signalKernel signalContinuation
      rw [(include_signal_fixed state id).1]
  | environment command =>
      cases command with
      | marker =>
          rw [MessageApplication.step, FinDist.bind_map]
          change (environmentStep state.application .marker).bind signalContinuation = _
          simp only [environmentStep, FinDist.pure_bind]
          split <;> rfl
      | advance clock =>
          rw [MessageApplication.step, FinDist.bind_map]
          change (environmentStep state.application (.advance clock)).bind
            signalContinuation = _
          simp only [environmentStep, FinDist.pure_bind]
          split <;> rfl
      | sample =>
          rw [MessageApplication.step, FinDist.bind_map]
          change (environmentStep state.application .sample).bind signalContinuation = _
          simp only [environmentStep]
          split
          · rename_i hsample
            have hnone : state.application.signal = none := by
              cases hsignal : state.application.signal <;> simp_all
            simp only [signalKernel, signalContinuation, hnone]
            rw [FinDist.bind_map]
            calc
              _ = fairCoin.denote.bind FinDist.pure := by
                apply FinDist.bind_congr
                intro signal _
                rfl
              _ = fairCoin.denote := FinDist.bind_pure _
          · rename_i hsample
            simp only [FinDist.pure_bind]
            cases state.application.signal <;> rfl

/-- Whenever a finite shared-runner execution has resolved the signal on all
of its support, the signal marginal is exactly the source fair coin. Policies,
the environment, and the invocation schedule are otherwise unrestricted. -/
theorem runPolicies_signal_law
    (players : TestPlayer → (application window).PlayerPolicy)
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (hresolved : ∀ next ∈ ((application window).runPolicies players environment schedule
        (MessageApplication.PolicyExecution.initial (application window)
          (initial window))).support,
      next.native.application.signal.isSome = true) :
    (((application window).runPolicies players environment schedule
        (MessageApplication.PolicyExecution.initial (application window)
          (initial window))).map
      (fun next => next.native.application.signal.getD false)) = fairCoin.denote := by
  let law := (application window).runPolicies players environment schedule
    (MessageApplication.PolicyExecution.initial (application window) (initial window))
  rw [FinDist.map_eq_bind]
  calc
    law.bind (fun next => FinDist.pure (next.native.application.signal.getD false)) =
        law.bind (fun next => signalKernel next.native) := by
      apply FinDist.bind_congr
      intro next hnext
      have hsome := hresolved next hnext
      cases hsignal : next.native.application.signal <;>
        simp_all [signalKernel, signalContinuation]
    _ = signalKernel (initial window) :=
      MessageApplication.runPolicies_harmonic (application window) signalKernel
        step_signal_harmonic players environment schedule _
    _ = fairCoin.denote := rfl

/-- The unchanged owner's resolving service supplies the support premise of
`runPolicies_signal_law`, so an arbitrary responder cannot bias the public
source signal. -/
theorem owner_service_signal_law (secret : Bool) (complete : Bool → Bool → Bool)
    (hwindow : 1 ≤ window)
    (players : TestPlayer → (application window).PlayerPolicy)
    (howner : players 0 = ownerPolicy (pureInitialDecision secret) (pureOpeningDecision complete))
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (hcycles : window + 3 ≤ cycles) :
    (((serviceGame window cycles selector).play players).map
      (fun next => next.native.application.signal.getD false)) = fairCoin.denote := by
  apply runPolicies_signal_law
  intro next hnext
  obtain ⟨signal, _, _, hsignal, _⟩ := owner_choices_preserved secret complete hwindow
    players howner selector hselector cycles (by omega) next hnext
  simp [hsignal]

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.runPolicies_signal_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runPolicies_signal_law

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.owner_service_signal_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms owner_service_signal_law

end VegasTests.OptionalDisclosure.DisclosureState
