/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingRestrictedAliceSupport
import VegasTests.MonitoredGuessingSourceInformation

/-! # Source policies represented in the restricted native game

The translation uses the source receiver lottery and the sender lottery at each
source observation. Normalization gives a legal response at every native input,
including inputs that no restricted execution can reach.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

def normalizedChoice (who : Player) (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) (event : nativeGraph.EventId) (handle : Handle nativeGraph)
    (value disclose : Bool) : nativeApp.Action :=
  if disclose then opening who past view event handle value else nativeSilent

open Classical in
def responsePolicy (guesses : FinDist Bool) (disclosures : Bool → Bool → FinDist Bool)
    (who : Player) : nativeApp.Policy := fun past view =>
  if who = watcher then FinDist.pure (nativeWatcherResponse view)
  else if who = bob ∧ view.application.publicView.serviceGrant = some bobPublication then
    guesses.map (normalizedChoice who past view bobPublication bobHandle true)
  else if who = alice ∧ view.application.publicView.serviceGrant = some alicePublication then
    let input := decodeAliceInput (some (past, view))
    (disclosures input.1 input.2).map
      (normalizedChoice who past view alicePublication aliceHandle (observedAliceBit view))
  else FinDist.pure nativeSilent

theorem responsePolicy_covered (guesses : FinDist Bool)
    (disclosures : Bool → Bool → FinDist Bool) (who : Player)
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView)
    (response : nativeApp.Action)
    (supported : response ∈ (responsePolicy guesses disclosures who past view).support) :
    response ∈ restrictedMenu.actions who past view := by
  classical
  unfold responsePolicy at supported
  change response ∈ (if who = watcher then _ else _) at ⊢
  split at supported
  · rename_i same
    rw [ite_eq_left same, Finset.mem_singleton]
    exact FinDist.mem_support_pure.mp supported
  · rename_i different
    rw [ite_eq_right different]
    unfold ordinaryActions
    split at supported
    · rename_i granted
      rw [ite_eq_left granted]
      obtain ⟨choice, _, rfl⟩ := FinDist.support_map .. ▸ supported
      cases choice <;> simp [normalizedChoice]
    · rename_i notBob
      rw [ite_eq_right notBob]
      split at supported
      · rename_i granted
        rw [ite_eq_left granted]
        obtain ⟨choice, _, rfl⟩ := FinDist.support_map .. ▸ supported
        cases choice <;> simp [normalizedChoice]
      · rename_i notAlice
        rw [ite_eq_right notAlice, Finset.mem_singleton]
        exact FinDist.mem_support_pure.mp supported

def responseProfile (guesses : FinDist Bool) (disclosures : Bool → Bool → FinDist Bool) :
    Profile restrictedModel.behavioralSignature := fun who =>
  restrictedMenu.restrictPolicy nativeInitialLaw nativeHorizon nativeScheduler who
    (responsePolicy guesses disclosures who) (fun _ _ _ _ supported =>
      responsePolicy_covered guesses disclosures who _ _ _ supported)

theorem decode_responseProfile (guesses : FinDist Bool)
    (disclosures : Bool → Bool → FinDist Bool) :
    restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler
      (responseProfile guesses disclosures) = responsePolicy guesses disclosures := by
  funext who
  exact restrictedMenu.decode_restrictPolicy_of_covered nativeInitialLaw nativeHorizon
    nativeScheduler who _ _ (responsePolicy_covered guesses disclosures who)

theorem responsePolicy_bob (guesses : FinDist Bool)
    (disclosures : Bool → Bool → FinDist Bool) (bit : Bool) :
    responsePolicy guesses disclosures bob ((quietBob bit).recall bob)
      ((quietBob bit).observe nativeApp bob) =
        guesses.map (choiceAction bobPublication bobHandle true) := by
  have different : bob ≠ watcher := by decide
  simp only [responsePolicy, different, ↓reduceIte]
  rw [ite_eq_left ⟨trivial, rfl⟩]
  congr 1
  funext choice
  cases choice <;> simp only [normalizedChoice, choiceAction, Bool.false_eq_true,
    ↓reduceIte, quiet_bob_opening]

theorem responsePolicy_alice (guesses : FinDist Bool)
    (disclosures : Bool → Bool → FinDist Bool) (bit guess : Bool) :
    responsePolicy guesses disclosures alice ((beforeAlice bit guess).recall alice)
      ((beforeAlice bit guess).observe nativeApp alice) =
        (disclosures bit guess).map (choiceAction alicePublication aliceHandle bit) := by
  have notWatcher : alice ≠ watcher := by decide
  have notBob : alice ≠ bob := by decide
  simp only [responsePolicy, notWatcher, notBob, false_and, ↓reduceIte]
  rw [ite_eq_left ⟨trivial, rfl⟩]
  change (disclosures (decodeAliceInput (aliceInput bit guess)).1
    (decodeAliceInput (aliceInput bit guess)).2).map _ = _
  rw [decode_alice_input]
  congr 1
  funext choice
  cases choice <;> simp only [normalizedChoice, choiceAction, Bool.false_eq_true,
    ↓reduceIte, before_alice_opening]

theorem responsePolicy_early_alice (guesses : FinDist Bool)
    (disclosures : Bool → Bool → FinDist Bool) (bit : Bool) :
    responsePolicy guesses disclosures alice ((aliceActivated bit).recall alice)
      ((aliceActivated bit).observe nativeApp alice) = FinDist.pure nativeSilent := by
  have notWatcher : alice ≠ watcher := by decide
  have notBob : alice ≠ bob := by decide
  simp only [responsePolicy, notWatcher, notBob, false_and, ↓reduceIte]
  rfl

theorem responsePolicy_watcher (guesses : FinDist Bool)
    (disclosures : Bool → Bool → FinDist Bool) :
    responsePolicy guesses disclosures watcher = nativeWatcherPolicy := by
  funext past view
  simp only [responsePolicy, ↓reduceIte]
  rfl

def sourceGuesses (profile : Profile sourceModel.behavioralSignature) : FinDist Bool :=
  sourceDecisionLaw profile bob sourceBobSite.1

def sourceDisclosures (profile : Profile sourceModel.behavioralSignature)
    (bit guess : Bool) : FinDist Bool :=
  sourceDecisionLaw profile alice (sourceAliceSite bit guess).1

def compile (profile : Profile sourceModel.behavioralSignature) :
    Profile restrictedModel.behavioralSignature :=
  responseProfile (sourceGuesses profile) (sourceDisclosures profile)

theorem compile_playerwise (first second : Profile sourceModel.behavioralSignature)
    (who : Player) (same : first who = second who) : compile first who = compile second who := by
  have policies : responsePolicy (sourceGuesses first) (sourceDisclosures first) who =
      responsePolicy (sourceGuesses second) (sourceDisclosures second) who := by
    funext past view
    fin_cases who
    · change first alice = second alice at same
      change responsePolicy _ _ alice past view = responsePolicy _ _ alice past view
      have disclosures : sourceDisclosures first = sourceDisclosures second := by
        funext bit guess
        simp only [sourceDisclosures, sourceDecisionLaw, sourceChoice, same]
      simp only [responsePolicy, show alice ≠ watcher by decide, show alice ≠ bob by decide,
        ↓reduceIte, false_and, disclosures]
    · change first bob = second bob at same
      change responsePolicy _ _ bob past view = responsePolicy _ _ bob past view
      have guesses : sourceGuesses first = sourceGuesses second := by
        simp only [sourceGuesses, sourceDecisionLaw, sourceChoice, same]
      simp only [responsePolicy, show bob ≠ watcher by decide, show bob ≠ alice by decide,
        ↓reduceIte, false_and, guesses]
    · change responsePolicy _ _ watcher past view = responsePolicy _ _ watcher past view
      rw [responsePolicy_watcher, responsePolicy_watcher]
  unfold compile responseProfile
  congr 1

end VegasTests.MonitoredGuessing.Restricted
