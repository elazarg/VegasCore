/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationNativeDeviationPayoff
import VegasTests.SelectiveAssociationResponseExecution
import Vegas.Pending.ReactiveAssociationPersistence

/-! # Certified bindings along the actual unilateral deviation -/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open ReactiveAssociationEvidence

theorem native_alice_profile_covered (profile : ∀ who, nativeModel.BehavioralPolicy who)
    (who : Player) (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView)
    (response : nativeApp.Action)
    (supported : response ∈ (nativeAliceProfile (nativeMenu.decodeProfile
      (FinDist.pure nativeInitial) nativeHorizon nativeScheduler profile) who past view).support) :
    response ∈ nativeMenu.actions who past view := by
  by_cases same : who = alice
  · subst who
    exact native_alice_available past view response supported
  · rw [nativeAliceProfile, Function.update_of_ne same] at supported
    exact native_decoded_covered profile who past view response supported

theorem native_carol_settlement_evidence (players : Player → nativeApp.Policy)
    (bit : Bool) (prior : nativeApp.Action) (final : nativeApp.Execution)
    (supported : final ∈ (nativeCarolPlay players bit prior).support) :
    final.application.BindingInvariant ∧ nativeRuntime.bindingEvidenceObserved nativeLeaks
      (final.observe nativeApp bob) (aliceBindingEvidence bit) := by
  obtain ⟨response, chosen, finished⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨trace⟩ := native_carol_raw_trace bit prior
  have valid : (carolSite bit prior).application.BindingInvariant :=
    (nativeRuntime.reactiveBindingInvariant nativeLeaks).history (FinDist.pure nativeInitial)
      nativeHorizon nativeScheduler (by
        intro state member
        cases FinDist.mem_support_pure.mp member
        exact State.initial_bindingInvariant nativeInputs) trace
  have invariant := nativeRuntime.observedBinding_policyInvariant nativeLeaks players bob
    (aliceBindingEvidence bit)
  have start := invariant.respond (carolSite bit prior) carol response
    ⟨valid, carolSite_evidence bit prior⟩ chosen
  apply invariant.runRounds nativeScheduler 4 _ final start
  rw [native_carol_guess_rounds]
  exact finished

theorem native_carol_settlement_alice (players : Player → nativeApp.Policy)
    (bit : Bool) (prior : nativeApp.Action) (final : nativeApp.Execution)
    (supported : final ∈ (nativeCarolPlay players bit prior).support) :
    aliceBindingRef.get? final.application.config.store = some (.success bit) := by
  obtain ⟨response, chosen, finished⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  have invariant := ReactiveApplication.Invariant.policyInvariant nativeApp
    (native_binding_invariant alice (.success bit)) players
  have start := invariant.respond (carolSite bit prior) carol response
    (carolSite_binding bit prior) chosen
  apply invariant.runRounds nativeScheduler 4 _ final start
  rw [native_carol_guess_rounds]
  exact finished

theorem native_deviation_settled_global (players : Player → nativeApp.Policy)
    (bit : Bool) (prior : nativeApp.Action)
    (priorMem : prior ∈ (players bob ((observed bit).recall bob)
      ((observed bit).observe nativeApp bob)).support)
    (settled : nativeApp.Execution)
    (settledMem : settled ∈ (nativeCarolPlay (nativeAliceProfile players) bit prior).support) :
    settled ∈ (nativeApp.runRounds nativeScheduler (nativeAliceProfile players)
      13 nativeRoot).support := by
  rw [native_alice_thirteen_rounds, FinDist.support_bind]
  apply Set.mem_iUnion₂.mpr
  refine ⟨bit, ?_, ?_⟩
  · exact FinDist.mem_support_uniformOfFintype bit
  · rw [FinDist.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨prior, priorMem, settledMem⟩

theorem native_run_support_append (players : Player → nativeApp.Policy)
    (count rest : Nat) (before after : nativeApp.Execution)
    (beforeMem : before ∈ (nativeApp.runRounds nativeScheduler players count nativeRoot).support)
    (afterMem : after ∈ (nativeApp.runRounds nativeScheduler players rest before).support) :
    after ∈ (nativeApp.runRounds nativeScheduler players (count + rest) nativeRoot).support := by
  rw [ReactiveApplication.runRounds_add, FinDist.support_bind]
  exact Set.mem_iUnion₂.mpr ⟨before, beforeMem, afterMem⟩

end VegasTests.SelectiveAssociation
