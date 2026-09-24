/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationNativeDeviationExecution

/-! # Completion of the actual selective-disclosure deviation -/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

/-- A checked local response guarantee applies at its actual calendar visit
and survives the remaining service rounds. -/
theorem native_reserved_result (players : Player → nativeApp.Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ nativeMenu.actions who past view)
    (event : nativeGraph.EventId) (priorRounds delay tail : Nat)
    (position : priorRounds + delay = (nativeBeforeResponse event).length)
    (P Q : nativeApp.Execution → Prop)
    (beforeInvariant : nativeApp.PolicyInvariant players P)
    (afterInvariant : nativeApp.PolicyInvariant players Q)
    (step : ∀ (control : nativeApp.Control), nativeArena.Trace (some control) →
      control.actor = some (nativeOwner event) →
      control.execution.application.serviceGrant = some event → P control.execution →
      ∀ response, response ∈ (players (nativeOwner event)
        (control.execution.recall (nativeOwner event))
        (control.execution.observe nativeApp (nativeOwner event))).support →
      ∀ next, next ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
        (.includeLatest event (nativeOwner event))
        (control.execution.respond nativeApp (nativeOwner event) response)).support → Q next)
    (execution final : nativeApp.Execution)
    (global : execution ∈
      (nativeApp.runRounds nativeScheduler players priorRounds nativeRoot).support)
    (valid : P execution)
    (supported : final ∈
      (nativeApp.runRounds nativeScheduler players (delay + (2 + tail)) execution).support) :
    Q final := by
  rw [ReactiveApplication.runRounds_add] at supported
  obtain ⟨before, beforeMem, afterMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  rw [ReactiveApplication.runRounds_add] at afterMem
  obtain ⟨after, included, finished⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ afterMem)
  have beforeGlobal := native_run_support_append players priorRounds delay execution before
    global beforeMem
  rw [position] at beforeGlobal
  obtain ⟨observed, response, observedMem, chosen, granted, ⟨trace⟩, included⟩ :=
    native_response_execution players covered event before after beforeGlobal included
  have observedValid := beforeInvariant.environment before observed
    (.activate (nativeOwner event))
    (beforeInvariant.runRounds nativeScheduler delay execution before valid beforeMem) observedMem
  have afterValid := step _ trace rfl granted observedValid response chosen after included
  exact afterInvariant.runRounds nativeScheduler tail after final afterValid finished

theorem native_alice_deviation_opening
    (profile : ∀ who, nativeModel.BehavioralPolicy who) (bit : Bool)
    (execution final : nativeApp.Execution)
    (global : execution ∈ (nativeApp.runRounds nativeScheduler
      (nativeAliceProfile (nativeMenu.decodeProfile (FinDist.pure nativeInitial)
        nativeHorizon nativeScheduler profile)) 13 nativeRoot).support)
    (stored : aliceBindingRef.get? execution.application.config.store = some (.success bit))
    (supported : final ∈ (nativeApp.runRounds nativeScheduler
      (nativeAliceProfile (nativeMenu.decodeProfile (FinDist.pure nativeInitial)
        nativeHorizon nativeScheduler profile)) 76 execution).support) :
    alicePublicationRef.get? final.application.config.store = some (.success bit) := by
  let players := nativeAliceProfile (nativeMenu.decodeProfile (FinDist.pure nativeInitial)
    nativeHorizon nativeScheduler profile)
  apply native_reserved_result players (native_alice_profile_covered profile) alicePublication
    13 9 65 rfl
    (fun current => aliceBindingRef.get? current.application.config.store = some (.success bit))
    (fun current => alicePublicationRef.get? current.application.config.store = some (.success bit))
    (ReactiveApplication.Invariant.policyInvariant nativeApp
      (native_binding_invariant alice (.success bit)) players)
    (ReactiveApplication.Invariant.policyInvariant nativeApp
      (native_publication_invariant alice (.success bit)) players)
    ?_ execution final global stored supported
  intro control trace active granted bound response chosen next reached
  have law : players alice (control.execution.recall alice)
      (control.execution.observe nativeApp alice) =
        FinDist.pure (nativeOpeningResponse alice (control.execution.observe nativeApp alice)) :=
    native_alice_opening _ _ granted
  change response ∈ (players alice (control.execution.recall alice)
    (control.execution.observe nativeApp alice)).support at chosen
  rw [law] at chosen
  cases FinDist.mem_support_pure.mp chosen
  obtain ⟨bindingValid, bounded, serials⟩ := native_history_invariants control trace
  have cursor := (native_decision_cursor alicePublication control trace alice active granted).2
  obtain ⟨_, available⟩ := native_decision_service alicePublication control trace active cursor
  have unfinished := native_decision_unfinished alicePublication control trace alice active granted
  obtain ⟨ready, timely⟩ := available.resolve_left unfinished
  obtain ⟨state, published, exactLaw⟩ := native_opening_response_realizes players
    control.execution alice bit bindingValid bounded serials ready timely bound
  have mapped : next.application ∈ (FinDist.pure state).support := by
    rw [← exactLaw, FinDist.support_map]
    exact ⟨next, reached, rfl⟩
  exact FinDist.mem_support_pure.mp mapped ▸ published

theorem native_deviation_bob_binding (assessment : nativeModel.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1))
    (bit : Bool) (execution final : nativeApp.Execution)
    (global : execution ∈ (nativeApp.runRounds nativeScheduler
      (nativeAliceProfile (nativeMenu.decodeProfile (FinDist.pure nativeInitial)
        nativeHorizon nativeScheduler assessment.strategy)) 13 nativeRoot).support)
    (observed : execution.application.BindingInvariant ∧
      nativeRuntime.bindingEvidenceObserved nativeLeaks (execution.observe nativeApp bob)
        (aliceBindingEvidence bit))
    (supported : final ∈ (nativeApp.runRounds nativeScheduler
      (nativeAliceProfile (nativeMenu.decodeProfile (FinDist.pure nativeInitial)
        nativeHorizon nativeScheduler assessment.strategy)) 3 execution).support) :
    bobBindingRef.get? final.application.config.store = some (.success bit) := by
  let players := nativeAliceProfile (nativeMenu.decodeProfile (FinDist.pure nativeInitial)
    nativeHorizon nativeScheduler assessment.strategy)
  apply native_reserved_result players (native_alice_profile_covered assessment.strategy)
    bobBinding 13 1 0 rfl
    (fun current => current.application.BindingInvariant ∧
      nativeRuntime.bindingEvidenceObserved nativeLeaks (current.observe nativeApp bob)
        (aliceBindingEvidence bit))
    (fun current => bobBindingRef.get? current.application.config.store = some (.success bit))
    (nativeRuntime.observedBinding_policyInvariant nativeLeaks players bob
      (aliceBindingEvidence bit))
    (ReactiveApplication.Invariant.policyInvariant nativeApp
      (native_binding_invariant bob (.success bit)) players)
    ?_ execution final global observed supported
  intro control trace active granted seen response chosen next reached
  apply native_supported_guess_inclusion assessment rational control trace active granted bit
    seen.2 response _ players next reached
  exact chosen

theorem native_deviation_bob_opening (assessment : nativeModel.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1))
    (bit : Bool) (execution final : nativeApp.Execution)
    (global : execution ∈ (nativeApp.runRounds nativeScheduler
      (nativeAliceProfile (nativeMenu.decodeProfile (FinDist.pure nativeInitial)
        nativeHorizon nativeScheduler assessment.strategy)) 16 nativeRoot).support)
    (stored : bobBindingRef.get? execution.application.config.store = some (.success bit))
    (supported : final ∈ (nativeApp.runRounds nativeScheduler
      (nativeAliceProfile (nativeMenu.decodeProfile (FinDist.pure nativeInitial)
        nativeHorizon nativeScheduler assessment.strategy)) 73 execution).support) :
    bobPublicationRef.get? final.application.config.store = some (.success bit) := by
  let players := nativeAliceProfile (nativeMenu.decodeProfile (FinDist.pure nativeInitial)
    nativeHorizon nativeScheduler assessment.strategy)
  apply native_reserved_result players (native_alice_profile_covered assessment.strategy)
    bobPublication 16 38 33 rfl
    (fun current => bobBindingRef.get? current.application.config.store = some (.success bit))
    (fun current => bobPublicationRef.get? current.application.config.store = some (.success bit))
    (ReactiveApplication.Invariant.policyInvariant nativeApp
      (native_binding_invariant bob (.success bit)) players)
    (ReactiveApplication.Invariant.policyInvariant nativeApp
      (native_publication_invariant bob (.success bit)) players)
    ?_ execution final global stored supported
  intro control trace active granted bound response chosen next reached
  apply native_supported_opening_inclusion assessment rational bob control trace active granted bit
    bound response _ players next reached
  exact chosen

end VegasTests.SelectiveAssociation
