/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationOpeningService
import VegasTests.SelectiveAssociationCursor
import VegasTests.SelectiveAssociationPayoffs
import Interaction.ReactiveResponseEvaluation

/-! # Opening guarantees throughout native continuations

The guarantee starts at an arbitrary legal owner response, including off-path
histories. It uses the actual scheduler cursor and the full bounded raw menu.
Once the ordinary opening is included, all later choices preserve its result.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory.Protocol

theorem native_publication_owner (who : Player) :
    nativeOwner (nativePublicationEvent who) = who := by fin_cases who <;> rfl

theorem native_publication_invariant (who : Player) (result : PublicationResult Bool) :
    nativeApp.Invariant (fun state =>
      (nativePublicationRef who).get? state.config.store = some result) := by
  fin_cases who
  · exact nativeRuntime.reactiveStoreInvariant nativeLeaks (.inr alicePublication) result
  · exact nativeRuntime.reactiveStoreInvariant nativeLeaks (.inr bobPublication) result
  · exact nativeRuntime.reactiveStoreInvariant nativeLeaks (.inr carolPublication) result

theorem native_history_invariants (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) :
    control.execution.application.BindingInvariant ∧
      nativeBounds.AcceptedHandles control.execution.application ∧
      control.execution.network.SerialsBeforeNext := by
  let rawTrace := nativeMenu.toRawTrace (FinDist.pure nativeInitial) nativeHorizon
    nativeScheduler trace
  have binding := (nativeRuntime.reactiveBindingInvariant nativeLeaks).history
    (FinDist.pure nativeInitial) nativeHorizon nativeScheduler (by
      intro state member
      cases FinDist.mem_support_pure.mp member
      exact State.initial_bindingInvariant nativeInputs) rawTrace
  have bounded := nativeBounds.executionHandles_raw_history nativeRuntime nativeLeaks
    (FinDist.pure nativeInputs) nativeHorizon nativeScheduler (state := some control)
    (by rw [FinDist.map_pure]; exact trace)
  exact ⟨binding, bounded.1, nativeApp.serialsBeforeNext_history nativeScheduler
    (FinDist.pure nativeInitial) nativeHorizon rawTrace⟩

theorem native_opening_next_instruction (who : Player) :
    nativePlan[(nativeBeforeResponse (nativePublicationEvent who)).length + 1]? =
      some (.includeLatest (nativePublicationEvent who) who) := by
  fin_cases who <;> rfl

/-- An actual result of the reserved inclusion persists through every remaining
round. The response and publication result may be arbitrary. -/
theorem native_response_finish (players : Player → nativeApp.Policy)
    (control : nativeApp.Control) (trace : nativeArena.Trace (some control))
    (who : Player) (response : nativeApp.Action) (publication : PublicationResult Bool)
    (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent who))
    (chooses : players who (control.execution.recall who)
      (control.execution.observe nativeApp who) = FinDist.pure response)
    (included : ∀ middle ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest (nativePublicationEvent who) who)
      (control.execution.respond nativeApp who response)).support,
      (nativePublicationRef who).get? middle.application.config.store = some publication)
    (result : nativeApp.ProtocolState)
    (supported : result ∈ (nativeApp.finish (FinDist.pure nativeInitial) nativeHorizon
      nativeScheduler players (some control)).support) :
    ∃ final, result = some final ∧
      (nativePublicationRef who).get? final.execution.application.config.store =
        some publication := by
  have position := (native_decision_cursor (nativePublicationEvent who) control trace who active
    granted).2
  have ownerActive : control.actor = some (nativeOwner (nativePublicationEvent who)) := by
    rwa [native_publication_owner]
  obtain ⟨remainingAccount, _⟩ := native_decision_predecessor
    (nativePublicationEvent who) control trace ownerActive position
  have positive : 0 < control.remaining := by
    have beforeEnd : (nativeBeforeResponse (nativePublicationEvent who)).length + 1 <
        nativeHorizon := by fin_cases who <;> decide
    omega
  obtain ⟨remaining, remainingEq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  let responded := control.execution.respond nativeApp who response
  have nextRound : nativeApp.round nativeScheduler players responded =
      nativeRuntime.interactionStep nativeLeaks players nativeNetwork
        (.includeLatest (nativePublicationEvent who) who) responded := by
    have cursor : responded.environmentRecall.length =
        (nativeBeforeResponse (nativePublicationEvent who)).length + 1 := by
      rw [nativeApp.respond_environmentRecall]
      exact position
    simp only [ReactiveApplication.round, nativeScheduler, cursor,
      native_opening_next_instruction, interactionStep]
  simp only [ReactiveApplication.finish, active, ReactiveApplication.resume,
    ReactiveApplication.invoke, chooses, FinDist.map_pure, FinDist.pure_bind,
    remainingEq, ReactiveApplication.runRounds] at supported
  obtain ⟨final, finalMem, rfl⟩ := FinDist.support_map .. ▸ supported
  obtain ⟨middle, middleMem, finalMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ finalMem)
  change middle ∈ (nativeApp.round nativeScheduler players responded).support at middleMem
  rw [nextRound] at middleMem
  refine ⟨_, rfl, ?_⟩
  exact (ReactiveApplication.Invariant.policyInvariant nativeApp
    (native_publication_invariant who publication) players).runRounds
    nativeScheduler remaining middle final (included middle middleMem) finalMem

/-- Ordinary opening at a usable decision history forces successful publication
through the complete continuation, against arbitrary later response policies. -/
theorem native_opening_finish (players : Player → nativeApp.Policy)
    (control : nativeApp.Control) (trace : nativeArena.Trace (some control))
    (who : Player) (bit : Bool) (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent who))
    (unfinished : nativePublicationEvent who ∉ control.execution.application.config.cut.completed)
    (stored : (nativeBindingRef who).get? control.execution.application.config.store =
      some (.success bit))
    (opens : players who (control.execution.recall who)
      (control.execution.observe nativeApp who) =
        FinDist.pure (nativeOpeningResponse who (control.execution.observe nativeApp who)))
    (result : nativeApp.ProtocolState)
    (supported : result ∈ (nativeApp.finish (FinDist.pure nativeInitial) nativeHorizon
      nativeScheduler players (some control)).support) :
    ∃ final, result = some final ∧
      (nativePublicationRef who).get? final.execution.application.config.store =
        some (.success bit) := by
  have position := (native_decision_cursor (nativePublicationEvent who) control trace who active
    granted).2
  have ownerActive : control.actor = some (nativeOwner (nativePublicationEvent who)) := by
    rwa [native_publication_owner]
  obtain ⟨_, service⟩ := native_decision_service (nativePublicationEvent who) control trace
    ownerActive position
  obtain ⟨ready, timely⟩ := service.resolve_left unfinished
  obtain ⟨valid, bounded, serials⟩ := native_history_invariants control trace
  obtain ⟨opened, published, inclusion⟩ := native_opening_response_realizes players
    control.execution who bit valid bounded serials ready timely stored
  apply native_response_finish players control trace who _ (.success bit) active granted opens
    _ result supported
  intro middle middleMem
  have same : middle.application = opened := by
    apply FinDist.mem_support_pure.mp
    rw [← inclusion, FinDist.support_map]
    exact ⟨middle, middleMem, rfl⟩
  simpa only [same] using published

theorem native_opening_utility_lower (config : nativeGraph.Config) (who : Player) (bit : Bool)
    (stored : (nativePublicationRef who).get? config.store = some (.success bit)) :
    -1 ≤ utility (nativeResults config) who := by
  fin_cases who
  · change -1 ≤ utility (nativeResults config) alice
    have published : (nativeResults config).alice = .success bit := by
      change (alicePublicationRef.get? config.store).getD .failure = _
      change alicePublicationRef.get? config.store = some (.success bit) at stored
      rw [stored]
      rfl
    have lower := (utility_alice_success_bounds bit (nativeResults config).bob
      (nativeResults config).carol).1
    simpa only [utility_alice, published] using lower
  · change -1 ≤ utility (nativeResults config) bob
    have published : (nativeResults config).bob = .success bit := by
      change (bobPublicationRef.get? config.store).getD .failure = _
      change bobPublicationRef.get? config.store = some (.success bit) at stored
      rw [stored]
      rfl
    have lower := (utility_bob_success_bounds bit (nativeResults config).alice
      (nativeResults config).carol).1
    have nonnegative : 0 ≤ utility (nativeResults config) bob := by
      simpa only [utility_bob, published] using lower
    linarith
  · change -1 ≤ utility (nativeResults config) carol
    have published : (nativeResults config).carol = .success bit := by
      change (carolPublicationRef.get? config.store).getD .failure = _
      change carolPublicationRef.get? config.store = some (.success bit) at stored
      rw [stored]
      rfl
    have lower := (utility_carol_success_bounds bit (nativeResults config).alice
      (nativeResults config).bob).1
    have nonnegative : 0 ≤ utility (nativeResults config) carol := by
      simpa only [utility_carol, published] using lower
    linarith

def nativeOpeningChoice (who : Player) (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) : nativeModel.Choice who (some (past, view)) :=
  ⟨some (nativeOpeningResponse who view), nativeOpeningResponse who view,
    native_opening_response_available who past view, rfl⟩

theorem native_profile_opens
    (profile : ∀ who, nativeModel.BehavioralPolicy who) (who : Player)
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView)
    (opens : profile who (some (past, view)) = FinDist.pure (nativeOpeningChoice who past view)) :
    nativeMenu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon nativeScheduler profile
      who past view = FinDist.pure (nativeOpeningResponse who view) := by
  simp only [ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
    ReactiveApplication.ResponseMenu.embedPolicy, opens, FinDist.map_pure]
  rfl

/-- The legal opening deviation has a uniform payoff lower bound at every
compatible legal history; no positive-posterior premise is needed. -/
theorem native_opening_behavioral_lower
    (profile : ∀ who, nativeModel.BehavioralPolicy who)
    (control : nativeApp.Control) (trace : nativeArena.Trace (some control))
    (who : Player) (bit : Bool) (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent who))
    (unfinished : nativePublicationEvent who ∉ control.execution.application.config.cut.completed)
    (stored : (nativeBindingRef who).get? control.execution.application.config.store =
      some (.success bit))
    (opens : profile who (some (control.execution.recall who,
      control.execution.observe nativeApp who)) = FinDist.pure (nativeOpeningChoice who
        (control.execution.recall who) (control.execution.observe nativeApp who))) :
    -1 ≤ (nativeModel.runBehavioralFrom profile (2 * nativeHorizon + 1)
      ⟨some control, trace⟩).expect (fun history => nativeUtility who history.state) := by
  let players := nativeMenu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon
    nativeScheduler profile
  have law := nativeMenu.run_eq_finish (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
    profile (2 * nativeHorizon + 1) ⟨some control, trace⟩ (by
      change nativeApp.rank nativeHorizon (some control) ≤ 2 * nativeHorizon + 1
      have bound := nativeApp.trace_bound (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
        (nativeMenu.toRawTrace (FinDist.pure nativeInitial) nativeHorizon nativeScheduler trace)
      omega)
  rw [← FinDist.expect_map GameTheory.Protocol.ExecutionProtocol.History.state, law]
  let finished := nativeApp.finish (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
    players (some control)
  calc
    -1 = finished.expect (fun _ => -1) := (FinDist.expect_const _ _).symm
    _ ≤ finished.expect (nativeUtility who) := FinDist.expect_mono (by
      intro result supported
      obtain ⟨final, rfl, published⟩ := native_opening_finish players control trace who bit active
        granted unfinished stored (native_profile_opens profile who _ _ opens) result supported
      exact native_opening_utility_lower final.execution.application.config who bit published)

end VegasTests.SelectiveAssociation
