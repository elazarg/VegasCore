/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationOpeningService
import VegasTests.SelectiveAssociationReservedContinuation
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

variable {observation : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph)}
open GameTheory.Protocol

theorem native_publication_owner (who : Player) :
    nativeOwner (nativePublicationEvent who) = who := by fin_cases who <;> rfl

theorem native_publication_invariant (who : Player) (result : PublicationResult Bool) :
    (serviceApp observation).Invariant (fun state =>
      (nativePublicationRef who).get? state.config.store = some result) := by
  fin_cases who
  · exact nativeRuntime.reactiveStoreInvariant observation (.inr alicePublication) result
  · exact nativeRuntime.reactiveStoreInvariant observation (.inr bobPublication) result
  · exact nativeRuntime.reactiveStoreInvariant observation (.inr carolPublication) result

theorem native_history_invariants (control : (serviceApp observation).Control)
    (trace : (serviceArena observation).Trace (some control)) :
    control.execution.application.BindingInvariant ∧
      nativeBounds.AcceptedHandles control.execution.application ∧
      control.execution.network.SerialsBeforeNext := by
  let rawTrace := (serviceMenu observation).toRawTrace (FinDist.pure nativeInitial) nativeHorizon
    (serviceScheduler observation) trace
  have binding := (nativeRuntime.reactiveBindingInvariant observation).history
    (FinDist.pure nativeInitial) nativeHorizon (serviceScheduler observation) (by
      intro state member
      cases FinDist.mem_support_pure.mp member
      exact State.initial_bindingInvariant nativeInputs) rawTrace
  have bounded := nativeBounds.executionHandles_raw_history nativeRuntime observation
    (FinDist.pure nativeInputs) nativeHorizon (serviceScheduler observation) (state := some control)
    (by
      have initialLaw : (FinDist.pure nativeInputs).map State.initial =
          FinDist.pure nativeInitial := FinDist.map_pure _ _
      exact initialLaw.symm ▸ trace)
  exact ⟨binding, bounded.1, (serviceApp observation).serialsBeforeNext_history (serviceScheduler
    observation)
    (FinDist.pure nativeInitial) nativeHorizon rawTrace⟩

/-- An actual result of the reserved inclusion persists through every remaining
round. The response and publication result may be arbitrary. -/
theorem native_response_finish (players : Player → (serviceApp observation).Policy)
    (control : (serviceApp observation).Control) (trace : (serviceArena observation).Trace (some
      control))
    (who : Player) (response : (serviceApp observation).Action) (publication : PublicationResult
      Bool)
    (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent who))
    (chooses : players who (control.execution.recall who)
      (control.execution.observe (serviceApp observation) who) = FinDist.pure response)
    (included : ∀ middle ∈ (nativeRuntime.interactionStep observation players (serviceNetwork
      observation)
      (.includeLatest (nativePublicationEvent who) who)
      (control.execution.respond (serviceApp observation) who response)).support,
      (nativePublicationRef who).get? middle.application.config.store = some publication)
    (result : (serviceApp observation).ProtocolState)
    (supported : result ∈ ((serviceApp observation).finish (FinDist.pure nativeInitial)
      nativeHorizon
      (serviceScheduler observation) players (some control)).support) :
    ∃ final, result = some final ∧
      (nativePublicationRef who).get? final.execution.application.config.store =
        some publication := by
  have ownerActive : control.actor = some (nativeOwner (nativePublicationEvent who)) := by
    rwa [native_publication_owner]
  have exactResult := native_reserved_finish players control trace (nativePublicationEvent who)
    response (fun state => (nativePublicationRef who).get? state.config.store = some publication)
    (native_publication_invariant who publication) ownerActive granted
      (by simpa only [native_publication_owner] using chooses)
      (by simpa only [native_publication_owner] using included) result supported
  exact exactResult

/-- Ordinary opening at a usable decision history forces successful publication
through the complete continuation, against arbitrary later response policies. -/
theorem native_opening_finish (players : Player → (serviceApp observation).Policy)
    (control : (serviceApp observation).Control) (trace : (serviceArena observation).Trace (some
      control))
    (who : Player) (bit : Bool) (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent who))
    (unfinished : nativePublicationEvent who ∉ control.execution.application.config.cut.completed)
    (stored : (nativeBindingRef who).get? control.execution.application.config.store =
      some (.success bit))
    (opens : players who (control.execution.recall who)
      (control.execution.observe (serviceApp observation) who) =
        FinDist.pure (nativeOpeningResponse who (control.execution.observe (serviceApp observation)
          who)))
    (result : (serviceApp observation).ProtocolState)
    (supported : result ∈ ((serviceApp observation).finish (FinDist.pure nativeInitial)
      nativeHorizon
      (serviceScheduler observation) players (some control)).support) :
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

def nativeOpeningChoice (who : Player) (past : List (serviceApp observation).PlayerEntry)
    (view : (serviceApp observation).PlayerView) : (serviceModel observation).Choice who (some
      (past, view)) :=
  ⟨some (nativeOpeningResponse who view), nativeOpeningResponse who view,
    native_opening_response_available who past view, rfl⟩

theorem native_profile_opens
    (profile : ∀ who, (serviceModel observation).BehavioralPolicy who) (who : Player)
    (past : List (serviceApp observation).PlayerEntry) (view : (serviceApp observation).PlayerView)
    (opens : profile who (some (past, view)) = FinDist.pure (nativeOpeningChoice who past view)) :
    (serviceMenu observation).decodeProfile (FinDist.pure nativeInitial) nativeHorizon
      (serviceScheduler observation) profile
      who past view = FinDist.pure (nativeOpeningResponse who view) := by
  simp only [ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
    ReactiveApplication.ResponseMenu.embedPolicy, opens, FinDist.map_pure]
  rfl

/-- The legal opening deviation has a uniform payoff lower bound at every
compatible legal history; no positive-posterior premise is needed. -/
theorem native_opening_behavioral_lower
    (profile : ∀ who, (serviceModel observation).BehavioralPolicy who)
    (control : (serviceApp observation).Control) (trace : (serviceArena observation).Trace (some
      control))
    (who : Player) (bit : Bool) (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent who))
    (unfinished : nativePublicationEvent who ∉ control.execution.application.config.cut.completed)
    (stored : (nativeBindingRef who).get? control.execution.application.config.store =
      some (.success bit))
    (opens : profile who (some (control.execution.recall who,
      control.execution.observe (serviceApp observation) who)) = FinDist.pure (nativeOpeningChoice
        who
        (control.execution.recall who) (control.execution.observe (serviceApp observation) who))) :
    -1 ≤ ((serviceModel observation).runBehavioralFrom profile (2 * nativeHorizon + 1)
      ⟨some control, trace⟩).expect (fun history => nativeUtility who history.state) := by
  let players := (serviceMenu observation).decodeProfile (FinDist.pure nativeInitial) nativeHorizon
    (serviceScheduler observation) profile
  have law := (serviceMenu observation).run_eq_finish (FinDist.pure nativeInitial) nativeHorizon
    (serviceScheduler observation)
    profile (2 * nativeHorizon + 1) ⟨some control, trace⟩ (by
      change (serviceApp observation).rank nativeHorizon (some control) ≤ 2 * nativeHorizon + 1
      have bound := (serviceApp observation).trace_bound (FinDist.pure nativeInitial) nativeHorizon
        (serviceScheduler observation)
        ((serviceMenu observation).toRawTrace (FinDist.pure nativeInitial) nativeHorizon
          (serviceScheduler observation) trace)
      omega)
  let finished := (serviceApp observation).finish (FinDist.pure nativeInitial) nativeHorizon
    (serviceScheduler observation)
    players (some control)
  have expectation : ((serviceModel observation).runBehavioralFrom profile
      (2 * nativeHorizon + 1) ⟨some control, trace⟩).expect
        (fun history => nativeUtility who history.state) = finished.expect (nativeUtility who) := by
    exact (FinDist.expect_map _ _ _).symm.trans
      (congrArg (fun distribution => distribution.expect (nativeUtility who)) law)
  rw [expectation]
  calc
    -1 = finished.expect (fun _ => -1) := (FinDist.expect_const _ _).symm
    _ ≤ finished.expect (nativeUtility who) := FinDist.expect_mono (by
      intro result supported
      obtain ⟨final, rfl, published⟩ := native_opening_finish players control trace who bit active
        granted unfinished stored (native_profile_opens profile who _ _ opens) result supported
      exact native_opening_utility_lower final.execution.application.config who bit published)

end VegasTests.SelectiveAssociation
