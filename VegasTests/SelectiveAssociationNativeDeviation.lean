/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationCarol
import Interaction.ReactiveMenuPolicy

/-! # A legal native strategy for selective disclosure

Alice privately randomizes a Boolean candidate on her initial response and
carries its opening evidence in that envelope. At her binding grant she
reoffers the same immutable candidate without evidence. At her publication
grant she chooses the ordinary available opening. All other responses are
silent; each response is in the full finite native menu at every input.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open ReactiveAssociationEvidence

def aliceCertifiedOffer (bit : Bool) : nativeApp.Action :=
  ⟨some (.submit ⟨⟨.commitment aliceBinding candidate, some ⟨.bool, bit⟩⟩,
    .owned (opening bit)⟩)⟩

def aliceAssociate : nativeApp.Action :=
  ⟨some (.submit ⟨⟨.commitment aliceBinding candidate, none⟩, .none⟩)⟩

theorem alice_certified_offer_available (bit : Bool)
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView) :
    aliceCertifiedOffer bit ∈ nativeMenu.actions alice past view := by
  change aliceCertifiedOffer bit ∈
    (nativeBounds.rawMenu nativeRuntime nativeLeaks).actions alice past view
  rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  change (⟨⟨.commitment aliceBinding candidate, some ⟨.bool, bit⟩⟩,
    .owned (opening bit)⟩ : WitnessedSubmission nativeGraph) ∈ nativeBounds.submissions _
  rw [MessageBounds.submissions_mem]
  have bounded : nativeBounds.AllowsHandle candidate := by change 0 < 2; decide
  have value : (⟨.bool, bit⟩ : Raw simpleExpr) ∈ nativeBounds.values := by cases bit <;> decide
  exact ⟨⟨bounded, value⟩, bounded, value⟩

theorem alice_associate_available (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) : aliceAssociate ∈ nativeMenu.actions alice past view := by
  change aliceAssociate ∈ (nativeBounds.rawMenu nativeRuntime nativeLeaks).actions alice past view
  rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  change (⟨⟨.commitment aliceBinding candidate, none⟩, .none⟩ :
    WitnessedSubmission nativeGraph) ∈ nativeBounds.submissions _
  rw [MessageBounds.submissions_mem]
  exact ⟨⟨by change 0 < 2; decide, trivial⟩, trivial⟩

def nativeAlicePolicy : nativeApp.Policy := fun past view =>
  match view.application.publicView.serviceGrant with
  | none => if past = [] then (FinDist.uniformOfFintype (α := Bool)).map aliceCertifiedOffer
      else FinDist.pure ⟨none⟩
  | some event =>
      if event = aliceBinding then FinDist.pure aliceAssociate
      else if event = alicePublication then FinDist.pure (nativeOpeningResponse alice view)
      else FinDist.pure ⟨none⟩

def nativeAliceProfile (players : Player → nativeApp.Policy) : Player → nativeApp.Policy :=
  Function.update players alice nativeAlicePolicy

theorem native_alice_available (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView)
    (action : nativeApp.Action) (supported : action ∈ (nativeAlicePolicy past view).support) :
    action ∈ nativeMenu.actions alice past view := by
  have silent : (⟨none⟩ : nativeApp.Action) ∈ nativeMenu.actions alice past view := by
    change (⟨none⟩ : nativeApp.Action) ∈
      (nativeBounds.rawMenu nativeRuntime nativeLeaks).actions alice past view
    rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
    trivial
  unfold nativeAlicePolicy at supported
  split at supported
  · split at supported
    · obtain ⟨bit, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact alice_certified_offer_available bit past view
    · cases FinDist.mem_support_pure.mp supported
      exact silent
  · split at supported
    · cases FinDist.mem_support_pure.mp supported
      exact alice_associate_available past view
    · split at supported
      · cases FinDist.mem_support_pure.mp supported
        exact native_opening_response_available alice past view
      · cases FinDist.mem_support_pure.mp supported
        exact silent

theorem native_alice_admissible : nativeMenu.Admissible (FinDist.pure nativeInitial)
    nativeHorizon nativeScheduler alice nativeAlicePolicy := by
  intro control _ _ action supported
  exact native_alice_available _ _ action supported

def nativeAliceBehavior : nativeModel.BehavioralPolicy alice :=
  nativeMenu.restrictPolicy (FinDist.pure nativeInitial) nativeHorizon nativeScheduler alice
    nativeAlicePolicy native_alice_admissible

theorem native_alice_initial :
    nativeAlicePolicy (activatedInitial.recall alice) (activatedInitial.observe nativeApp alice) =
      (FinDist.uniformOfFintype (α := Bool)).map aliceCertifiedOffer := rfl

theorem native_alice_association (execution : nativeApp.Execution) :
    nativeAlicePolicy ((beforeOffer execution).recall alice)
      ((beforeOffer execution).observe nativeApp alice) = FinDist.pure aliceAssociate := by
  simp [nativeAlicePolicy, beforeOffer, ReactiveApplication.Execution.observe,
    nativeApp, serviceApp, reactiveApplication, State.publicView, aliceBinding]

theorem native_alice_opening (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView)
    (granted : view.application.publicView.serviceGrant = some alicePublication) :
    nativeAlicePolicy past view = FinDist.pure (nativeOpeningResponse alice view) := by
  simp only [nativeAlicePolicy, granted]
  rw [ite_eq_right (by decide : alicePublication ≠ aliceBinding), ite_true]

theorem native_alice_first_round (players : Player → nativeApp.Policy) :
    nativeRuntime.interactionStep nativeLeaks (nativeAliceProfile players) nativeNetwork
      (.player alice) initial = (FinDist.uniformOfFintype (α := Bool)).map first := by
  simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
    ReactiveApplication.dispatch, initial_activation, FinDist.pure_bind,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume, ReactiveApplication.invoke,
    nativeAliceProfile, Function.update_self, native_alice_initial, FinDist.map_comp]
  rfl

theorem native_alice_bob_round (players : Player → nativeApp.Policy) (bit : Bool) :
    nativeRuntime.interactionStep nativeLeaks (nativeAliceProfile players) nativeNetwork
      (.player bob) (first bit) =
      (players bob ((observed bit).recall bob) ((observed bit).observe nativeApp bob)).map
        (reacted bit) := by
  simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
    ReactiveApplication.dispatch, activation_leaks_to_bob, FinDist.pure_bind,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume, ReactiveApplication.invoke,
    nativeAliceProfile, Function.update_of_ne (by decide : bob ≠ alice)]
  rfl

theorem native_alice_offer_rounds (players : Player → nativeApp.Policy)
    (bit : Bool) (response : nativeApp.Action) :
    nativeRuntime.runInteractionPlan nativeLeaks (nativeAliceProfile players) nativeNetwork
      [.grant aliceBinding, .player alice] (reacted bit response) =
      FinDist.pure (offeredAfter bit response) := by
  have law : (((reacted bit response).environmentStep nativeApp
      (.application (.grant aliceBinding))).bind fun next =>
      next.environmentStep nativeApp (.activate alice)) =
      FinDist.pure (beforeOffer (reacted bit response)) := beforeOffer_law _
  have combined : nativeRuntime.runInteractionPlan nativeLeaks (nativeAliceProfile players)
      nativeNetwork [.grant aliceBinding, .player alice] (reacted bit response) =
      (((reacted bit response).environmentStep nativeApp (.application (.grant aliceBinding))).bind
        fun next => next.environmentStep nativeApp (.activate alice)).bind
          (nativeApp.invoke (nativeAliceProfile players) alice) := by
    simp only [runInteractionPlan, FinDist.bind_pure, interactionStep, interactionInstruction,
      FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
      ReactiveApplication.resume, FinDist.bind_bind]
    rfl
  rw [combined, law, FinDist.pure_bind]
  simp only [ReactiveApplication.invoke, nativeAliceProfile, Function.update_self,
    native_alice_association, FinDist.map_pure]
  rfl

theorem native_alice_include_round (players : Player → nativeApp.Policy)
    (bit : Bool) (response : nativeApp.Action) :
    nativeRuntime.interactionStep nativeLeaks (nativeAliceProfile players) nativeNetwork
      (.includeLatest aliceBinding alice) (offeredAfter bit response) =
      FinDist.pure (includedAfter bit response) := by
  have selected : nativeRuntime.reactiveLatest nativeLeaks aliceBinding alice
      ((offeredAfter bit response).observeEnvironment nativeApp) = .include (alice, 1) :=
    later_envelope_selected bit response
  simp only [interactionStep, interactionInstruction, selected,
    FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
  change ((offeredAfter bit response).environmentStep nativeApp (.include (alice, 1))).bind
    FinDist.pure = _
  rw [FinDist.bind_pure]
  exact inclusion_law bit response

theorem native_alice_carol_rounds (players : Player → nativeApp.Policy)
    (bit : Bool) (response : nativeApp.Action) :
    nativeRuntime.runInteractionPlan nativeLeaks (nativeAliceProfile players) nativeNetwork
      [.tick, .expire aliceBinding, .grant carolBinding, .player carol]
        (includedAfter bit response) =
      (players carol ((carolSite bit response).recall carol)
        ((carolSite bit response).observe nativeApp carol)).map
          ((carolSite bit response).respond nativeApp carol) := by
  let observedPrefix := ((includedAfter bit response).environmentStep nativeApp
    (.application .advanceClock)).bind fun next =>
      (next.environmentStep nativeApp (.application (.expire aliceBinding))).bind fun next =>
        (next.environmentStep nativeApp (.application (.grant carolBinding))).bind fun next =>
          next.environmentStep nativeApp (.activate carol)
  have law : observedPrefix = FinDist.pure (carolSite bit response) := carolSite_law _ _
  have combined : nativeRuntime.runInteractionPlan nativeLeaks (nativeAliceProfile players)
      nativeNetwork [.tick, .expire aliceBinding, .grant carolBinding, .player carol]
        (includedAfter bit response) =
      observedPrefix.bind (nativeApp.invoke (nativeAliceProfile players) carol) := by
    dsimp only [observedPrefix]
    simp only [runInteractionPlan, FinDist.bind_pure, interactionStep, interactionInstruction,
      FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
      ReactiveApplication.resume, FinDist.bind_bind]
    rfl
  rw [combined, law, FinDist.pure_bind]
  simp only [ReactiveApplication.invoke, nativeAliceProfile,
    Function.update_of_ne (by decide : carol ≠ alice)]

theorem native_alice_after_bob (players : Player → nativeApp.Policy)
    (bit : Bool) (response : nativeApp.Action) :
    nativeRuntime.runInteractionPlan nativeLeaks (nativeAliceProfile players) nativeNetwork
      [.grant aliceBinding, .player alice, .includeLatest aliceBinding alice,
        .tick, .expire aliceBinding, .grant carolBinding, .player carol] (reacted bit response) =
      (players carol ((carolSite bit response).recall carol)
        ((carolSite bit response).observe nativeApp carol)).map
          ((carolSite bit response).respond nativeApp carol) := by
  change nativeRuntime.runInteractionPlan nativeLeaks (nativeAliceProfile players) nativeNetwork
    ([.grant aliceBinding, .player alice] ++
      [.includeLatest aliceBinding alice, .tick, .expire aliceBinding,
        .grant carolBinding, .player carol]) (reacted bit response) = _
  rw [runInteractionPlan_append, native_alice_offer_rounds, FinDist.pure_bind,
    runInteractionPlan, native_alice_include_round, FinDist.pure_bind]
  exact native_alice_carol_rounds players bit response

/-- Nine scheduler rounds include Carol's ordinary response. Her activation
input is exactly the concrete selectively informed prefix. -/
theorem native_alice_nine_rounds (players : Player → nativeApp.Policy) :
    nativeApp.runRounds nativeScheduler (nativeAliceProfile players) 9 nativeRoot =
      (FinDist.uniformOfFintype (α := Bool)).bind fun bit =>
        (players bob ((observed bit).recall bob) ((observed bit).observe nativeApp bob)).bind
          fun response => (players carol ((carolSite bit response).recall carol)
            ((carolSite bit response).observe nativeApp carol)).map
              ((carolSite bit response).respond nativeApp carol) := by
  have bridge := native_prefix_rounds (nativeAliceProfile players) (nativePlan.take 9)
    (nativePlan.drop 9) (List.take_append_drop 9 nativePlan).symm
  change nativeApp.runRounds nativeScheduler (nativeAliceProfile players) 9 nativeRoot = _ at bridge
  rw [bridge]
  change nativeRuntime.runInteractionPlan nativeLeaks (nativeAliceProfile players) nativeNetwork
    (.player alice :: .player bob :: [.grant aliceBinding, .player alice,
      .includeLatest aliceBinding alice, .tick, .expire aliceBinding,
      .grant carolBinding, .player carol]) initial = _
  rw [runInteractionPlan, native_alice_first_round, FinDist.bind_map]
  apply FinDist.bind_congr
  intro bit _
  rw [runInteractionPlan, native_alice_bob_round, FinDist.bind_map]
  exact FinDist.bind_congr fun response _ => native_alice_after_bob players bit response

/-- After thirteen rounds Carol's guess is fixed. This is the actual service
continuation of the legal Alice deviation, with both opponents unrestricted. -/
theorem native_alice_thirteen_rounds (players : Player → nativeApp.Policy) :
    nativeApp.runRounds nativeScheduler (nativeAliceProfile players) 13 nativeRoot =
      (FinDist.uniformOfFintype (α := Bool)).bind fun bit =>
        (players bob ((observed bit).recall bob) ((observed bit).observe nativeApp bob)).bind
          (nativeCarolPlay (nativeAliceProfile players) bit) := by
  change nativeApp.runRounds nativeScheduler (nativeAliceProfile players) (9 + 4) nativeRoot = _
  rw [ReactiveApplication.runRounds_add, native_alice_nine_rounds, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro bit _
  rw [FinDist.bind_bind]
  apply FinDist.bind_congr
  intro response _
  rw [FinDist.bind_map]
  simp only [nativeCarolPlay, nativeAliceProfile,
    Function.update_of_ne (by decide : carol ≠ alice)]
  apply FinDist.bind_congr
  intro current _
  exact native_carol_guess_rounds (nativeAliceProfile players) bit response current

private theorem native_alice_activation_after_bob (players : Player → nativeApp.Policy)
    (bit : Bool) (response : nativeApp.Action) :
    (nativeRuntime.runInteractionPlan nativeLeaks (nativeAliceProfile players) nativeNetwork
      [.grant aliceBinding, .player alice, .includeLatest aliceBinding alice,
        .tick, .expire aliceBinding, .grant carolBinding] (reacted bit response)).bind
          (fun prior => prior.environmentStep nativeApp (.activate carol)) =
      FinDist.pure (carolSite bit response) := by
  change (nativeRuntime.runInteractionPlan nativeLeaks (nativeAliceProfile players) nativeNetwork
    ([.grant aliceBinding, .player alice] ++ [.includeLatest aliceBinding alice,
      .tick, .expire aliceBinding, .grant carolBinding]) (reacted bit response)).bind _ = _
  rw [runInteractionPlan_append, native_alice_offer_rounds, FinDist.pure_bind,
    runInteractionPlan, native_alice_include_round, FinDist.pure_bind]
  have law : (((includedAfter bit response).environmentStep nativeApp
      (.application .advanceClock)).bind fun next =>
        (next.environmentStep nativeApp (.application (.expire aliceBinding))).bind fun next =>
          (next.environmentStep nativeApp (.application (.grant carolBinding))).bind fun next =>
            next.environmentStep nativeApp (.activate carol)) =
      FinDist.pure (carolSite bit response) := carolSite_law _ _
  convert law using 1
  simp only [runInteractionPlan, FinDist.bind_pure, interactionStep, interactionInstruction,
    FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
    ReactiveApplication.resume, FinDist.bind_bind]

/-- Stop immediately after Carol's passive observation and before her response.
This is her genuine decision input, with the exact private-leak rule intact. -/
theorem native_alice_carol_activation (players : Player → nativeApp.Policy) :
    (nativeApp.runRounds nativeScheduler (nativeAliceProfile players) 8 nativeRoot).bind
        (fun prior => prior.environmentStep nativeApp (.activate carol)) =
      (FinDist.uniformOfFintype (α := Bool)).bind fun bit =>
        (players bob ((observed bit).recall bob) ((observed bit).observe nativeApp bob)).map
          (carolSite bit) := by
  have bridge := native_prefix_rounds (nativeAliceProfile players) (nativePlan.take 8)
    (nativePlan.drop 8) (List.take_append_drop 8 nativePlan).symm
  change nativeApp.runRounds nativeScheduler (nativeAliceProfile players) 8 nativeRoot = _ at bridge
  rw [bridge]
  change (nativeRuntime.runInteractionPlan nativeLeaks (nativeAliceProfile players) nativeNetwork
    (.player alice :: .player bob :: [.grant aliceBinding, .player alice,
      .includeLatest aliceBinding alice, .tick, .expire aliceBinding, .grant carolBinding])
      initial).bind _ = _
  rw [runInteractionPlan, native_alice_first_round, FinDist.bind_map, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro bit _
  rw [runInteractionPlan, native_alice_bob_round, FinDist.bind_map, FinDist.bind_bind,
    FinDist.map_eq_bind]
  exact FinDist.bind_congr fun response _ => native_alice_activation_after_bob players bit response

end VegasTests.SelectiveAssociation
