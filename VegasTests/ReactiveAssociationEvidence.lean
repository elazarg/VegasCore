/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationNative
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.Pending.ReactiveResponseObservation
import Vegas.Pending.ReactiveService
import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.ReactiveSafety

/-! # A prior private certificate acquires a public binding association

Alice sends a certified candidate; only Bob observes its opening. A later
packet associates the same candidate with the game, without carrying a new
certificate. Bob can now verify the named binding. Carol sees the association
and the entire ledger but cannot distinguish the two possible binding values.
-/

noncomputable section

namespace VegasTests.ReactiveAssociationEvidence

open GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime

abbrev graph := SelectiveAssociation.nativeGraph
local instance : NeZero graph.order.eventCount := ⟨by decide⟩
abbrev runtime := SelectiveAssociation.nativeRuntime
abbrev leaks := SelectiveAssociation.nativeLeaks
abbrev app := runtime.reactiveApplication leaks
abbrev candidate : Handle graph := (0, .prepared 0)
def opening (bit : Bool) : OpeningFact graph := ⟨candidate, ⟨.bool, bit⟩⟩
def named (bit : Bool) : EventGraph.CommitmentEvidence graph :=
  ⟨0, .bool, ⟨.inr 0, rfl⟩, bit⟩

def initial : app.Execution :=
  ReactiveApplication.Execution.initial app SelectiveAssociation.nativeInitial

def activatedInitial : app.Execution :=
  { initial with environmentRecall := [⟨initial.observeEnvironment app, .activate 0⟩] }

def first (bit : Bool) : app.Execution :=
  activatedInitial.respond app 0 ⟨some (.submit
    ⟨⟨.commitment 0 candidate, some ⟨.bool, bit⟩⟩, .owned (opening bit)⟩)⟩

def observed (bit : Bool) : app.Execution :=
  { first bit with
    network := (first bit).network.learn 1 {(0, 0)}
    environmentRecall := (first bit).environmentRecall ++
      [⟨(first bit).observeEnvironment app, .activate 1⟩] }

def beforeOffer (execution : app.Execution) : app.Execution :=
  let granted : app.Execution := { execution with
    application := { execution.application with serviceGrant := some 0 }
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .application (.grant 0)⟩] }
  { granted with environmentRecall := granted.environmentRecall ++
    [⟨granted.observeEnvironment app, .activate 0⟩] }

def offered (bit : Bool) : app.Execution :=
  (beforeOffer (observed bit)).respond app 0
    ⟨some (.submit ⟨⟨.commitment 0 candidate, none⟩, .none⟩)⟩

def included (bit : Bool) : app.Execution :=
  { (offered bit).includePending app (0, 1) with
    environmentRecall := (offered bit).environmentRecall ++
      [⟨(offered bit).observeEnvironment app, .include (0, 1)⟩] }

private theorem ready (bit : Bool) : (offered bit).application.config.cut.Ready 0 := by
  cases bit <;> decide

private def bound (bit : Bool) : State graph :=
  { (offered bit).application.complete 0 (ready bit) (.success bit) (.success bit) with
    accepted := Function.update (offered bit).application.accepted (.inr 0) (some candidate)
    candidates := (offered bit).application.candidates.freeze candidate }

private theorem accepts (bit : Bool) :
    app.handle (offered bit).application ⟨(0, 1), ⟨.commitment 0 candidate, none⟩⟩ =
      some (bound bit) := by
  have unused : (offered bit).application.HandleUnused candidate := by
    intro field
    cases field with
    | inl input => exact Fin.elim0 input
    | inr event =>
        change (none : Option (Handle graph)) ≠ some candidate
        simp
  have result := handle_commitment_eq runtime (offered bit).application (0, 1) 0 candidate
    0 .bool rfl rfl rfl (ready bit) (by change 0 < 1; decide) rfl rfl rfl unused
  change handle runtime (offered bit).application ⟨(0, 1), .commitment 0 candidate⟩ = _
  convert result using 1
  cases bit <;> rfl

private theorem lookup (bit : Bool) : (offered bit).network.lookup (0, 1) =
    some ⟨(0, 1), ⟨.commitment 0 candidate, none⟩⟩ := rfl

private theorem included_application (bit : Bool) : (included bit).application = bound bit := by
  unfold included ReactiveApplication.Execution.includePending MessageNetwork.includePending
  rw [lookup]
  change (app.handle _ _).getD _ = _
  rw [accepts]
  rfl

theorem activation_leaks_to_bob (bit : Bool) :
    (first bit).environmentStep app (.activate 1) = FinDist.pure (observed bit) := by
  simp only [ReactiveApplication.Execution.environmentStep, app, reactiveApplication, leaks,
    SelectiveAssociation.nativeLeaks, SelectiveAssociation.bob, SelectiveAssociation.alice,
    FinDist.map_pure]
  rfl

theorem initial_activation : initial.environmentStep app (.activate 0) =
    FinDist.pure activatedInitial := by
  simp [ReactiveApplication.Execution.environmentStep, app, reactiveApplication,
    leaks, SelectiveAssociation.nativeLeaks, SelectiveAssociation.bob, MessageNetwork.learn_empty,
    FinDist.map_pure, activatedInitial, initial, ReactiveApplication.Execution.initial]

theorem beforeOffer_law (execution : app.Execution) :
    ((execution.environmentStep app (.application (.grant 0))).bind
      fun next => next.environmentStep app (.activate 0)) =
        FinDist.pure (beforeOffer execution) := by
  simp [ReactiveApplication.Execution.environmentStep, app, reactiveApplication,
    environmentStep, leaks, SelectiveAssociation.nativeLeaks, SelectiveAssociation.bob,
    MessageNetwork.learn_empty,
    FinDist.map_pure, beforeOffer]

theorem proof_before_association (bit : Bool) :
    opening bit ∈ (runtime.packetEvidence leaks).observe ((observed bit).observe app 1) ∧
      (observed bit).application.accepted (.inr 0) = none ∧
      (named bit).binding.get? (observed bit).application.config.store = none := by
  cases bit <;> decide

theorem association_without_new_certificate (bit : Bool) :
    (included bit).network.ledger = [⟨(0, 1), ⟨.commitment 0 candidate, none⟩⟩] ∧
      (included bit).receipts = [((0, 1), true)] ∧
      runtime.bindingEvidenceObserved leaks ((included bit).observe app 1) (named bit) := by
  refine ⟨rfl, ?_, candidate, ?_, ?_⟩
  · unfold included ReactiveApplication.Execution.includePending MessageNetwork.includePending
    rw [lookup]
    change (offered bit).receipts ++ [((0, 1), (app.handle _ _).isSome)] = _
    rw [accepts]
    rfl
  · change (included bit).application.accepted (.inr 0) = some candidate
    rw [included_application]
    simp [bound]
  · cases bit <;> decide

theorem carol_has_no_certificate (bit : Bool) :
    (runtime.packetEvidence leaks).observe ((included bit).observe app 2) = [] := by
  cases bit <;> rfl

theorem carol_cannot_distinguish :
    (included false).observe app 2 = (included true).observe app 2 := by
  unfold ReactiveApplication.Execution.observe
  rw [included_application, included_application]
  rw [(association_without_new_certificate false).2.1,
    (association_without_new_certificate true).2.1]
  congr 1
  change (⟨2, (bound false).publicView, graph.playerObserve 2 (bound false).config,
      fun slot => (bound false).candidates.lookup (2, slot)⟩ : ReactivePlayerView graph) =
    ⟨2, (bound true).publicView, graph.playerObserve 2 (bound true).config,
      fun slot => (bound true).candidates.lookup (2, slot)⟩
  congr 1
  · unfold State.publicView
    congr 1
    apply EventGraph.PublicObservation.ext
    · rfl
    · apply graph.publicStore_congr
      intro field visible
      cases field with
      | inl input => exact Fin.elim0 input
      | inr event =>
          fin_cases event
          · exact False.elim visible
          all_goals rfl
  · apply EventGraph.PlayerObservation.ext
    · rfl
    · apply graph.playerStore_congr
      intro field visible
      cases field with
      | inl input => exact Fin.elim0 input
      | inr event =>
          fin_cases event
          · exact False.elim (by
              change (0 : Fin 3) = 2 at visible
              cases visible)
          all_goals rfl
    · rfl

/-- Bob's response may prepare candidates, forge claims, forward a possessed
certificate, replay Alice's envelope, or remain silent. No case is excluded. -/
def reacted (bit : Bool) (response : app.Action) : app.Execution :=
  (observed bit).respond app 1 response

def offeredAfter (bit : Bool) (response : app.Action) : app.Execution :=
  (beforeOffer (reacted bit response)).respond app 0
    ⟨some (.submit ⟨⟨.commitment 0 candidate, none⟩, .none⟩)⟩

def includedAfter (bit : Bool) (response : app.Action) : app.Execution :=
  { (offeredAfter bit response).includePending app (0, 1) with
    environmentRecall := (offeredAfter bit response).environmentRecall ++
      [⟨(offeredAfter bit response).observeEnvironment app, .include (0, 1)⟩] }

theorem inclusion_law (bit : Bool) (response : app.Action) :
    (offeredAfter bit response).environmentStep app (.include (0, 1)) =
      FinDist.pure (includedAfter bit response) := by
  simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
  rfl

theorem arbitrary_response_private (bit : Bool) (response : app.Action)
    (who : Fin 3) (different : who ≠ 1) :
    ((reacted bit response).recall who, (reacted bit response).observe app who) =
      ((observed bit).recall who, (observed bit).observe app who) :=
  runtime.reactive_response_other_input leaks (observed bit) 1 who different response

private theorem reacted_public (bit : Bool) (response : app.Action) :
    (reacted bit response).application.publicView = (observed bit).application.publicView :=
  (runtime.reactive_respond_application leaks (observed bit) 1 response).2

private theorem reacted_config (bit : Bool) (response : app.Action) :
    (reacted bit response).application.config = (observed bit).application.config :=
  (runtime.reactive_respond_application leaks (observed bit) 1 response).1

private theorem reacted_candidate (bit : Bool) (response : app.Action) :
    (reacted bit response).application.candidates.lookup candidate =
      .openable ⟨.bool, bit⟩ := by
  have fixed : (observed bit).application.candidates.lookup candidate ≠ .fresh := by
    cases bit <;> decide
  exact runtime.reactive_respond_candidate_fixed leaks (observed bit) 1 response candidate fixed

private theorem reacted_alice_serial (bit : Bool) (response : app.Action) :
    (reacted bit response).network.nextSerial 0 = 1 := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit material => rfl
      | replay id =>
          cases found : ((observed bit).network.known 1).find?
              (fun envelope => envelope.id = id) <;>
            simp only [reacted, ReactiveApplication.Execution.respond, MessageNetwork.replay, found]
          all_goals rfl

private theorem reacted_ledger (bit : Bool) (response : app.Action) :
    (reacted bit response).network.ledger = [] := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit material => rfl
      | replay id =>
          cases found : ((observed bit).network.known 1).find?
              (fun envelope => envelope.id = id) <;>
            simp only [reacted, ReactiveApplication.Execution.respond, MessageNetwork.replay, found]
          all_goals rfl

private theorem offeredAfter_application (bit : Bool) (response : app.Action) :
    (offeredAfter bit response).application =
      { (reacted bit response).application with serviceGrant := some 0 } := by
  change submitStep { (reacted bit response).application with serviceGrant := some 0 }
    0 (.commitment 0 candidate) = _
  simp only [submitStep, candidate, ↓reduceIte]
  rw [CommitmentCandidates.freeze_eq_self_of_not_fresh _ _ (by
    rw [reacted_candidate]
    simp)]

private theorem offeredAfter_public (bit : Bool) (response : app.Action) :
    (offeredAfter bit response).application.publicView =
      { (observed bit).application.publicView with serviceGrant := some 0 } := by
  rw [offeredAfter_application]
  exact congrArg (fun view : PublicView graph => { view with serviceGrant := some 0 })
    (reacted_public bit response)

private theorem offeredAfter_config (bit : Bool) (response : app.Action) :
    (offeredAfter bit response).application.config = (observed bit).application.config := by
  rw [offeredAfter_application, reacted_config]

private theorem offeredAfter_ready (bit : Bool) (response : app.Action) :
    (offeredAfter bit response).application.config.cut.Ready 0 := by
  rw [offeredAfter_config]
  cases bit <;> decide

private def boundAfter (bit : Bool) (response : app.Action) : State graph :=
  { (offeredAfter bit response).application.complete 0 (offeredAfter_ready bit response)
      (.success bit) (.success bit) with
    accepted := Function.update (offeredAfter bit response).application.accepted
      (.inr 0) (some candidate)
    candidates := (offeredAfter bit response).application.candidates.freeze candidate }

private theorem acceptsAfter (bit : Bool) (response : app.Action) :
    app.handle (offeredAfter bit response).application
      ⟨(0, 1), ⟨.commitment 0 candidate, none⟩⟩ = some (boundAfter bit response) := by
  have publicEq := offeredAfter_public bit response
  have accepted := congrArg PublicView.accepted publicEq
  change (offeredAfter bit response).application.accepted =
    (observed bit).application.accepted at accepted
  have vacant : (offeredAfter bit response).application.accepted (.inr 0) = none := by
    rw [accepted]
    rfl
  have unused : (offeredAfter bit response).application.HandleUnused candidate := by
    intro field
    rw [accepted]
    cases field with
    | inl input => exact Fin.elim0 input
    | inr event =>
        change (none : Option (Handle graph)) ≠ some candidate
        simp
  have timely : (offeredAfter bit response).application.WithinDeadline runtime 0 := by
    have clock := congrArg PublicView.clock publicEq
    have activated := congrArg PublicView.activatedAt publicEq
    change (offeredAfter bit response).application.clock =
      (observed bit).application.clock at clock
    change (offeredAfter bit response).application.activatedAt =
      (observed bit).application.activatedAt at activated
    unfold State.WithinDeadline
    rw [clock, activated]
    change 0 < 1
    decide
  have meaning : (offeredAfter bit response).application.bindingResult candidate .bool =
      .success bit := by
    rw [offeredAfter_application]
    unfold State.bindingResult
    rw [reacted_candidate]
    rfl
  have result := handle_commitment_eq runtime (offeredAfter bit response).application
    (0, 1) 0 candidate 0 .bool rfl rfl rfl (offeredAfter_ready bit response)
      timely rfl rfl vacant unused
  change handle runtime _ ⟨(0, 1), .commitment 0 candidate⟩ = _
  simpa only [meaning, cast_eq, boundAfter] using result

private theorem bobKnown (bit : Bool) : (observed bit).network.known 1 =
    [⟨(0, 0), ⟨.commitment 0 candidate, some (opening bit)⟩⟩] := by
  cases bit <;> rfl

private theorem reacted_missing (bit : Bool) (response : app.Action) :
    (reacted bit response).network.lookup (0, 1) = none := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => cases bit <;> rfl
  | some transmission =>
      cases transmission with
      | submit material => cases bit <;> rfl
      | replay id =>
          simp only [reacted, ReactiveApplication.Execution.respond, MessageNetwork.replay,
            bobKnown]
          by_cases same : (0, 0) = id
          · subst id
            simp only [List.find?_cons, decide_true]
            cases bit <;> rfl
          · simp only [List.find?_cons, same, decide_false, List.find?_nil]
            cases bit <;> rfl

private theorem lookupAfter (bit : Bool) (response : app.Action) :
    (offeredAfter bit response).network.lookup (0, 1) =
      some ⟨(0, 1), ⟨.commitment 0 candidate, none⟩⟩ := by
  change ((reacted bit response).network.pending ++
    [(⟨(0, (reacted bit response).network.nextSerial 0),
      ⟨.commitment 0 candidate, none⟩⟩ : Message (Fin 3) app.Payload)]).find?
        (fun message => message.id = (0, 1)) = _
  rw [reacted_alice_serial, List.find?_append]
  have missing := reacted_missing bit response
  change (reacted bit response).network.pending.find? (fun message => message.id = (0, 1)) =
    none at missing
  rw [missing]
  rfl

private theorem includedAfter_application (bit : Bool) (response : app.Action) :
    (includedAfter bit response).application = boundAfter bit response := by
  unfold includedAfter ReactiveApplication.Execution.includePending MessageNetwork.includePending
  rw [lookupAfter]
  change (app.handle _ _).getD _ = _
  rw [acceptsAfter]
  rfl

/-- The reserved selector chooses Alice's later envelope even if Bob replayed
the first certified one or submitted a competing application call. -/
theorem later_envelope_selected (bit : Bool) (response : app.Action) :
    runtime.reactiveLatest leaks 0 0 ((offeredAfter bit response).observeEnvironment app) =
      .include (0, 1) := by
  simp [reactiveLatest, ReactiveApplication.EnvironmentView.Unpublished, offeredAfter,
    ReactiveApplication.Execution.observeEnvironment, ReactiveApplication.Execution.respond,
    MessageNetwork.submit, MessageNetwork.publicView, reacted_ledger, reacted_alice_serial,
    List.reverse_append, Message.sender, Payload.event?, app, reactiveApplication,
    WitnessedSubmission.emit, beforeOffer]

theorem carol_activation_leaks_nothing (execution : app.Execution) :
    ((execution.environmentStep app (.activate 2)).map fun next => next.observe app 2) =
      FinDist.pure (execution.observe app 2) := by
  simp [ReactiveApplication.Execution.environmentStep, app, reactiveApplication,
    leaks, SelectiveAssociation.nativeLeaks, SelectiveAssociation.bob,
    MessageNetwork.learn_empty, FinDist.map_pure,
    ReactiveApplication.Execution.observe]

private theorem offeredAfter_carol (bit : Bool) (response : app.Action) :
    ((offeredAfter bit response).recall 2, (offeredAfter bit response).observe app 2) =
      ((offered bit).recall 2, (offered bit).observe app 2) := by
  have middle :
      ((beforeOffer (reacted bit response)).recall 2,
        (beforeOffer (reacted bit response)).observe app 2) =
      ((beforeOffer (observed bit)).recall 2, (beforeOffer (observed bit)).observe app 2) := by
    exact congrArg (fun input : List app.PlayerEntry × app.PlayerView =>
      (input.1, { input.2 with application := { input.2.application with
        publicView := { input.2.application.publicView with serviceGrant := some 0 } } }))
          (arbitrary_response_private bit response 2 (by decide))
  exact (runtime.reactive_response_other_input leaks (beforeOffer (reacted bit response)) 0 2
    (by decide) _).trans (middle.trans
      (runtime.reactive_response_other_input leaks (beforeOffer (observed bit)) 0 2
        (by decide) _).symm)

private theorem boundAfter_carol (bit : Bool) (response : app.Action) :
    app.observePlayer (boundAfter bit response) 2 = app.observePlayer (bound bit) 2 := by
  have before := congrArg (fun input => input.2.application) (offeredAfter_carol bit response)
  have config : (offeredAfter bit response).application.config =
      (offered bit).application.config := offeredAfter_config bit response
  have publicEq := congrArg ReactivePlayerView.publicView before
  have accepted := congrArg PublicView.accepted publicEq
  have clock := congrArg PublicView.clock publicEq
  have activated := congrArg PublicView.activatedAt publicEq
  have granted := congrArg PublicView.serviceGrant publicEq
  have candidates := congrArg ReactivePlayerView.candidates before
  change (offeredAfter bit response).application.accepted =
    (offered bit).application.accepted at accepted
  change (offeredAfter bit response).application.clock =
    (offered bit).application.clock at clock
  change (offeredAfter bit response).application.activatedAt =
    (offered bit).application.activatedAt at activated
  change (offeredAfter bit response).application.serviceGrant =
    (offered bit).application.serviceGrant at granted
  change (fun slot => (offeredAfter bit response).application.candidates.lookup (2, slot)) =
    (fun slot => (offered bit).application.candidates.lookup (2, slot)) at candidates
  change (⟨2, (boundAfter bit response).publicView,
    graph.playerObserve 2 (boundAfter bit response).config,
    fun slot => (boundAfter bit response).candidates.lookup (2, slot)⟩ :
      ReactivePlayerView graph) = _
  congr 1
  · simp only [boundAfter, bound, State.complete, State.publicView]
    simp only [config, accepted, clock, activated, granted]
  · simp only [boundAfter, bound, State.complete]
    simp only [config]
  · funext slot
    simp only [boundAfter, bound]
    have different : (2, slot) ≠ candidate := by
      intro same
      have := congrArg Prod.fst same
      exact (by decide : (2 : Fin 3) ≠ 0) this
    rw [CommitmentCandidates.lookup_freeze_other _ _ _ different,
      CommitmentCandidates.lookup_freeze_other _ _ _ different]
    exact congrFun candidates slot

private theorem includedAfter_carol (bit : Bool) (response : app.Action) :
    ((includedAfter bit response).recall 2, (includedAfter bit response).observe app 2) =
      ((included bit).recall 2, (included bit).observe app 2) := by
  have before := offeredAfter_carol bit response
  have recall := congrArg Prod.fst before
  have messages := congrArg (fun input => input.2.messages) before
  have receipts := congrArg (fun input => input.2.receipts) before
  apply Prod.ext
  · change (includedAfter bit response).recall 2 = (included bit).recall 2
    unfold includedAfter included ReactiveApplication.Execution.includePending
      MessageNetwork.includePending
    rw [lookupAfter, lookup]
    exact recall
  · change (includedAfter bit response).observe app 2 = (included bit).observe app 2
    unfold ReactiveApplication.Execution.observe
    rw [includedAfter_application, included_application, boundAfter_carol]
    congr 1
    · unfold includedAfter included ReactiveApplication.Execution.includePending
        MessageNetwork.includePending
      rw [lookupAfter, lookup]
      change (⟨(offeredAfter bit response).network.leaked 2,
          (offeredAfter bit response).network.ledger ++ [_]⟩ :
            MessageNetwork.PlayerView (Fin 3) app.Payload) =
        ⟨(offered bit).network.leaked 2, (offered bit).network.ledger ++ [_]⟩
      exact congrArg (fun prior : MessageNetwork.PlayerView (Fin 3) app.Payload =>
        (⟨prior.leaked, prior.ledger ++ [⟨(0, 1), ⟨.commitment 0 candidate, none⟩⟩]⟩ :
          MessageNetwork.PlayerView (Fin 3) app.Payload)) messages
    · unfold includedAfter included ReactiveApplication.Execution.includePending
        MessageNetwork.includePending
      rw [lookupAfter, lookup]
      dsimp only
      rw [acceptsAfter, accepts]
      exact congrArg (fun prior => prior ++ [((0, 1), true)]) receipts

/-- Carol's entire decision input is unchanged even when Bob takes different
arbitrary responses after learning the two possible values. -/
theorem carol_input_after_arbitrary_responses (left right : app.Action) :
    ((includedAfter false left).recall 2, (includedAfter false left).observe app 2) =
      ((includedAfter true right).recall 2, (includedAfter true right).observe app 2) := by
  rw [includedAfter_carol, includedAfter_carol]
  apply Prod.ext
  · rfl
  · exact carol_cannot_distinguish

private theorem reacted_leaked (bit : Bool) (response : app.Action) (who : Fin 3) :
    (reacted bit response).network.leaked who = (observed bit).network.leaked who := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit material => rfl
      | replay id =>
          cases found : ((observed bit).network.known 1).find?
              (fun envelope => envelope.id = id) <;>
            simp only [reacted, ReactiveApplication.Execution.respond, MessageNetwork.replay,
              found]

/-- Arbitrary intervening responses cannot erase Bob's old certificate. The
later accepted envelope carries no certificate of its own. -/
theorem association_after_arbitrary_response (bit : Bool) (response : app.Action) :
    (includedAfter bit response).network.ledger =
        [⟨(0, 1), ⟨.commitment 0 candidate, none⟩⟩] ∧
      runtime.bindingEvidenceObserved leaks
        ((includedAfter bit response).observe app 1) (named bit) := by
  have ledger : (includedAfter bit response).network.ledger =
      [⟨(0, 1), ⟨.commitment 0 candidate, none⟩⟩] := by
    unfold includedAfter ReactiveApplication.Execution.includePending MessageNetwork.includePending
    rw [lookupAfter]
    change (reacted bit response).network.ledger ++ [_] = _
    rw [reacted_ledger]
    rfl
  refine ⟨ledger, candidate, ?_, ?_⟩
  · change (includedAfter bit response).application.accepted (.inr 0) = some candidate
    rw [includedAfter_application]
    simp [boundAfter]
  · have leaked : (includedAfter bit response).network.leaked 1 =
        (observed bit).network.leaked 1 := by
      unfold includedAfter ReactiveApplication.Execution.includePending
        MessageNetwork.includePending
      rw [lookupAfter]
      exact reacted_leaked bit response 1
    change opening bit ∈
      (((includedAfter bit response).network.leaked 1 ++
        (includedAfter bit response).network.ledger).flatMap
          fun message => message.payload.evidence.toList)
    rw [leaked, ledger]
    cases bit <;> decide

/-- The actual Carol activation preserves the complete input equality. -/
theorem carol_activation_after_arbitrary_responses (left right : app.Action) :
    (((includedAfter false left).environmentStep app (.activate 2)).map
      fun next => (next.recall 2, next.observe app 2)) =
    (((includedAfter true right).environmentStep app (.activate 2)).map
      fun next => (next.recall 2, next.observe app 2)) := by
  simpa [ReactiveApplication.Execution.environmentStep, app, reactiveApplication,
    leaks, SelectiveAssociation.nativeLeaks, SelectiveAssociation.bob,
    SelectiveAssociation.alice, MessageNetwork.learn_empty, FinDist.map_pure,
    ReactiveApplication.Execution.observe]
      using congrArg FinDist.pure (carol_input_after_arbitrary_responses left right)

private def afterApplication (execution : app.Execution) (state : State graph)
    (command : EnvironmentCommand graph) : app.Execution :=
  { execution with
    application := state
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .application command⟩] }

private def ticked (bit : Bool) (response : app.Action) : app.Execution :=
  afterApplication (includedAfter bit response)
    { (includedAfter bit response).application with
      clock := (includedAfter bit response).application.clock + 1 } .advanceClock

private def expired (bit : Bool) (response : app.Action) : app.Execution :=
  afterApplication (ticked bit response) (ticked bit response).application (.expire 0)

private def carolGranted (bit : Bool) (response : app.Action) : app.Execution :=
  afterApplication (expired bit response)
    { (expired bit response).application with serviceGrant := some 1 } (.grant 1)

/-- The execution at Carol's actual activation in the fixed calendar. -/
def carolSite (bit : Bool) (response : app.Action) : app.Execution :=
  let granted := carolGranted bit response
  { granted with environmentRecall := granted.environmentRecall ++
    [⟨granted.observeEnvironment app, .activate 2⟩] }

private theorem ticked_not_ready (bit : Bool) (response : app.Action) :
    ¬(ticked bit response).application.config.cut.Ready 0 := by
  change ¬(includedAfter bit response).application.config.cut.Ready 0
  rw [includedAfter_application]
  intro ready
  exact ready.1 (by simp [boundAfter, State.complete, EventGraph.Config.complete])

/-- The four intervening service commands are precisely the calendar's clock
tick, expiry, next grant, and Carol activation. -/
theorem carolSite_law (bit : Bool) (response : app.Action) :
    (((includedAfter bit response).environmentStep app (.application .advanceClock)).bind
      fun next => (next.environmentStep app (.application (.expire 0))).bind
        fun next => (next.environmentStep app (.application (.grant 1))).bind
          fun next => next.environmentStep app (.activate 2)) =
      FinDist.pure (carolSite bit response) := by
  have tick : (includedAfter bit response).environmentStep app (.application .advanceClock) =
      FinDist.pure (ticked bit response) := by
    simp [ReactiveApplication.Execution.environmentStep, app, reactiveApplication,
      environmentStep, FinDist.map_pure, ticked, afterApplication]
  have expiry : (ticked bit response).environmentStep app (.application (.expire 0)) =
      FinDist.pure (expired bit response) := by
    simp only [ReactiveApplication.Execution.environmentStep, app, reactiveApplication]
    rw [environmentStep_expire_of_not_ready runtime _ 0 (ticked_not_ready bit response)]
    simp only [FinDist.map_pure]
    rfl
  rw [tick, FinDist.pure_bind, expiry, FinDist.pure_bind]
  simp [ReactiveApplication.Execution.environmentStep, app, reactiveApplication,
    environmentStep, leaks, SelectiveAssociation.nativeLeaks, SelectiveAssociation.bob,
    MessageNetwork.learn_empty, FinDist.map_pure, carolSite, carolGranted, afterApplication]

/-- Carol receives the same entire input at her scheduled choice, for either
Alice value and any two earlier Bob responses. -/
theorem carolSite_input (left right : app.Action) :
    ((carolSite false left).recall 2, (carolSite false left).observe app 2) =
      ((carolSite true right).recall 2, (carolSite true right).observe app 2) := by
  exact congrArg (fun input : List app.PlayerEntry × app.PlayerView =>
    (input.1, { input.2 with application := { input.2.application with
      publicView := { input.2.application.publicView with
        clock := input.2.application.publicView.clock + 1, serviceGrant := some 1 } } }))
      (carol_input_after_arbitrary_responses left right)

theorem carolSite_rounds (bit : Bool) (response : app.Action) :
    (carolSite bit response).environmentRecall.length = 9 := by
  simp [carolSite, carolGranted, expired, ticked, afterApplication, includedAfter,
    offeredAfter, beforeOffer, reacted, observed, first, activatedInitial, initial,
    ReactiveApplication.Execution.respond, ReactiveApplication.Execution.initial]

end VegasTests.ReactiveAssociationEvidence
