/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.ReactiveAssociationEvidence
import VegasTests.SelectiveAssociationProbability

/-! # Removing passive observation from the native selective-association service

The application, raw response bounds, service calendar, selector, and deadlines
are the existing native fixture. Only its observation rule is changed. The
paired prefix below checks the information effect of that single change. An
equilibrium of this restricted native protocol remains a separate obligation.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def leaks : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph) :=
  fun _ _ => FinDist.pure ∅

abbrev app := serviceApp leaks
abbrev menu := serviceMenu leaks
abbrev network := serviceNetwork leaks
abbrev scheduler := serviceScheduler leaks
abbrev arena := serviceArena leaks
abbrev model := serviceModel leaks

def initial : app.Execution := .initial app nativeInitial

abbrev candidate : Handle nativeGraph := (alice, .prepared 0)
def opening (bit : Bool) : OpeningFact nativeGraph := ⟨candidate, ⟨.bool, bit⟩⟩

def certifiedOffer (bit : Bool) : app.Action :=
  ⟨some (.submit ⟨⟨.commitment aliceBinding candidate, some ⟨.bool, bit⟩⟩,
    .owned (opening bit)⟩)⟩

def associate : app.Action :=
  ⟨some (.submit ⟨⟨.commitment aliceBinding candidate, none⟩, .none⟩)⟩

theorem certifiedOffer_available (bit : Bool) (past : List app.PlayerEntry)
    (view : app.PlayerView) : certifiedOffer bit ∈ menu.actions alice past view := by
  change certifiedOffer bit ∈ (nativeBounds.rawMenu nativeRuntime leaks).actions alice past view
  rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  change (⟨⟨.commitment aliceBinding candidate, some ⟨.bool, bit⟩⟩,
    .owned (opening bit)⟩ : WitnessedSubmission nativeGraph) ∈ nativeBounds.submissions _
  rw [MessageBounds.submissions_mem]
  have bounded : nativeBounds.AllowsHandle candidate := by change 0 < 2; decide
  have value : (⟨.bool, bit⟩ : Raw simpleExpr) ∈ nativeBounds.values := by cases bit <;> decide
  exact ⟨⟨bounded, value⟩, bounded, value⟩

theorem associate_available (past : List app.PlayerEntry) (view : app.PlayerView) :
    associate ∈ menu.actions alice past view := by
  change associate ∈ (nativeBounds.rawMenu nativeRuntime leaks).actions alice past view
  rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  change (⟨⟨.commitment aliceBinding candidate, none⟩, .none⟩ :
    WitnessedSubmission nativeGraph) ∈ nativeBounds.submissions _
  rw [MessageBounds.submissions_mem]
  exact ⟨⟨by change 0 < 2; decide, trivial⟩, trivial⟩

def activate (execution : app.Execution) (who : Player) : app.Execution :=
  { execution with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .activate who⟩] }

theorem activation_law (execution : app.Execution) (who : Player) :
    execution.environmentStep app (.activate who) = FinDist.pure (activate execution who) := by
  simp [ReactiveApplication.Execution.environmentStep, app, serviceApp, reactiveApplication,
    leaks, FinDist.map_pure, activate]

def first (bit : Bool) : app.Execution :=
  (activate initial alice).respond app alice (certifiedOffer bit)

def bobInput (bit : Bool) : app.Execution := activate (first bit) bob

theorem bob_activation (bit : Bool) :
    (first bit).environmentStep app (.activate bob) = FinDist.pure (bobInput bit) :=
  activation_law _ _

/-- The private certified packet exists on the wire, but the restricted
observation rule supplies neither its payload nor its certificate to Bob. -/
theorem first_packet (bit : Bool) :
    (bobInput bit).network.pending =
      [⟨(alice, 0), ⟨.commitment aliceBinding candidate, some (opening bit)⟩⟩] ∧
    (nativeRuntime.packetEvidence leaks).observe ((bobInput bit).observe app bob) = [] := by
  cases bit <;> exact ⟨rfl, rfl⟩

/-- Equality includes the complete private input, not just the ledger. -/
theorem bob_input_same :
    ((bobInput false).recall bob, (bobInput false).observe app bob) =
      ((bobInput true).recall bob, (bobInput true).observe app bob) := by
  have hidden (bit : Bool) := nativeRuntime.reactive_response_other_input leaks
    (activate initial alice) alice bob (by decide) (certifiedOffer bit)
  exact (hidden false).trans (hidden true).symm

/-- Consequently every behavioral response has the same law at the two
restricted inputs. No assumption about which raw responses it chooses is used. -/
theorem bob_response_same (policy : app.Policy) :
    policy ((bobInput false).recall bob) ((bobInput false).observe app bob) =
      policy ((bobInput true).recall bob) ((bobInput true).observe app bob) :=
  congrArg (fun input => policy input.1 input.2) bob_input_same

def firstPolicy (players : Player → app.Policy) : Player → app.Policy :=
  Function.update players alice fun _ _ =>
    (FinDist.uniformOfFintype (α := Bool)).map certifiedOffer

theorem first_round (players : Player → app.Policy) :
    nativeRuntime.interactionStep leaks (firstPolicy players) network (.player alice) initial =
      (FinDist.uniformOfFintype (α := Bool)).map first := by
  simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
    ReactiveApplication.dispatch, activation_law, FinDist.pure_bind,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume, ReactiveApplication.invoke,
    firstPolicy, Function.update_self, FinDist.map_comp]
  rfl

theorem bob_round (players : Player → app.Policy) (bit : Bool) :
    nativeRuntime.interactionStep leaks (firstPolicy players) network (.player bob) (first bit) =
      (players bob ((bobInput bit).recall bob) ((bobInput bit).observe app bob)).map
        ((bobInput bit).respond app bob) := by
  simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
    ReactiveApplication.dispatch, bob_activation, FinDist.pure_bind,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume, ReactiveApplication.invoke,
    firstPolicy, Function.update_of_ne (by decide : bob ≠ alice)]

/-- The first two instructions of the actual native calendar factor through
one Bob response distribution, independent of Alice's private bit. -/
theorem two_rounds (players : Player → app.Policy) :
    nativeRuntime.runInteractionPlan leaks (firstPolicy players) network
      (nativePlan.take 2) initial =
      (FinDist.uniformOfFintype (α := Bool)).bind fun bit =>
        (players bob ((bobInput false).recall bob) ((bobInput false).observe app bob)).map
          ((bobInput bit).respond app bob) := by
  change nativeRuntime.runInteractionPlan leaks (firstPolicy players) network
    [.player alice, .player bob] initial = _
  rw [runInteractionPlan, first_round, FinDist.bind_map]
  apply FinDist.bind_congr
  intro bit _
  rw [runInteractionPlan, bob_round]
  simp only [runInteractionPlan, FinDist.bind_pure]
  cases bit
  · rfl
  · rw [bob_response_same (players bob)]

/-- No randomized raw response at Bob's first activation can encode a guess
of the private fair bit with accuracy above one half. Failure-valued reports
are included. This is a prefix information bound, not an equilibrium claim. -/
theorem first_response_guess_bound (policy : app.Policy)
    (report : app.Action → PublicationResult Bool) :
    (FinDist.uniformOfFintype (α := Bool)).expect (fun bit =>
      (policy ((bobInput bit).recall bob) ((bobInput bit).observe app bob)).expect
        (fun response => correctness (.success bit) (report response))) ≤ 1 / 2 := by
  have constant (bit : Bool) :
      policy ((bobInput bit).recall bob) ((bobInput bit).observe app bob) =
        policy ((bobInput false).recall bob) ((bobInput false).observe app bob) := by
    cases bit
    · rfl
    · exact (bob_response_same policy).symm
  simp_rw [constant]
  simpa only [FinDist.expect_map] using fair_guess_le_half
    ((policy ((bobInput false).recall bob) ((bobInput false).observe app bob)).map report)

def reacted (bit : Bool) : app.Execution := (bobInput bit).respond app bob ⟨none⟩

def beforeOffer (bit : Bool) : app.Execution :=
  let granted : app.Execution := { reacted bit with
    application := { (reacted bit).application with serviceGrant := some aliceBinding }
    environmentRecall := (reacted bit).environmentRecall ++
      [⟨(reacted bit).observeEnvironment app, .application (.grant aliceBinding)⟩] }
  activate granted alice

def offered (bit : Bool) : app.Execution := (beforeOffer bit).respond app alice associate

def included (bit : Bool) : app.Execution :=
  { (offered bit).includePending app (alice, 1) with
    environmentRecall := (offered bit).environmentRecall ++
      [⟨(offered bit).observeEnvironment app, .include (alice, 1)⟩] }

private theorem ready (bit : Bool) : (offered bit).application.config.cut.Ready aliceBinding := by
  cases bit <;> decide

private def bound (bit : Bool) : State nativeGraph :=
  { (offered bit).application.complete aliceBinding (ready bit) (.success bit) (.success bit) with
    accepted := Function.update (offered bit).application.accepted (.inr aliceBinding)
      (some candidate)
    candidates := (offered bit).application.candidates.freeze candidate }

private theorem accepts (bit : Bool) :
    app.handle (offered bit).application
      ⟨(alice, 1), ⟨.commitment aliceBinding candidate, none⟩⟩ = some (bound bit) := by
  have unused : (offered bit).application.HandleUnused candidate := by
    intro field
    cases field with
    | inl input => exact Fin.elim0 input
    | inr event =>
        change (none : Option (Handle nativeGraph)) ≠ some candidate
        simp
  have result := handle_commitment_eq nativeRuntime (offered bit).application
    (alice, 1) aliceBinding candidate alice .bool rfl rfl rfl (ready bit)
    (by change 0 < 1; decide) rfl rfl rfl unused
  change handle nativeRuntime (offered bit).application
    ⟨(alice, 1), .commitment aliceBinding candidate⟩ = _
  convert result using 1
  cases bit <;> rfl

private theorem included_application (bit : Bool) :
    (included bit).application = bound bit := by
  have lookup : (offered bit).network.lookup (alice, 1) =
      some ⟨(alice, 1), ⟨.commitment aliceBinding candidate, none⟩⟩ := rfl
  unfold included ReactiveApplication.Execution.includePending MessageNetwork.includePending
  rw [lookup]
  change (app.handle _ _).getD _ = _
  rw [accepts]
  rfl

private theorem included_receipts (bit : Bool) :
    (included bit).receipts = [((alice, 1), true)] := by
  have lookup : (offered bit).network.lookup (alice, 1) =
      some ⟨(alice, 1), ⟨.commitment aliceBinding candidate, none⟩⟩ := rfl
  unfold included ReactiveApplication.Execution.includePending MessageNetwork.includePending
  rw [lookup]
  change (offered bit).receipts ++ [((alice, 1), (app.handle _ _).isSome)] = _
  rw [accepts]
  rfl

theorem beforeOffer_law (bit : Bool) :
    (((reacted bit).environmentStep app (.application (.grant aliceBinding))).bind
      fun next => next.environmentStep app (.activate alice)) = FinDist.pure (beforeOffer bit) := by
  simp [ReactiveApplication.Execution.environmentStep, app, serviceApp, reactiveApplication,
    environmentStep, leaks, FinDist.map_pure, beforeOffer, activate]

theorem association_selected (bit : Bool) :
    nativeRuntime.reactiveLatest leaks aliceBinding alice
      ((offered bit).observeEnvironment app) = .include (alice, 1) := by
  cases bit <;> rfl

theorem association_inclusion (bit : Bool) :
    (offered bit).environmentStep app (.include (alice, 1)) = FinDist.pure (included bit) := by
  simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
  rfl

/-- Public acceptance creates the same game association as in the leaking
fixture. It supplies no opening certificate to either guesser here. -/
theorem association_without_disclosure (bit : Bool) (who : Player) :
    (included bit).network.ledger =
      [⟨(alice, 1), ⟨.commitment aliceBinding candidate, none⟩⟩] ∧
    (included bit).application.accepted (.inr aliceBinding) = some candidate ∧
    (nativeRuntime.packetEvidence leaks).observe ((included bit).observe app who) = [] := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [included_application]
    simp [bound]
  · cases bit <;> rfl

theorem association_hidden (who : Player) (foreign : who ≠ alice) :
    (included false).observe app who = (included true).observe app who := by
  unfold ReactiveApplication.Execution.observe
  rw [included_application, included_application]
  rw [included_receipts false, included_receipts true]
  congr 1
  change (⟨who, (bound false).publicView, nativeGraph.playerObserve who (bound false).config,
      fun slot => (bound false).candidates.lookup (who, slot)⟩ : ReactivePlayerView nativeGraph) =
    ⟨who, (bound true).publicView, nativeGraph.playerObserve who (bound true).config,
      fun slot => (bound true).candidates.lookup (who, slot)⟩
  congr 1
  · unfold State.publicView
    congr 1
    apply EventGraph.PublicObservation.ext
    · rfl
    · apply nativeGraph.publicStore_congr
      intro field visible
      cases field with
      | inl input => exact Fin.elim0 input
      | inr event =>
          fin_cases event
          · exact False.elim visible
          all_goals rfl
  · apply EventGraph.PlayerObservation.ext
    · rfl
    · apply nativeGraph.playerStore_congr
      intro field visible
      cases field with
      | inl input => exact Fin.elim0 input
      | inr event =>
          fin_cases event
          · exact (foreign visible.symm).elim
          all_goals rfl
    · fin_cases who <;> first | exact (foreign rfl).elim | rfl
  · fin_cases who <;> first | exact (foreign rfl).elim | rfl

theorem association_input_hidden (who : Player) (foreign : who ≠ alice) :
    ((included false).recall who, (included false).observe app who) =
      ((included true).recall who, (included true).observe app who) := by
  apply Prod.ext
  · fin_cases who <;> first | exact (foreign rfl).elim | rfl
  · exact association_hidden who foreign

def prefixPlayers (bit : Bool) : Player → app.Policy := fun who _ view =>
  if who = alice then
    if view.application.publicView.serviceGrant = some aliceBinding then FinDist.pure associate
    else FinDist.pure (certifiedOffer bit)
  else FinDist.pure ⟨none⟩

theorem prefixPlayers_available (bit : Bool) (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) (response : app.Action)
    (supported : response ∈ (prefixPlayers bit who past view).support) :
    response ∈ menu.actions who past view := by
  unfold prefixPlayers at supported
  split at supported
  · rename_i same
    subst who
    split at supported
    · cases FinDist.mem_support_pure.mp supported
      exact associate_available past view
    · cases FinDist.mem_support_pure.mp supported
      exact certifiedOffer_available bit past view
  · cases FinDist.mem_support_pure.mp supported
    change (⟨none⟩ : app.Action) ∈ (nativeBounds.rawMenu nativeRuntime leaks).actions who past view
    rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
    trivial

private theorem prefix_first (bit : Bool) :
    nativeRuntime.interactionStep leaks (prefixPlayers bit) network (.player alice) initial =
      FinDist.pure (first bit) := by
  simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
    ReactiveApplication.dispatch, activation_law, FinDist.pure_bind,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume, ReactiveApplication.invoke]
  change (FinDist.pure (certifiedOffer bit)).map _ = _
  rw [FinDist.map_pure]
  rfl

private theorem prefix_bob (bit : Bool) :
    nativeRuntime.interactionStep leaks (prefixPlayers bit) network (.player bob) (first bit) =
      FinDist.pure (reacted bit) := by
  simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
    ReactiveApplication.dispatch, bob_activation, FinDist.pure_bind,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume, ReactiveApplication.invoke]
  change (FinDist.pure (⟨none⟩ : app.Action)).map _ = _
  rw [FinDist.map_pure]
  rfl

private theorem prefix_offer (bit : Bool) :
    nativeRuntime.runInteractionPlan leaks (prefixPlayers bit) network
      [.grant aliceBinding, .player alice] (reacted bit) = FinDist.pure (offered bit) := by
  have combined : nativeRuntime.runInteractionPlan leaks (prefixPlayers bit) network
      [.grant aliceBinding, .player alice] (reacted bit) =
      (((reacted bit).environmentStep app (.application (.grant aliceBinding))).bind
        fun next => next.environmentStep app (.activate alice)).bind
          (app.invoke (prefixPlayers bit) alice) := by
    simp only [runInteractionPlan, FinDist.bind_pure, interactionStep, interactionInstruction,
      FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
      ReactiveApplication.resume, FinDist.bind_bind]
    rfl
  rw [combined, beforeOffer_law, FinDist.pure_bind]
  change (FinDist.pure associate).map _ = _
  rw [FinDist.map_pure]
  rfl

private theorem prefix_include (bit : Bool) :
    nativeRuntime.interactionStep leaks (prefixPlayers bit) network
      (.includeLatest aliceBinding alice) (offered bit) = FinDist.pure (included bit) := by
  simp only [interactionStep, interactionInstruction, association_selected,
    FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
  change ((offered bit).environmentStep app (.include (alice, 1))).bind FinDist.pure = _
  rw [FinDist.bind_pure, association_inclusion]

/-- Both values reach their indistinguishable accepted-association states
through the first five instructions of the unchanged service calendar, using
responses admitted in the complete native menu. -/
theorem five_rounds (bit : Bool) :
    nativeRuntime.runInteractionPlan leaks (prefixPlayers bit) network
      (nativePlan.take 5) initial = FinDist.pure (included bit) := by
  change nativeRuntime.runInteractionPlan leaks (prefixPlayers bit) network
    [.player alice, .player bob, .grant aliceBinding, .player alice,
      .includeLatest aliceBinding alice] initial = _
  rw [runInteractionPlan, prefix_first, FinDist.pure_bind,
    runInteractionPlan, prefix_bob, FinDist.pure_bind]
  change nativeRuntime.runInteractionPlan leaks (prefixPlayers bit) network
    ([.grant aliceBinding, .player alice] ++ [.includeLatest aliceBinding alice]) (reacted bit) = _
  rw [runInteractionPlan_append, prefix_offer, FinDist.pure_bind,
    runInteractionPlan, prefix_include, FinDist.pure_bind]
  rfl

/-- Restoring the observation rule enables a distinction absent from the
restricted prefix. Both sides use the same candidate and certified payload.
The certificate is privately observed before anything is published. -/
theorem observation_feature_contrast (bit : Bool) :
    (nativeRuntime.packetEvidence leaks).observe ((bobInput bit).observe app bob) = [] ∧
      ReactiveAssociationEvidence.opening bit ∈
        (nativeRuntime.packetEvidence nativeLeaks).observe
          ((ReactiveAssociationEvidence.observed bit).observe nativeApp bob) ∧
      (ReactiveAssociationEvidence.observed bit).network.ledger = [] :=
  ⟨(first_packet bit).2, (ReactiveAssociationEvidence.proof_before_association bit).1, rfl⟩

end VegasTests.SelectiveAssociation.Restricted
