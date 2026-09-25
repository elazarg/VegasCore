/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedStoreSymmetry
import VegasTests.SelectiveAssociationRestrictedPrefix

/-! # Paired native prefixes before the guessing decisions

The proofs map certificates on the existing network while preserving envelope
identifiers, call bodies, broadcaster identities, and scheduling operations.
Alice's hidden candidate and binding are changed together. Other players'
literal responses are retained; a statement about their unchanged inputs must
also account for certificates they have actually observed.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted.PrefixSymmetry

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def input (selected : Handle nativeGraph)
    (before : NetworkInput Player (WitnessedPacket nativeGraph)) :
    NetworkInput Player (WitnessedPacket nativeGraph) :=
  { before with envelope := CandidateFlip.message selected before.envelope }

def network (selected : Handle nativeGraph)
    (before : MessageNetwork Player (WitnessedPacket nativeGraph)) :
    MessageNetwork Player (WitnessedPacket nativeGraph) where
  pending := before.pending.map (CandidateFlip.message selected)
  ledger := before.ledger.map (CandidateFlip.message selected)
  leaked who := (before.leaked who).map (CandidateFlip.message selected)
  inputs := before.inputs.map (input selected)
  nextSerial := before.nextSerial

theorem network_known (selected : Handle nativeGraph)
    (before : MessageNetwork Player (WitnessedPacket nativeGraph)) (who : Player) :
    (network selected before).known who =
      (before.known who).map (CandidateFlip.message selected) := by
  have own : ((before.inputs.map (input selected)).filterMap fun sent =>
      if sent.broadcaster = who then some sent.envelope else none) =
    (before.inputs.filterMap fun sent =>
      if sent.broadcaster = who then some sent.envelope else none).map
        (CandidateFlip.message selected) := by
    induction before.inputs with
    | nil => rfl
    | cons head tail ih =>
        by_cases authored : head.broadcaster = who <;>
          simp [input, authored, ih]
  simp only [MessageNetwork.known, network, own, List.map_append]

theorem network_lookup (selected : Handle nativeGraph)
    (before : MessageNetwork Player (WitnessedPacket nativeGraph)) (id : MessageId Player) :
    (network selected before).lookup id =
      (before.lookup id).map (CandidateFlip.message selected) :=
  CandidateFlip.find_message selected before.pending id

theorem network_submit (selected : Handle nativeGraph)
    (before : MessageNetwork Player (WitnessedPacket nativeGraph)) (who : Player)
    (sent : WitnessedPacket nativeGraph) :
    (network selected before).submit who (CandidateFlip.packet selected sent) =
      (CandidateFlip.message selected (before.submit who sent).1,
        network selected (before.submit who sent).2) := by
  simp only [MessageNetwork.submit, network, List.map_append, List.map_cons, List.map_nil,
    input, CandidateFlip.message]

theorem network_replay (selected : Handle nativeGraph)
    (before : MessageNetwork Player (WitnessedPacket nativeGraph)) (who : Player)
    (id : MessageId Player) :
    (network selected before).replay who id =
      ((before.replay who id).1.map (CandidateFlip.message selected),
        network selected (before.replay who id).2) := by
  simp only [MessageNetwork.replay, network_known, CandidateFlip.find_message]
  cases (before.known who).find? (fun sent => sent.id = id) <;>
    simp [network, input]

theorem removeFirst (selected : Handle nativeGraph) (id : MessageId Player)
    (sent : List (Message Player (WitnessedPacket nativeGraph))) :
    MessagePool.removeFirst id (sent.map (CandidateFlip.message selected)) =
      (MessagePool.removeFirst id sent).map (CandidateFlip.message selected) := by
  induction sent with
  | nil => rfl
  | cons head tail ih =>
      by_cases same : head.id = id <;>
        simp [MessagePool.removeFirst, CandidateFlip.message_id, same, ih]

theorem network_includePending (selected : Handle nativeGraph)
    (before : MessageNetwork Player (WitnessedPacket nativeGraph)) (id : MessageId Player) :
    (network selected before).includePending id =
      ((before.includePending id).1.map (CandidateFlip.message selected),
        network selected (before.includePending id).2) := by
  simp only [MessageNetwork.includePending, network_lookup]
  cases before.lookup id <;>
    simp [network, removeFirst]

theorem latest (selected : Handle nativeGraph) (first second : app.Execution)
    (same : second.network = network selected first.network)
    (event : nativeGraph.EventId) (who : Player) :
    nativeRuntime.reactiveLatest leaks event who (second.observeEnvironment app) =
      nativeRuntime.reactiveLatest leaks event who (first.observeEnvironment app) := by
  let selectedPacket (execution : app.Execution) :=
    (execution.observeEnvironment app).network.pending.reverse.find? fun sent =>
      sent.sender = who ∧ sent.payload.call.event? nativeGraph = some event ∧
        (execution.observeEnvironment app).Unpublished app sent.id
  have paired : selectedPacket second =
      (selectedPacket first).map (CandidateFlip.message selected) := by
    dsimp only [selectedPacket, ReactiveApplication.Execution.observeEnvironment,
      MessageNetwork.publicView, ReactiveApplication.EnvironmentView.Unpublished]
    simp only [same, network, ← List.map_reverse, List.find?_map, List.map_map,
      Function.comp_def, CandidateFlip.message, CandidateFlip.packet, Message.sender]
    congr 2
  unfold reactiveLatest
  split <;> split
  · rfl
  · rename_i _ secondNone _ sent firstSome
    have absent : selectedPacket second = none := by
      convert secondNone using 1
    have present : selectedPacket first = some sent := by
      convert firstSome using 1
    rw [absent, present] at paired
    cases paired
  · rename_i _ sent secondSome _ firstNone
    have present : selectedPacket second = some sent := by
      convert secondSome using 1
    have absent : selectedPacket first = none := by
      convert firstNone using 1
    rw [absent, present] at paired
    cases paired
  · rename_i _ secondSent secondSome _ firstSent firstSome
    have left : selectedPacket second = some secondSent := by
      convert secondSome using 1
    have right : selectedPacket first = some firstSent := by
      convert firstSome using 1
    rw [left, right, Option.map_some] at paired
    have identified := congrArg Message.id (Option.some.inj paired)
    exact congrArg ReactiveApplication.Command.include identified

/-- Only Alice's private recall is omitted from this proof relation. The two
guessers retain their full literal action and observation recall. -/
structure Related (selected : Handle nativeGraph) (first second : app.Execution) : Prop where
  application : second.application = StoreFlip.state selected first.application
  network : second.network = network selected first.network
  receipts : second.receipts = first.receipts
  bobRecall : second.recall bob = first.recall bob
  carolRecall : second.recall carol = first.recall carol
  environmentCount : second.environmentRecall.length = first.environmentRecall.length

theorem submission_application (selected : Handle nativeGraph) (before : State nativeGraph)
    (who : Player) (submitted : WitnessedSubmission nativeGraph) :
    app.submit (StoreFlip.state selected before) who (CandidateFlip.submission selected submitted) =
      StoreFlip.state selected (app.submit before who submitted) := by
  change submitStep ((CandidateFlip.call selected submitted.call).register
      (StoreFlip.state selected before) who) who
      (CandidateFlip.call selected submitted.call).packet =
    StoreFlip.state selected (submitStep (submitted.call.register before who)
      who submitted.call.packet)
  rw [StoreFlip.register, CandidateFlip.call_packet, StoreFlip.submitStep_state]

theorem respond_application (selected : Handle nativeGraph) (first second : app.Execution)
    (same : second.application = StoreFlip.state selected first.application)
    (who : Player) (response : app.Action) :
    (second.respond app who (CandidateFlip.action selected response)).application =
      StoreFlip.state selected (first.respond app who response).application := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact same
  | some transmission =>
      cases transmission with
      | replay => exact same
      | submit submitted =>
          change app.submit second.application who (CandidateFlip.submission selected submitted) = _
          rw [same, submission_application]
          rfl

theorem respond_network (selected : Handle nativeGraph) (first second : app.Execution)
    (sameApplication : second.application = StoreFlip.state selected first.application)
    (sameNetwork : second.network = network selected first.network)
    (who : Player) (response : app.Action) :
    (second.respond app who (CandidateFlip.action selected response)).network =
      network selected (first.respond app who response).network := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact sameNetwork
  | some transmission =>
      cases transmission with
      | replay id =>
          change (second.network.replay who id).2 = network selected (first.network.replay who id).2
          rw [sameNetwork, network_replay]
      | submit submitted =>
          change (second.network.submit who
            ((CandidateFlip.submission selected submitted).emit
              (app.submit second.application who (CandidateFlip.submission selected submitted))
              who (second.network.known who))).2 =
            network selected (first.network.submit who
              (submitted.emit (app.submit first.application who submitted)
                who (first.network.known who))).2
          rw [sameApplication, submission_application, sameNetwork, network_known, StoreFlip.emit,
            network_submit]

private theorem respond_receipts (execution : app.Execution) (who : Player)
    (response : app.Action) :
    (execution.respond app who response).receipts = execution.receipts := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission => cases transmission <;> rfl

theorem related_respond_alice (selected : Handle nativeGraph) (first second : app.Execution)
    (related : Related selected first second) (response : app.Action) :
    Related selected (first.respond app alice response)
      (second.respond app alice (CandidateFlip.action selected response)) := by
  refine ⟨respond_application selected first second related.application alice response,
    respond_network selected first second related.application related.network alice response,
    ?_, ?_, ?_, ?_⟩
  · rw [respond_receipts, respond_receipts, related.receipts]
  · rw [app.respond_recall_other second alice bob (by decide),
      app.respond_recall_other first alice bob (by decide), related.bobRecall]
  · rw [app.respond_recall_other second alice carol (by decide),
      app.respond_recall_other first alice carol (by decide), related.carolRecall]
  · rw [app.respond_environmentRecall, app.respond_environmentRecall, related.environmentCount]

theorem related_known_ids (selected : Handle nativeGraph) (first second : app.Execution)
    (related : Related selected first second) (who : Player)
    (firstRecall : first.InputRecall app) (secondRecall : second.InputRecall app) :
    (ReactiveApplication.ResponseMenu.knownPackets (first.recall who)
      (first.observe app who)).map Message.id =
    (ReactiveApplication.ResponseMenu.knownPackets (second.recall who)
      (second.observe app who)).map Message.id := by
  have firstKnown := app.known_from_recall first who firstRecall
  have secondKnown := app.known_from_recall second who secondRecall
  change first.network.known who = ReactiveApplication.ResponseMenu.knownPackets
    (first.recall who) (first.observe app who) at firstKnown
  change second.network.known who = ReactiveApplication.ResponseMenu.knownPackets
    (second.recall who) (second.observe app who) at secondKnown
  rw [← firstKnown, ← secondKnown, related.network, network_known]
  exact (CandidateFlip.message_ids selected (first.network.known who)).symm

def NoObservedCertificate (selected : Handle nativeGraph) (execution : app.Execution)
    (who : Player) : Prop :=
  ∀ sent ∈ execution.network.leaked who ++ execution.network.ledger, ∀ evidence,
    sent.payload.evidence = some evidence → evidence.handle ≠ selected

theorem related_observe (selected : Handle nativeGraph) (owner : selected.1 = alice)
    (first second : app.Execution) (related : Related selected first second)
    (who : Player) (different : alice ≠ who) (hidden : NoObservedCertificate selected first who) :
    second.observe app who = first.observe app who := by
  have leaked : (first.network.leaked who).map (CandidateFlip.message selected) =
      first.network.leaked who :=
    CandidateFlip.messages_eq_of_no_certificate selected _ fun sent member =>
      hidden sent (List.mem_append_left _ member)
  have ledger : first.network.ledger.map (CandidateFlip.message selected) =
      first.network.ledger :=
    CandidateFlip.messages_eq_of_no_certificate selected _ fun sent member =>
      hidden sent (List.mem_append_right _ member)
  have candidates : (fun slot =>
      (CandidateFlip.catalogue selected first.application.candidates).lookup (who, slot)) =
      fun slot => first.application.candidates.lookup (who, slot) := by
    funext slot
    exact CandidateFlip.catalogue_lookup_other_owner selected first.application.candidates
      who (owner ▸ different) slot
  unfold ReactiveApplication.Execution.observe
  rw [related.application, related.network, related.receipts]
  congr 1
  · simp only [MessageNetwork.observe, network, leaked, ledger]
  · change (⟨who, _, _, _⟩ : ReactivePlayerView nativeGraph) = ⟨who, _, _, _⟩
    simp only [StoreFlip.state, State.publicView, StoreFlip.publicObserve,
      StoreFlip.playerObserve first.application.config who different, candidates]

theorem related_guesser_input (selected : Handle nativeGraph) (owner : selected.1 = alice)
    (first second : app.Execution) (related : Related selected first second)
    (who : Player) (guesser : who = bob ∨ who = carol)
    (hidden : NoObservedCertificate selected first who) :
    (second.recall who, second.observe app who) = (first.recall who, first.observe app who) := by
  rcases guesser with rfl | rfl
  · rw [related.bobRecall,
      related_observe selected owner first second related bob (by decide) hidden]
  · rw [related.carolRecall,
      related_observe selected owner first second related carol (by decide) hidden]

def NoKnownCertificate (selected : Handle nativeGraph) (execution : app.Execution)
    (who : Player) : Prop :=
  ∀ sent ∈ execution.network.known who, ∀ evidence,
    sent.payload.evidence = some evidence → evidence.handle ≠ selected

theorem related_known (selected : Handle nativeGraph) (first second : app.Execution)
    (related : Related selected first second) (who : Player)
    (hidden : NoKnownCertificate selected first who) :
    second.network.known who = first.network.known who := by
  rw [related.network, network_known]
  exact CandidateFlip.messages_eq_of_no_certificate selected _ hidden

theorem submission_other_application (selected : Handle nativeGraph)
    (before : State nativeGraph) (who : Player) (different : selected.1 ≠ who)
    (submitted : WitnessedSubmission nativeGraph) :
    app.submit (StoreFlip.state selected before) who submitted =
      StoreFlip.state selected (app.submit before who submitted) := by
  change submitStep (submitted.call.register (StoreFlip.state selected before) who)
      who submitted.call.packet = _
  rw [StoreFlip.register_other_owner selected submitted.call before who different,
    StoreFlip.submitStep_state]
  rfl

theorem submission_other_packet (selected : Handle nativeGraph)
    (before : State nativeGraph) (who : Player) (different : selected.1 ≠ who)
    (known : List (Message Player (WitnessedPacket nativeGraph)))
    (submitted : WitnessedSubmission nativeGraph) :
    app.packet (app.submit (StoreFlip.state selected before) who submitted) who known submitted =
      app.packet (app.submit before who submitted) who known submitted := by
  rw [submission_other_application selected before who different submitted]
  apply WitnessedSubmission.emit_local
  exact CandidateFlip.catalogue_lookup_other_owner selected _ who different

theorem submission_packet_fixed (selected : Handle nativeGraph)
    (before : State nativeGraph) (who : Player) (different : selected.1 ≠ who)
    (known : List (Message Player (WitnessedPacket nativeGraph)))
    (hidden : ∀ sent ∈ known, ∀ evidence,
      sent.payload.evidence = some evidence → evidence.handle ≠ selected)
    (submitted : WitnessedSubmission nativeGraph) :
    CandidateFlip.packet selected
        (app.packet (app.submit before who submitted) who known submitted) =
      app.packet (app.submit before who submitted) who known submitted := by
  apply CandidateFlip.packet_eq_of_no_certificate
  intro evidence certified same
  rcases submitted.emit_origin (app.submit before who submitted) who known evidence certified with
    owned | received
  · exact different (same ▸ owned.1)
  · obtain ⟨sent, member, certified⟩ := received
    exact hidden sent member evidence certified same

theorem respond_other_recall (selected : Handle nativeGraph)
    (first second : app.Execution) (related : Related selected first second)
    (who observer : Player) (different : selected.1 ≠ who)
    (sameRecall : second.recall observer = first.recall observer)
    (sameView : second.observe app who = first.observe app who)
    (hidden : NoKnownCertificate selected first who) (response : app.Action) :
    (second.respond app who response).recall observer =
      (first.respond app who response).recall observer := by
  by_cases self : observer = who
  · subst observer
    have known := related_known selected first second related who hidden
    have serial : second.network.nextSerial = first.network.nextSerial := by
      rw [related.network]
      rfl
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => simp only [ReactiveApplication.Execution.respond, ↓reduceIte, sameRecall, sameView]
    | some transmission =>
        cases transmission with
        | replay id =>
            simp only [ReactiveApplication.Execution.respond, MessageNetwork.replay, known,
              ↓reduceIte, sameRecall, sameView]
            cases (first.network.known who).find? (fun sent => sent.id = id) <;> rfl
        | submit submitted =>
            simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit,
              ↓reduceIte, related.application,
              submission_other_packet selected first.application who different,
              known, serial, sameRecall, sameView]
  · rw [app.respond_recall_other second who observer self,
      app.respond_recall_other first who observer self, sameRecall]

theorem respond_other_network (selected : Handle nativeGraph)
    (first second : app.Execution) (related : Related selected first second)
    (who : Player) (different : selected.1 ≠ who)
    (hidden : NoKnownCertificate selected first who) (response : app.Action) :
    (second.respond app who response).network =
      network selected (first.respond app who response).network := by
  have known := related_known selected first second related who hidden
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact related.network
  | some transmission =>
      cases transmission with
      | replay id =>
          change (second.network.replay who id).2 = _
          rw [related.network, network_replay]
          rfl
      | submit submitted =>
          change (second.network.submit who
            (app.packet (app.submit second.application who submitted) who
              (second.network.known who) submitted)).2 = _
          rw [related.application, submission_other_packet selected first.application who different,
            known]
          rw [← submission_packet_fixed selected first.application who different _ hidden submitted,
            related.network, network_submit]
          rfl

theorem related_respond_other (selected : Handle nativeGraph)
    (owner : selected.1 = alice) (first second : app.Execution)
    (related : Related selected first second) (who : Player) (different : alice ≠ who)
    (unobserved : NoObservedCertificate selected first who)
    (unknown : NoKnownCertificate selected first who) (response : app.Action) :
    Related selected (first.respond app who response) (second.respond app who response) := by
  have foreign : selected.1 ≠ who := owner ▸ different
  have sameView := related_observe selected owner first second related who different unobserved
  refine ⟨?_, respond_other_network selected first second related who foreign unknown response,
    ?_, respond_other_recall selected first second related who bob foreign related.bobRecall
      sameView unknown response,
    respond_other_recall selected first second related who carol foreign related.carolRecall
      sameView unknown response, ?_⟩
  · rcases response with ⟨transmission⟩
    cases transmission with
    | none => exact related.application
    | some transmission =>
        cases transmission with
        | replay => exact related.application
        | submit submitted =>
            change app.submit second.application who submitted = _
            rw [related.application, submission_other_application selected _ who foreign]
            rfl
  · rw [respond_receipts, respond_receipts, related.receipts]
  · rw [app.respond_environmentRecall, app.respond_environmentRecall, related.environmentCount]

theorem related_activate (selected : Handle nativeGraph) (first second : app.Execution)
    (related : Related selected first second) (who : Player) :
    Related selected (activate first who) (activate second who) := by
  refine ⟨related.application, related.network, related.receipts,
    related.bobRecall, related.carolRecall, ?_⟩
  simpa only [activate, List.length_append, List.length_singleton] using
    congrArg (· + 1) related.environmentCount

/-- Inclusion preserves the paired execution whenever the actual application
handler commutes on the selected envelope. No condition on unrelated pending
packets, including rejected or wrongly addressed packets, is needed. -/
theorem related_includePending (selected : Handle nativeGraph) (first second : app.Execution)
    (related : Related selected first second) (id : MessageId Player)
    (handler : ∀ sent, first.network.lookup id = some sent →
      app.handle second.application (CandidateFlip.message selected sent) =
        (app.handle first.application sent).map (StoreFlip.state selected)) :
    Related selected (first.includePending app id) (second.includePending app id) := by
  have pairedNetwork : (second.network.includePending id).2 =
      network selected (first.network.includePending id).2 := by
    rw [related.network, network_includePending]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact (app.includePending_network second id).trans
        (pairedNetwork.trans (congrArg (network selected)
          (app.includePending_network first id).symm))
    | skip
  all_goals cases found : first.network.lookup id with
    | none =>
        have paired : second.network.lookup id = none := by
          rw [related.network, network_lookup, found]
          rfl
        simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          found, paired]
        first | exact related.application | exact related.receipts | exact related.bobRecall
              | exact related.carolRecall | exact related.environmentCount
    | some sent =>
        have paired : second.network.lookup id = some (CandidateFlip.message selected sent) := by
          rw [related.network, network_lookup, found]
          rfl
        have handled := handler sent found
        simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          found, paired, handled]
        cases app.handle first.application sent <;>
          simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
            Option.isSome_none, Option.isSome_some, related.application, related.receipts,
            related.bobRecall, related.carolRecall, related.environmentCount]

private theorem application_shape (execution : app.Execution)
    (command : EnvironmentCommand nativeGraph) :
    Prefix.environmentResult execution (.application command) =
      { execution with
        application := (Prefix.environmentResult execution (.application command)).application
        environmentRecall := execution.environmentRecall ++
          [⟨execution.observeEnvironment app, .application command⟩] } := by
  apply Prefix.environmentResult_eq
  simp only [ReactiveApplication.Execution.environmentStep,
    Prefix.environmentResult_application_law, FinDist.map_pure]

theorem related_application (selected : Handle nativeGraph) (first second : app.Execution)
    (related : Related selected first second) (command : EnvironmentCommand nativeGraph)
    (commutes : app.environment (StoreFlip.state selected first.application) command =
      (app.environment first.application command).map (StoreFlip.state selected)) :
    Related selected (Prefix.environmentResult first (.application command))
      (Prefix.environmentResult second (.application command)) := by
  have pair : app.environment second.application command =
      (app.environment first.application command).map (StoreFlip.state selected) :=
    related.application ▸ commutes
  rw [Prefix.environmentResult_application_law, Prefix.environmentResult_application_law,
    FinDist.map_pure] at pair
  have sameState : (Prefix.environmentResult second (.application command)).application =
      StoreFlip.state selected
        (Prefix.environmentResult first (.application command)).application :=
    FinDist.mem_support_pure.mp (pair ▸ FinDist.mem_support_pure.mpr rfl)
  rw [application_shape first command, application_shape second command]
  refine ⟨sameState, related.network, related.receipts, related.bobRecall, related.carolRecall, ?_⟩
  simpa only [List.length_append, List.length_singleton] using
    congrArg (· + 1) related.environmentCount

theorem related_grant (selected : Handle nativeGraph) (first second : app.Execution)
    (related : Related selected first second) (event : nativeGraph.EventId) :
    Related selected (Prefix.environmentResult first (.application (.grant event)))
      (Prefix.environmentResult second (.application (.grant event))) :=
  related_application selected first second related (.grant event)
    (StoreFlip.environment_grant selected first.application event)

theorem related_tick (selected : Handle nativeGraph) (first second : app.Execution)
    (related : Related selected first second) :
    Related selected (Prefix.environmentResult first (.application .advanceClock))
      (Prefix.environmentResult second (.application .advanceClock)) :=
  related_application selected first second related .advanceClock
    (StoreFlip.environment_tick selected first.application)

theorem related_expire_binding (selected : Handle nativeGraph) (first second : app.Execution)
    (related : Related selected first second) (who : Player) :
    Related selected
      (Prefix.environmentResult first (.application (.expire (nativeBindingEvent who))))
      (Prefix.environmentResult second (.application (.expire (nativeBindingEvent who)))) :=
  related_application selected first second related (.expire (nativeBindingEvent who))
    (StoreFlip.environment_expire_binding selected first.application (nativeBindingEvent who)
      who (native_binding_output who) (native_binding_code who) (native_binding_node who))

theorem related_wait (selected : Handle nativeGraph) (first second : app.Execution)
    (related : Related selected first second) :
    Related selected (Prefix.environmentResult first .wait)
      (Prefix.environmentResult second .wait) := by
  have shape (execution : app.Execution) : Prefix.environmentResult execution .wait =
      { execution with environmentRecall := execution.environmentRecall ++
        [⟨execution.observeEnvironment app, .wait⟩] } :=
    Prefix.environmentResult_eq execution _ _ (by
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure])
  rw [shape first, shape second]
  refine ⟨related.application, related.network, related.receipts, related.bobRecall,
    related.carolRecall, ?_⟩
  simpa only [List.length_append, List.length_singleton] using
    congrArg (· + 1) related.environmentCount

theorem related_include (selected : Handle nativeGraph) (first second : app.Execution)
    (related : Related selected first second) (id : MessageId Player)
    (handler : ∀ sent, first.network.lookup id = some sent →
      app.handle second.application (CandidateFlip.message selected sent) =
        (app.handle first.application sent).map (StoreFlip.state selected)) :
    Related selected (Prefix.environmentResult first (.include id))
      (Prefix.environmentResult second (.include id)) := by
  have shape (execution : app.Execution) : Prefix.environmentResult execution (.include id) =
      { execution.includePending app id with environmentRecall := execution.environmentRecall ++
        [⟨execution.observeEnvironment app, .include id⟩] } :=
    Prefix.environmentResult_eq execution _ _ (by
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure])
  rw [shape first, shape second]
  have included := related_includePending selected first second related id handler
  refine ⟨included.application, included.network, included.receipts, included.bobRecall,
    included.carolRecall, ?_⟩
  simpa only [List.length_append, List.length_singleton] using
    congrArg (· + 1) related.environmentCount

theorem related_includeLatest (selected : Handle nativeGraph) (first second : app.Execution)
    (related : Related selected first second) (event : nativeGraph.EventId) (who : Player)
    (handler : ∀ id, nativeRuntime.reactiveLatest leaks event who
        (first.observeEnvironment app) = .include id →
      ∀ sent, first.network.lookup id = some sent →
        app.handle second.application (CandidateFlip.message selected sent) =
          (app.handle first.application sent).map (StoreFlip.state selected)) :
    Related selected (Prefix.includeLatest first event who)
      (Prefix.includeLatest second event who) := by
  unfold Prefix.includeLatest
  rw [latest selected first second related.network]
  cases command : nativeRuntime.reactiveLatest leaks event who (first.observeEnvironment app) with
  | wait => exact related_wait selected first second related
  | «include» id => exact related_include selected first second related id (handler id command)
  | activate | application =>
      unfold reactiveLatest at command
      split at command <;> cases command

theorem related_initial (selected : Handle nativeGraph) : Related selected initial initial := by
  have fresh (who : Player) (slot : CandidateSlot nativeGraph) :
      nativeInitial.candidates.table who slot = .fresh := by
    change (State.initial nativeInputs).candidates.lookup (who, slot) = .fresh
    rw [State.initial_candidate]
    cases slot with
    | initial input => exact Fin.elim0 input
    | prepared => rfl
  have catalogue : CandidateFlip.catalogue selected nativeInitial.candidates =
      nativeInitial.candidates := by
    apply congrArg CommitmentCandidates.mk
    funext who slot
    change (if (who, slot) = selected then
      CandidateFlip.candidate (nativeInitial.candidates.table who slot)
      else nativeInitial.candidates.table who slot) = nativeInitial.candidates.table who slot
    simp only [fresh, CandidateFlip.candidate]
    split <;> rfl
  have config : StoreFlip.config nativeInitial.config = nativeInitial.config := rfl
  have state : StoreFlip.state selected nativeInitial = nativeInitial := by
    change { nativeInitial with
      config := StoreFlip.config nativeInitial.config
      candidates := CandidateFlip.catalogue selected nativeInitial.candidates } = nativeInitial
    rw [config, catalogue]
  exact ⟨state.symm, rfl, rfl, rfl, rfl, rfl⟩

def flipCarol (selected : Handle nativeGraph) (responses : Prefix.CarolResponses) :
    Prefix.CarolResponses where
  alicePrelude := CandidateFlip.action selected responses.alicePrelude
  bobPrelude := responses.bobPrelude
  aliceBinding := CandidateFlip.action selected responses.aliceBinding

def flipBob (selected : Handle nativeGraph) (responses : Prefix.BobResponses) :
    Prefix.BobResponses where
  beforeCarol := flipCarol selected responses.beforeCarol
  carolBinding := responses.carolBinding

theorem flipCarol_involutive (selected : Handle nativeGraph) :
    Function.Involutive (flipCarol selected) := by
  intro responses
  cases responses with
  | mk first second third =>
      simp only [flipCarol, CandidateFlip.action_involutive selected first,
        CandidateFlip.action_involutive selected third]

theorem flipBob_involutive (selected : Handle nativeGraph) :
    Function.Involutive (flipBob selected) := by
  intro responses
  cases responses with
  | mk first second => simp only [flipBob, flipCarol_involutive selected first]

theorem related_bobPrelude (selected : Handle nativeGraph) (response : app.Action) :
    Related selected (Prefix.bobPreludeInput response)
      (Prefix.bobPreludeInput (CandidateFlip.action selected response)) :=
  related_activate selected _ _
    (related_respond_alice selected _ _
      (related_activate selected _ _ (related_initial selected) alice) response) bob

theorem bobPrelude_known (response : app.Action) :
    (Prefix.bobPreludeInput response).network.known bob = [] := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | replay id =>
          simp only [Prefix.bobPreludeInput, activate, ReactiveApplication.Execution.respond,
            initial, ReactiveApplication.Execution.initial, MessageNetwork.replay,
            MessageNetwork.known, MessageNetwork.empty, List.filterMap_nil,
            List.nil_append, List.find?_nil]
      | submit submitted => rfl

theorem bobPrelude_unobserved (selected : Handle nativeGraph) (response : app.Action) :
    NoObservedCertificate selected (Prefix.bobPreludeInput response) bob := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact fun _ member => nomatch member
  | some transmission =>
      cases transmission with
      | replay id =>
          simp only [NoObservedCertificate, Prefix.bobPreludeInput, activate,
            ReactiveApplication.Execution.respond, initial, ReactiveApplication.Execution.initial,
            MessageNetwork.replay, MessageNetwork.known, MessageNetwork.empty,
            List.filterMap_nil, List.nil_append, List.find?_nil, List.not_mem_nil, false_implies]
          exact fun _ => True.intro
      | submit => exact fun _ member => nomatch member

theorem related_aliceInput (selected : Handle nativeGraph) (owner : selected.1 = alice)
    (first second : app.Action) :
    Related selected (Prefix.aliceInput first second)
      (Prefix.aliceInput (CandidateFlip.action selected first) second) := by
  apply related_activate
  apply related_grant
  apply related_respond_other selected owner _ _ (related_bobPrelude selected first)
    bob (by decide) (bobPrelude_unobserved selected first)
  intro sent member
  rw [bobPrelude_known] at member
  exact False.elim (List.not_mem_nil member)

theorem related_aliceSubmitted (selected : Handle nativeGraph) (owner : selected.1 = alice)
    (responses : Prefix.CarolResponses) :
    Related selected
      ((Prefix.aliceInput responses.alicePrelude responses.bobPrelude).respond app alice
        responses.aliceBinding)
      ((Prefix.aliceInput (flipCarol selected responses).alicePrelude
        (flipCarol selected responses).bobPrelude).respond app alice
        (flipCarol selected responses).aliceBinding) :=
  related_respond_alice selected _ _
    (related_aliceInput selected owner responses.alicePrelude responses.bobPrelude)
    responses.aliceBinding

/-- The accepted Alice envelope is the only application step requiring a
selected-handle premise. All surrounding raw responses and maintenance steps
have already been related independently. -/
theorem related_carolInput (selected : Handle nativeGraph) (responses : Prefix.CarolResponses)
    (included : Related selected
      (Prefix.includeLatest
        ((Prefix.aliceInput responses.alicePrelude responses.bobPrelude).respond app alice
          responses.aliceBinding) aliceBinding alice)
      (Prefix.includeLatest
        ((Prefix.aliceInput (flipCarol selected responses).alicePrelude
          (flipCarol selected responses).bobPrelude).respond app alice
          (flipCarol selected responses).aliceBinding) aliceBinding alice)) :
    Related selected (Prefix.carolInput responses)
      (Prefix.carolInput (flipCarol selected responses)) := by
  apply related_activate
  apply related_grant
  exact related_expire_binding selected _ _ (related_tick selected _ _ included) alice

theorem related_carolSubmitted (selected : Handle nativeGraph) (owner : selected.1 = alice)
    (responses : Prefix.BobResponses)
    (before : Related selected (Prefix.carolInput responses.beforeCarol)
      (Prefix.carolInput (flipCarol selected responses.beforeCarol)))
    (unobserved : NoObservedCertificate selected (Prefix.carolInput responses.beforeCarol) carol)
    (unknown : NoKnownCertificate selected (Prefix.carolInput responses.beforeCarol) carol) :
    Related selected
      ((Prefix.carolInput responses.beforeCarol).respond app carol responses.carolBinding)
      ((Prefix.carolInput (flipBob selected responses).beforeCarol).respond app carol
        (flipBob selected responses).carolBinding) :=
  related_respond_other selected owner _ _ before carol (by decide) unobserved unknown
    responses.carolBinding

theorem related_bobInput (selected : Handle nativeGraph) (responses : Prefix.BobResponses)
    (included : Related selected
      (Prefix.includeLatest
        ((Prefix.carolInput responses.beforeCarol).respond app carol responses.carolBinding)
        carolBinding carol)
      (Prefix.includeLatest
        ((Prefix.carolInput (flipBob selected responses).beforeCarol).respond app carol
          (flipBob selected responses).carolBinding) carolBinding carol)) :
    Related selected (Prefix.bobInput responses)
      (Prefix.bobInput (flipBob selected responses)) := by
  apply related_activate
  apply related_grant
  exact related_expire_binding selected _ _
    (related_tick selected _ _ (related_tick selected _ _ included)) carol

theorem related_accepted (selected : Handle nativeGraph) (first second : app.Execution)
    (related : Related selected first second) :
    second.application.accepted = first.application.accepted := by
  rw [related.application]
  rfl

theorem related_aliceValue (selected : Handle nativeGraph) (first second : app.Execution)
    (related : Related selected first second) :
    second.application.config.outputs aliceBinding =
      (first.application.config.outputs aliceBinding).map CandidateFlip.result := by
  rw [related.application]
  simp only [StoreFlip.state, StoreFlip.config]
  congr 1

end VegasTests.SelectiveAssociation.Restricted.PrefixSymmetry
