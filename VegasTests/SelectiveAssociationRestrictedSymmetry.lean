/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestricted
import Interaction.ReactiveRoundReachability

/-! # Flipping one hidden native candidate

These local transformations exchange the Boolean meanings of one candidate.
Public application calls, handles, and message identifiers stay fixed. Private
opening material and owned-certificate requests are transformed together, so a
failed request does not become a successful certificate request. Certificates
already attached to private packets are transformed as well.

An observed packet stays identical when it carries no certificate for the
selected handle. The menu permutation and emission equations below are local
lemmas; lifting them to entire histories and comparing their probabilities is a
separate obligation.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted.CandidateFlip

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def raw : Raw simpleExpr → Raw simpleExpr
  | ⟨.bool, bit⟩ => ⟨.bool, !bit⟩
  | value => value

theorem raw_involutive : Function.Involutive raw := by
  rintro ⟨ty, value⟩
  cases ty <;> simp [raw]

@[simp] theorem raw_raw (value : Raw simpleExpr) : raw (raw value) = value :=
  raw_involutive value

theorem raw_as_bool (value : Raw simpleExpr) :
    (raw value).as? .bool = (value.as? .bool).map Bool.not := by
  rcases value with ⟨ty, value⟩
  cases ty <;> simp [raw, Raw.as?]

theorem raw_available (value : Raw simpleExpr) (available : value ∈ nativeBounds.values) :
    raw value ∈ nativeBounds.values := by
  simp only [nativeBounds, Finset.mem_insert, Finset.mem_singleton] at available ⊢
  rcases available with rfl | rfl | rfl <;> simp [raw]

def fact (selected : Handle nativeGraph) (evidence : OpeningFact nativeGraph) :
    OpeningFact nativeGraph :=
  if evidence.handle = selected then { evidence with raw := raw evidence.raw } else evidence

@[simp] theorem fact_handle (selected : Handle nativeGraph) (evidence : OpeningFact nativeGraph) :
    (fact selected evidence).handle = evidence.handle := by
  unfold fact
  split <;> rfl

theorem fact_involutive (selected : Handle nativeGraph) :
    Function.Involutive (fact selected) := by
  rintro ⟨handle, value⟩
  by_cases same : handle = selected <;> simp [fact, same]

@[simp] theorem fact_fact (selected : Handle nativeGraph) (evidence : OpeningFact nativeGraph) :
    fact selected (fact selected evidence) = evidence := fact_involutive selected evidence

def request (selected : Handle nativeGraph) : EvidenceRequest nativeGraph →
    EvidenceRequest nativeGraph
  | .owned evidence => .owned (fact selected evidence)
  | other => other

theorem request_involutive (selected : Handle nativeGraph) :
    Function.Involutive (request selected) := by
  intro evidence
  cases evidence <;> simp [request]

@[simp] theorem request_request (selected : Handle nativeGraph)
    (evidence : EvidenceRequest nativeGraph) :
    request selected (request selected evidence) = evidence := request_involutive selected evidence

def call (selected : Handle nativeGraph) (submitted : Submission nativeGraph) :
    Submission nativeGraph :=
  match submitted.packet with
  | .commitment _ handle =>
      if handle = selected then { submitted with opening := submitted.opening.map raw }
      else submitted
  | _ => submitted

@[simp] theorem call_packet (selected : Handle nativeGraph) (submitted : Submission nativeGraph) :
    (call selected submitted).packet = submitted.packet := by
  cases submitted with
  | mk packet opening =>
      cases packet with
      | commitment event handle =>
          by_cases same : handle = selected <;> simp [call, same]
      | opening | withhold | malformed => rfl

theorem call_involutive (selected : Handle nativeGraph) :
    Function.Involutive (call selected) := by
  rintro ⟨packet, opening⟩
  cases packet with
  | commitment event handle =>
      by_cases same : handle = selected
      · cases opening <;> simp [call, same]
      · simp [call, same]
  | opening | withhold | malformed => rfl

@[simp] theorem call_call (selected : Handle nativeGraph) (submitted : Submission nativeGraph) :
    call selected (call selected submitted) = submitted := call_involutive selected submitted

def submission (selected : Handle nativeGraph) (submitted : WitnessedSubmission nativeGraph) :
    WitnessedSubmission nativeGraph :=
  ⟨call selected submitted.call, request selected submitted.evidence⟩

theorem submission_involutive (selected : Handle nativeGraph) :
    Function.Involutive (submission selected) := by
  rintro ⟨submitted, evidence⟩
  simp [submission]

@[simp] theorem submission_packet (selected : Handle nativeGraph)
    (submitted : WitnessedSubmission nativeGraph) :
    (submission selected submitted).call.packet = submitted.call.packet := call_packet _ _

def action (selected : Handle nativeGraph) (response : app.Action) : app.Action :=
  match response.transmission with
  | some (.submit submitted) => ⟨some (.submit (submission selected submitted))⟩
  | _ => response

theorem action_involutive (selected : Handle nativeGraph) :
    Function.Involutive (action selected) := by
  rintro ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | replay => rfl
      | submit submitted =>
          change (⟨some (.submit (submission selected (submission selected submitted)))⟩ :
            app.Action) = _
          rw [submission_involutive]

def packet (selected : Handle nativeGraph) (sent : WitnessedPacket nativeGraph) :
    WitnessedPacket nativeGraph :=
  { sent with evidence := sent.evidence.map (fact selected) }

@[simp] theorem packet_call (selected : Handle nativeGraph) (sent : WitnessedPacket nativeGraph) :
    (packet selected sent).call = sent.call := rfl

theorem packet_involutive (selected : Handle nativeGraph) :
    Function.Involutive (packet selected) := by
  rintro ⟨call, evidence⟩
  cases evidence <;> simp [packet]

def message (selected : Handle nativeGraph) (sent : Message Player (WitnessedPacket nativeGraph)) :
    Message Player (WitnessedPacket nativeGraph) :=
  { sent with payload := packet selected sent.payload }

@[simp] theorem message_id (selected : Handle nativeGraph)
    (sent : Message Player (WitnessedPacket nativeGraph)) :
    (message selected sent).id = sent.id := rfl

theorem message_involutive (selected : Handle nativeGraph) :
    Function.Involutive (message selected) := by
  rintro ⟨id, sent⟩
  change (⟨id, packet selected (packet selected sent)⟩ :
    Message Player (WitnessedPacket nativeGraph)) = _
  rw [packet_involutive]

theorem message_ids (selected : Handle nativeGraph)
    (known : List (Message Player (WitnessedPacket nativeGraph))) :
    (known.map (message selected)).map Message.id = known.map Message.id := by
  rw [List.map_map]
  rfl

def candidate : CommitmentCandidate (Raw simpleExpr) → CommitmentCandidate (Raw simpleExpr)
  | .openable value => .openable (raw value)
  | other => other

theorem candidate_involutive : Function.Involutive candidate := by
  intro value
  cases value <;> simp [candidate]

def catalogue (selected : Handle nativeGraph)
    (before : CommitmentCandidates Player (CandidateSlot nativeGraph) (Raw simpleExpr)) :
    CommitmentCandidates Player (CandidateSlot nativeGraph) (Raw simpleExpr) where
  table who slot :=
    if (who, slot) = selected then candidate (before.table who slot) else before.table who slot

private theorem catalogue_ext
    (first second : CommitmentCandidates Player (CandidateSlot nativeGraph) (Raw simpleExpr))
    (same : ∀ handle, first.lookup handle = second.lookup handle) : first = second := by
  cases first with
  | mk first =>
      cases second with
      | mk second =>
          congr 1
          funext who slot
          exact same (who, slot)

theorem catalogue_lookup (selected handle : Handle nativeGraph)
    (before : CommitmentCandidates Player (CandidateSlot nativeGraph) (Raw simpleExpr)) :
    (catalogue selected before).lookup handle =
      if handle = selected then candidate (before.lookup handle) else before.lookup handle := rfl

theorem catalogue_lookup_other_owner (selected : Handle nativeGraph)
    (before : CommitmentCandidates Player (CandidateSlot nativeGraph) (Raw simpleExpr))
    (who : Player) (different : selected.1 ≠ who) (slot : CandidateSlot nativeGraph) :
    (catalogue selected before).lookup (who, slot) = before.lookup (who, slot) := by
  rw [catalogue_lookup]
  apply ite_eq_right
  intro same
  exact different (congrArg Prod.fst same).symm

theorem catalogue_involutive (selected : Handle nativeGraph) :
    Function.Involutive (catalogue selected) := by
  intro before
  apply catalogue_ext
  intro handle
  rw [catalogue_lookup, catalogue_lookup]
  by_cases chosen : handle = selected
  · simp only [chosen, ↓reduceIte]
    exact candidate_involutive _
  · simp only [chosen, ↓reduceIte]

theorem catalogue_prepare (selected : Handle nativeGraph)
    (before : CommitmentCandidates Player (CandidateSlot nativeGraph) (Raw simpleExpr))
    (owner : Player) (slot : CandidateSlot nativeGraph) (value : Raw simpleExpr) :
    catalogue selected (before.prepare owner slot value) =
      (catalogue selected before).prepare owner slot
        (if (owner, slot) = selected then raw value else value) := by
  apply catalogue_ext
  intro handle
  by_cases same : handle = (owner, slot)
  · subst handle
    rw [catalogue_lookup, CommitmentCandidates.lookup_prepare_self,
      CommitmentCandidates.lookup_prepare_self, catalogue_lookup]
    by_cases chosen : (owner, slot) = selected <;>
      cases before.lookup (owner, slot) <;> simp [chosen, candidate]
  · rw [CommitmentCandidates.lookup_prepare_other _ _ _ _ _ same, catalogue_lookup,
      CommitmentCandidates.lookup_prepare_other _ _ _ _ _ same, catalogue_lookup]

theorem catalogue_freeze (selected frozen : Handle nativeGraph)
    (before : CommitmentCandidates Player (CandidateSlot nativeGraph) (Raw simpleExpr)) :
    catalogue selected (before.freeze frozen) = (catalogue selected before).freeze frozen := by
  apply catalogue_ext
  intro handle
  by_cases same : handle = frozen
  · subst handle
    rw [catalogue_lookup, CommitmentCandidates.lookup_freeze_self,
      CommitmentCandidates.lookup_freeze_self, catalogue_lookup]
    by_cases chosen : frozen = selected <;>
      cases before.lookup frozen <;> simp [chosen, candidate]
  · rw [CommitmentCandidates.lookup_freeze_other _ _ _ same, catalogue_lookup,
      CommitmentCandidates.lookup_freeze_other _ _ _ same, catalogue_lookup]

theorem catalogue_verify (selected : Handle nativeGraph)
    (before : CommitmentCandidates Player (CandidateSlot nativeGraph) (Raw simpleExpr))
    (evidence : OpeningFact nativeGraph) :
    (catalogue selected before).verify (fact selected evidence).handle
        (fact selected evidence).raw = before.verify evidence.handle evidence.raw := by
  rw [fact_handle]
  by_cases same : evidence.handle = selected
  · simp only [CommitmentCandidates.verify, fact, same, ↓reduceIte]
    rw [catalogue_lookup, ite_eq_left rfl]
    cases stored : before.lookup selected <;>
      simp [candidate, raw_involutive.injective.eq_iff]
  · simp only [CommitmentCandidates.verify, fact, same, ↓reduceIte]
    congr 1
    rw [catalogue_lookup, ite_eq_right same]

def state (selected : Handle nativeGraph) (before : State nativeGraph) : State nativeGraph :=
  { before with candidates := catalogue selected before.candidates }

def result : PublicationResult Bool → PublicationResult Bool
  | .failure => .failure
  | .success bit => .success (!bit)

theorem bindingResult (selected : Handle nativeGraph) (before : State nativeGraph) :
    (state selected before).bindingResult selected .bool =
      result (before.bindingResult selected .bool) := by
  simp only [state, State.bindingResult]
  rw [catalogue_lookup, ite_eq_left rfl]
  cases before.candidates.lookup selected with
  | fresh | unopenable => rfl
  | openable value =>
      simp only [candidate, raw_as_bool]
      cases value.as? .bool <;> rfl

theorem register (selected : Handle nativeGraph) (submitted : Submission nativeGraph)
    (before : State nativeGraph) (who : Player) :
    (call selected submitted).register (state selected before) who =
      state selected (submitted.register before who) := by
  rcases submitted with ⟨packet, opening⟩
  cases packet with
  | commitment event handle =>
      rcases handle with ⟨owner, slot⟩
      cases slot with
      | initial input =>
          by_cases chosen : (owner, Slot.initial input) = selected
          · subst selected
            cases opening <;> simp [call, Submission.register]
          · cases opening <;> simp [call, chosen, Submission.register]
      | prepared serial =>
          by_cases owned : owner = who
          · subst owner
            by_cases chosen : (who, Slot.prepared serial) = selected
            · subst selected
              cases opening with
              | none => simp [call, Submission.register]
              | some value =>
                  simp only [call, ↓reduceIte, Option.map_some, Submission.register, state]
                  congr 1
                  simpa only [↓reduceIte] using
                    (catalogue_prepare (who, .prepared serial) before.candidates who
                      (.prepared serial) value).symm
            · cases opening with
              | none => simp [call, chosen, Submission.register]
              | some value =>
                  simp only [call, chosen, ↓reduceIte, Submission.register, state]
                  congr 1
                  simpa only [chosen, ↓reduceIte] using
                    (catalogue_prepare selected before.candidates who (.prepared serial) value).symm
          · by_cases chosen : (owner, Slot.prepared serial) = selected
            · subst selected
              cases opening <;> simp [call, Submission.register, owned]
            · cases opening <;> simp [call, chosen, Submission.register, owned]
  | opening | withhold | malformed => rfl

theorem call_register_other_owner (selected : Handle nativeGraph)
    (submitted : Submission nativeGraph) (before : State nativeGraph)
    (who : Player) (different : selected.1 ≠ who) :
    (call selected submitted).register before who = submitted.register before who := by
  rcases submitted with ⟨packet, opening⟩
  cases packet with
  | commitment event handle =>
      by_cases chosen : handle = selected
      · subst handle
        rcases selected with ⟨owner, slot⟩
        cases slot <;> cases opening <;> simp [call, Submission.register, different]
      · simp [call, chosen]
  | opening | withhold | malformed => rfl

/-- Other players retain their literal raw responses and private recall,
including ineffective foreign-handle material. -/
theorem register_other_owner (selected : Handle nativeGraph)
    (submitted : Submission nativeGraph) (before : State nativeGraph)
    (who : Player) (different : selected.1 ≠ who) :
    submitted.register (state selected before) who =
      state selected (submitted.register before who) := by
  rw [← call_register_other_owner selected submitted (state selected before) who different,
    register]

theorem submitStep_state (selected : Handle nativeGraph) (before : State nativeGraph)
    (who : Player) (sent : Payload nativeGraph) :
    submitStep (state selected before) who sent = state selected (submitStep before who sent) := by
  cases sent with
  | commitment event handle =>
      by_cases owned : handle.1 = who
      · simp only [submitStep, owned, ↓reduceIte, state]
        congr 1
        exact (catalogue_freeze selected handle before.candidates).symm
      · simp [submitStep, state, owned]
  | opening | withhold | malformed => rfl

theorem find_message (selected : Handle nativeGraph)
    (known : List (Message Player (WitnessedPacket nativeGraph))) (id : MessageId Player) :
    ((known.map (message selected)).find? fun sent => sent.id = id) =
      (known.find? fun sent => sent.id = id).map (message selected) := by
  induction known with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.find?_cons, message_id]
      split <;> simp_all

/-- The request and the candidate are flipped together. In particular,
unsuccessful owned requests remain unsuccessful. Forwarding transports the
certificate already attached to the known envelope. -/
theorem emit (selected : Handle nativeGraph) (submitted : WitnessedSubmission nativeGraph)
    (before : State nativeGraph) (who : Player)
    (known : List (Message Player (WitnessedPacket nativeGraph))) :
    (submission selected submitted).emit (state selected before) who
        (known.map (message selected)) =
      packet selected (submitted.emit before who known) := by
  cases submitted with
  | mk submitted evidence =>
      cases evidence with
      | none => simp [submission, request, WitnessedSubmission.emit, packet]
      | owned evidence =>
          have verified := catalogue_verify selected before.candidates evidence
          rw [fact_handle] at verified
          simp only [submission, request, WitnessedSubmission.emit, call_packet, state,
            fact_handle, verified, packet]
          split <;> rfl
      | forward id =>
          simp only [submission, request, WitnessedSubmission.emit, call_packet, find_message,
            packet]
          cases known.find? (fun sent => sent.id = id) <;> rfl

theorem emit_evidence_none_iff (selected : Handle nativeGraph)
    (submitted : WitnessedSubmission nativeGraph) (before : State nativeGraph) (who : Player)
    (known : List (Message Player (WitnessedPacket nativeGraph))) :
    ((submission selected submitted).emit (state selected before) who
      (known.map (message selected))).evidence = none ↔
        (submitted.emit before who known).evidence = none := by
  rw [emit]
  exact Option.map_eq_none_iff

theorem emit_other_owner (selected : Handle nativeGraph)
    (submitted : WitnessedSubmission nativeGraph) (before : State nativeGraph)
    (who : Player) (different : selected.1 ≠ who)
    (known : List (Message Player (WitnessedPacket nativeGraph))) :
    submitted.emit (state selected before) who known = submitted.emit before who known := by
  apply WitnessedSubmission.emit_local
  exact catalogue_lookup_other_owner selected before.candidates who different

/-- The emission equation includes the real registration-and-freezing order
used by an atomic native submission. It retains every public application call. -/
theorem registered_emit (selected : Handle nativeGraph)
    (submitted : WitnessedSubmission nativeGraph) (before : State nativeGraph) (who : Player)
    (known : List (Message Player (WitnessedPacket nativeGraph))) :
    (submission selected submitted).emit
        (submitStep ((submission selected submitted).call.register (state selected before) who)
          who (submission selected submitted).call.packet)
        who (known.map (message selected)) =
      packet selected (submitted.emit
        (submitStep (submitted.call.register before who) who submitted.call.packet) who known) := by
  change (submission selected submitted).emit
      (submitStep ((call selected submitted.call).register (state selected before) who)
        who (call selected submitted.call).packet) who (known.map (message selected)) = _
  rw [register, call_packet, submitStep_state, emit]

theorem registered_emit_other_owner (selected : Handle nativeGraph)
    (submitted : WitnessedSubmission nativeGraph) (before : State nativeGraph)
    (who : Player) (different : selected.1 ≠ who)
    (known : List (Message Player (WitnessedPacket nativeGraph))) :
    submitted.emit (submitStep (submitted.call.register (state selected before) who)
        who submitted.call.packet) who known =
      submitted.emit (submitStep (submitted.call.register before who)
        who submitted.call.packet) who known := by
  rw [register_other_owner selected submitted.call before who different, submitStep_state,
    emit_other_owner selected submitted _ who different]

theorem packet_eq_of_no_certificate (selected : Handle nativeGraph)
    (sent : WitnessedPacket nativeGraph)
    (absent : ∀ evidence, sent.evidence = some evidence → evidence.handle ≠ selected) :
    packet selected sent = sent := by
  cases sent with
  | mk call evidence =>
      cases evidence with
      | none => rfl
      | some evidence => simp [packet, fact, absent evidence rfl]

theorem messages_eq_of_no_certificate (selected : Handle nativeGraph)
    (sent : List (Message Player (WitnessedPacket nativeGraph)))
    (absent : ∀ envelope ∈ sent, ∀ evidence,
      envelope.payload.evidence = some evidence → evidence.handle ≠ selected) :
    sent.map (message selected) = sent := by
  induction sent with
  | nil => rfl
  | cons head tail ih =>
      have same := packet_eq_of_no_certificate selected head.payload
        (absent head List.mem_cons_self)
      have rest := ih fun envelope member => absent envelope (List.mem_cons_of_mem head member)
      simp only [List.map_cons, message, same, rest]

theorem call_available (selected : Handle nativeGraph) (submitted : Submission nativeGraph)
    (allowed : submitted ∈ nativeBounds.calls) : call selected submitted ∈ nativeBounds.calls := by
  rw [MessageBounds.calls_mem] at allowed ⊢
  refine ⟨by simpa only [call_packet] using allowed.1, ?_⟩
  rcases submitted with ⟨packet, opening⟩
  cases packet with
  | commitment event handle =>
      by_cases same : handle = selected
      · simp only [call, same, ↓reduceIte]
        cases opening with
        | none => trivial
        | some value => exact raw_available value allowed.2
      · simpa only [call, same, ↓reduceIte] using allowed.2
  | opening | withhold | malformed => exact allowed.2

theorem request_available (selected : Handle nativeGraph)
    (known : List (Message Player (WitnessedPacket nativeGraph)))
    (evidence : EvidenceRequest nativeGraph)
    (allowed : nativeBounds.AllowsEvidence known evidence) :
    nativeBounds.AllowsEvidence known (request selected evidence) := by
  cases evidence with
  | none | forward => exact allowed
  | owned evidence =>
      change nativeBounds.AllowsHandle (fact selected evidence).handle ∧
        (fact selected evidence).raw ∈ nativeBounds.values
      refine ⟨by simpa only [fact_handle] using allowed.1, ?_⟩
      by_cases same : evidence.handle = selected
      · simpa only [fact, same, ↓reduceIte] using raw_available evidence.raw allowed.2
      · simpa only [fact, same, ↓reduceIte] using allowed.2

theorem submission_available (selected : Handle nativeGraph)
    (known : List (Message Player (WitnessedPacket nativeGraph)))
    (submitted : WitnessedSubmission nativeGraph)
    (allowed : submitted ∈ nativeBounds.submissions known) :
    submission selected submitted ∈ nativeBounds.submissions known := by
  rw [MessageBounds.submissions_mem] at allowed ⊢
  exact ⟨(MessageBounds.calls_mem _ _).mp (call_available selected submitted.call
    ((MessageBounds.calls_mem _ _).mpr allowed.1)),
    request_available selected known submitted.evidence allowed.2⟩

theorem action_available (selected : Handle nativeGraph) (who : Player)
    (past : List app.PlayerEntry) (view : app.PlayerView) (response : app.Action)
    (allowed : response ∈ menu.actions who past view) :
    action selected response ∈ menu.actions who past view := by
  change response ∈ (nativeBounds.rawMenu nativeRuntime leaks).actions who past view at allowed
  change action selected response ∈
    (nativeBounds.rawMenu nativeRuntime leaks).actions who past view
  rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at allowed ⊢
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => trivial
  | some transmission =>
      cases transmission with
      | replay => exact allowed
      | submit submitted => exact submission_available selected _ submitted allowed

def responseEquiv (selected : Handle nativeGraph) (who : Player)
    (past : List app.PlayerEntry) (view : app.PlayerView) :
    menu.actions who past view ≃ menu.actions who past view where
  toFun response :=
    ⟨action selected response.1, action_available selected who past view _ response.2⟩
  invFun response :=
    ⟨action selected response.1, action_available selected who past view _ response.2⟩
  left_inv response := Subtype.ext (action_involutive selected response.1)
  right_inv response := Subtype.ext (action_involutive selected response.1)

/-- The permutation covers the full raw response menu, including ineffective
private material, failed certificate requests, silence, and known replays. -/
theorem uniform (selected : Handle nativeGraph) (who : Player)
    (past : List app.PlayerEntry) (view : app.PlayerView) :
    (menu.uniformResponses who past view).map (action selected) =
      menu.uniformResponses who past view := by
  classical
  let choices := menu.actions who past view
  let : Nonempty choices :=
    ⟨⟨(menu.nonempty who past view).choose, (menu.nonempty who past view).choose_spec⟩⟩
  have symmetric : (FinDist.uniformOfFintype : FinDist choices).map
      (responseEquiv selected who past view) = FinDist.uniformOfFintype := by
    apply FinDist.ext_of_prob
    intro response
    obtain ⟨before, rfl⟩ := (responseEquiv selected who past view).surjective response
    rw [FinDist.prob_map_of_injective _ (responseEquiv selected who past view).injective]
    simp only [FinDist.prob_uniformOfFintype]
  change ((FinDist.uniformOfFintype : FinDist choices).map Subtype.val).map (action selected) = _
  rw [FinDist.map_comp]
  calc
    _ = ((FinDist.uniformOfFintype : FinDist choices).map
        (responseEquiv selected who past view)).map Subtype.val := by rw [FinDist.map_comp]; rfl
    _ = _ := by rw [symmetric]; rfl

theorem uniform_prob (selected : Handle nativeGraph) (who : Player)
    (past : List app.PlayerEntry) (view : app.PlayerView) (response : app.Action) :
    (menu.uniformResponses who past view).prob (action selected response) =
      (menu.uniformResponses who past view).prob response := by
  classical
  have same := congrArg (fun law => law.prob (action selected response))
    (uniform selected who past view)
  rw [FinDist.prob_map_of_injective _ (action_involutive selected).injective] at same
  exact same.symm

theorem requests_eq_of_known_ids
    (first second : List (Message Player (WitnessedPacket nativeGraph)))
    (same : first.map Message.id = second.map Message.id) :
    nativeBounds.requests first = nativeBounds.requests second := by
  have forwarded : first.map (fun sent => EvidenceRequest.forward (graph := nativeGraph) sent.id) =
      second.map (fun sent => EvidenceRequest.forward (graph := nativeGraph) sent.id) := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map (EvidenceRequest.forward (graph := nativeGraph))) same
  simp only [MessageBounds.requests, forwarded]

/-- Private recall and certificate contents may change. The full raw menu
depends on possessed message identifiers, so those changes do not change the
available submissions, replays, or uniform response weights. -/
theorem menus_eq_of_known_ids (who : Player)
    (firstPast secondPast : List app.PlayerEntry) (firstView secondView : app.PlayerView)
    (same : (ReactiveApplication.ResponseMenu.knownPackets firstPast firstView).map Message.id =
      (ReactiveApplication.ResponseMenu.knownPackets secondPast secondView).map Message.id) :
    menu.actions who firstPast firstView = menu.actions who secondPast secondView := by
  classical
  have submissions : nativeBounds.submissions
      (ReactiveApplication.ResponseMenu.knownPackets firstPast firstView) =
      nativeBounds.submissions
        (ReactiveApplication.ResponseMenu.knownPackets secondPast secondView) := by
    simp only [MessageBounds.submissions, requests_eq_of_known_ids _ _ same]
  apply Finset.ext
  intro response
  change response ∈ (nativeBounds.rawMenu nativeRuntime leaks).actions who firstPast firstView ↔
    response ∈ (nativeBounds.rawMenu nativeRuntime leaks).actions who secondPast secondView
  simp only [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  cases response.transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit submitted => rw [submissions]
      | replay id =>
          unfold ReactiveApplication.SubmissionNormalization.ReplayKnown
          simpa only [List.mem_map] using
            Iff.of_eq (congrArg (fun ids => id ∈ ids) same)

theorem uniform_eq_of_known_ids (who : Player)
    (firstPast secondPast : List app.PlayerEntry) (firstView secondView : app.PlayerView)
    (same : (ReactiveApplication.ResponseMenu.knownPackets firstPast firstView).map Message.id =
      (ReactiveApplication.ResponseMenu.knownPackets secondPast secondView).map Message.id) :
    menu.uniformResponses who firstPast firstView =
      menu.uniformResponses who secondPast secondView := by
  classical
  have menus := menus_eq_of_known_ids who firstPast secondPast firstView secondView same
  let distribution (choices : {values : Finset app.Action // values.Nonempty}) :
      FinDist app.Action := by
    let : Nonempty choices.1 := ⟨⟨choices.2.choose, choices.2.choose_spec⟩⟩
    exact (FinDist.uniformOfFintype : FinDist choices.1).map Subtype.val
  change distribution ⟨menu.actions who firstPast firstView,
    menu.nonempty who firstPast firstView⟩ = distribution
      ⟨menu.actions who secondPast secondView, menu.nonempty who secondPast secondView⟩
  exact congrArg distribution (Subtype.ext menus)

theorem uniform_prob_of_known_ids (selected : Handle nativeGraph) (who : Player)
    (firstPast secondPast : List app.PlayerEntry) (firstView secondView : app.PlayerView)
    (same : (ReactiveApplication.ResponseMenu.knownPackets firstPast firstView).map Message.id =
      (ReactiveApplication.ResponseMenu.knownPackets secondPast secondView).map Message.id)
    (response : app.Action) :
    (menu.uniformResponses who secondPast secondView).prob (action selected response) =
      (menu.uniformResponses who firstPast firstView).prob response := by
  rw [uniform_prob, uniform_eq_of_known_ids who firstPast secondPast firstView secondView same]

end VegasTests.SelectiveAssociation.Restricted.CandidateFlip
