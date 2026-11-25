module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensClientInput

@[expose] public section

/-! # Executable opening encoding for Odds–Evens -/

namespace Vegas.Examples.OddsEvensExecutableClient

open OddsEvens OddsEvensLedgerClient EventGraphRuntime Interaction

/-- The messages that can supply an opening certificate at this callback. -/
def openingKnownPackets (past : List app.PlayerEntry) (view : app.PlayerView) :
    List (Message Player (WitnessedPacket compiled)) :=
  past.filterMap ReactiveApplication.PlayerEntry.emitted ++
    view.messages.leaked ++ view.messages.ledger

/-- Compare the certificate resolved by an identifier with a Boolean opening. -/
def openingForwardMatches (known : List (Message Player (WitnessedPacket compiled)))
    (handle : Bool × Slot 0) (bit : Bool) (id : Bool × Nat) : Bool :=
  let evidence := (known.find? fun packet => (packet.id : Bool × Nat) == id).bind
    (·.payload.evidence)
  evidence.any fun fact => decide ((fact.handle : Bool × Slot 0) = handle ∧
    booleanValue fact.raw = some bit)

def matchesCandidate (candidate : CommitmentCandidate (Raw simpleExpr)) (bit : Bool) :
    Bool :=
  match candidate with
  | .openable raw => booleanValue raw == some bit
  | .fresh | .unopenable => false

/-- Use the first known reference to the owned certificate, when it exists.
An identifier resolves through the first packet bearing it. -/
def openingEvidence (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (handle : Bool × Slot 0) (bit : Bool) : EvidenceRequest compiled :=
  let candidate : CommitmentCandidate (Raw simpleExpr) := view.application.candidates handle.2
  if handle.1 = who ∧ matchesCandidate candidate bit = true then
    let known := openingKnownPackets past view
    match known.find? (fun message => openingForwardMatches known handle bit message.id) with
    | none => .owned ⟨handle, ⟨.bool, bit⟩⟩
    | some message => .forward message.id
  else .none

/-- Encode a Boolean reveal from the matching accepted handle and visible
successful binding. Selection of the proper opening event is done by the caller. -/
def writeOpeningPacket (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (event : Fin 4) (stored : Option (PublicationResult Bool))
    (accepted : Option (Handle compiled)) : app.Action :=
  if who ∈ (view.application.publicView.observation.defaults.defaulted : Finset Bool) then ⟨none⟩
  else ⟨do
    let .success bit ← stored | none
    let handle ← accepted
    if handle.1 = who then
      let raw : Raw simpleExpr := ⟨.bool, bit⟩
      some ⟨⟨.opening event handle raw, none⟩, openingEvidence who past view handle bit⟩
    else none⟩

/-- Encode the successful opening request for Even or Odd from the raw callback. -/
def writeOpening (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (second : Bool) : app.Action :=
  if second then
    writeOpeningPacket who past view 3
      (show Option (PublicationResult Bool) from
        view.application.observation.store (.inr (1 : Fin 4)))
      (view.application.publicView.accepted (.inr (1 : Fin 4)))
  else
    writeOpeningPacket who past view 2
      (show Option (PublicationResult Bool) from
        view.application.observation.store (.inr (0 : Fin 4)))
      (view.application.publicView.accepted (.inr (0 : Fin 4)))

private theorem booleanValue_eq_some (raw : Raw simpleExpr) (bit : Bool) :
    booleanValue raw = some bit ↔ raw = ⟨.bool, bit⟩ := by
  rcases raw with ⟨type, value⟩
  cases type <;> simp [booleanValue]

private theorem openingEvidence_eq (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) (handle : Bool × Slot 0) (bit : Bool) :
    openingEvidence who past view handle bit =
      (EvidenceRequest.owned (⟨handle, ⟨.bool, bit⟩⟩ : OpeningFact compiled)).normalize
        who view.application.candidates (ReactiveApplication.ResponseMenu.knownPackets past view) :=
  by
    classical
    have catalogue :
        matchesCandidate (view.application.candidates handle.2) bit = true ↔
          view.application.candidates handle.2 = .openable ⟨.bool, bit⟩ := by
      cases candidate : view.application.candidates handle.2 <;>
        simp [matchesCandidate, booleanValue_eq_some]
    have search :
        (openingKnownPackets past view).find? (fun message =>
          openingForwardMatches (openingKnownPackets past view) handle bit message.id) =
        EvidenceRequest.forwardingPacket (ReactiveApplication.ResponseMenu.knownPackets past view)
          (⟨handle, ⟨.bool, bit⟩⟩ : OpeningFact compiled) := by
      unfold EvidenceRequest.forwardingPacket openingKnownPackets
        ReactiveApplication.ResponseMenu.knownPackets ReactiveApplication.outputs
      congr 1
      funext message
      unfold openingForwardMatches EvidenceRequest.forwardedEvidence
      have ids (packet : Message Player (WitnessedPacket compiled)) :
          ((packet.id : Bool × Nat) == message.id) = decide (packet.id = message.id) :=
        Bool.eq_iff_iff.mpr (by simp)
      simp only [ids]
      generalize ((List.find? (fun packet : Message Player (WitnessedPacket compiled) =>
        decide (packet.id = message.id))
        (past.filterMap ReactiveApplication.PlayerEntry.emitted ++
          view.messages.leaked ++ view.messages.ledger)).bind
            (·.payload.evidence)) = evidence
      cases evidence with
      | none => rfl
      | some fact =>
          change decide ((fact.handle : Bool × Slot 0) = handle ∧
            booleanValue fact.raw = some bit) = decide (some fact = _)
          apply decide_eq_decide.mpr
          rcases fact with ⟨recorded, raw⟩
          simp [booleanValue_eq_some]
    simp only [openingEvidence, EvidenceRequest.normalize, EvidenceRequest.resolve]
    by_cases verified : handle.1 = who ∧
        view.application.candidates handle.2 = .openable ⟨.bool, bit⟩
    · have checked := (and_congr_right fun _ => catalogue).mpr verified
      simp only [ite_eq_left checked, ite_eq_left verified, EvidenceRequest.canonical, search]
      cases EvidenceRequest.forwardingPacket
        (ReactiveApplication.ResponseMenu.knownPackets past view)
        (⟨handle, ⟨.bool, bit⟩⟩ : OpeningFact compiled) <;> rfl
    · have rejected := fun checked => verified ((and_congr_right fun _ => catalogue).mp checked)
      simp only [ite_eq_right rejected, ite_eq_right verified, EvidenceRequest.canonical]

private theorem openPacket_eq (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) (event : compiled.EventId) (owner : Player)
    (binding : EventGraph.FieldRef compiled.layout (.binding owner .bool))
    (checks : List (EventGraph.GuardCheck compiled.layout BaseTy.bool))
    (outputEq : compiled.outputLayout event = .publication .bool)
    (codeEq : cast (congrArg (EventGraph.EventCode compiled.layout) outputEq)
      (compiled.nodes event) =
        EventGraph.EventCode.resolve (L := simpleExpr) (layout := compiled.layout)
          owner BaseTy.bool binding checks) :
    writeOpeningPacket who past view event (binding.get? view.application.observation.store)
      (view.application.publicView.accepted binding.field) =
      ordinaryResponse who past view event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) := by
  classical
  rw [ordinaryResponse]
  unfold canonicalServiceDecision canonicalReactiveDecision
  rw [nodeView_eq_resolve outputEq codeEq]
  by_cases inactive : who ∈
      (view.application.publicView.observation.defaults.defaulted : Finset Bool)
  · simp only [writeOpeningPacket, EventPublicObservation.defaulted, inactive,
      ↓reduceIte, ReactiveApplication.SubmissionNormalization.action]
  · simp only [writeOpeningPacket, EventPublicObservation.defaulted, inactive,
      ↓reduceIte, reactiveResolutionPacket, cast_cast, cast_eq]
    cases stored : binding.get? view.application.observation.store with
    | none => rfl
    | some result =>
        cases result with
        | failure => rfl
        | success bit =>
            cases accepted : view.application.publicView.accepted binding.field with
            | none => rfl
            | some handle =>
                by_cases owned : handle.1 = who
                · simp only [owned, ↓reduceIte, Option.map_some,
                    ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
                    WitnessedSubmission.normalizeReactive, disclosureSubmission,
                    Submission.normalizeReactive_none, Submission.candidateAfter_opening,
                    EvidenceRequest.normalize_owned_nil, true_and, openingEvidence_eq]
                  by_cases verified : view.application.candidates handle.2 = .openable ⟨.bool, bit⟩
                  · simp [owned, verified]
                  · simp [verified, owned, EvidenceRequest.normalize, EvidenceRequest.resolve,
                        EvidenceRequest.canonical]
                · simp [owned, ReactiveApplication.SubmissionNormalization.action]

/-- The executable Even opening agrees with the prescribed canonical action. -/
theorem writeOpening_first_eq (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) :
    writeOpening who past view false = ordinaryResponse who past view (eventId 2) true := by
  let binding : EventGraph.FieldRef compiled.layout (.binding even .bool) :=
    ⟨.inr (0 : Fin 4), rfl⟩
  exact openPacket_eq who past view (eventId 2) even binding _ rfl rfl

/-- The executable Odd opening agrees with the prescribed canonical action. -/
theorem writeOpening_second_eq (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) :
    writeOpening who past view true = ordinaryResponse who past view (eventId 3) true := by
  let binding : EventGraph.FieldRef compiled.layout (.binding odd .bool) :=
    ⟨.inr (1 : Fin 4), rfl⟩
  exact openPacket_eq who past view (eventId 3) odd binding _ rfl rfl

end Vegas.Examples.OddsEvensExecutableClient
