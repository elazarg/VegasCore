/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveNormalization

/-! # Prescribed graph decisions in one activation

A binding omission transmits nothing; an admitted binding transmits an opaque
handle, including when its private meaning is unusable. A requested authentic
opening is transmitted without predicting whether its public guards succeed.
The handler evaluates those guards. Defaulted owners transmit nothing.
The turn-counted client determines when a source choice is sampled, including
the persistent choice of omission; these translators do not sample it again.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

open Classical in
def reactiveFreshSlot (view : PlayerView graph) : Option Nat :=
  if fresh : ∃ serial, view.candidates (.prepared serial) = .fresh then
    some (Nat.find fresh) else none

omit [DecidableEq Player] in
theorem reactiveFreshSlot_spec (view : PlayerView graph) (serial : Nat)
    (selected : reactiveFreshSlot view = some serial) :
    view.candidates (.prepared serial) = .fresh := by
  classical
  unfold reactiveFreshSlot at selected
  split at selected
  · rename_i fresh
    cases Option.some.inj selected
    exact Nat.find_spec fresh
  · contradiction

def reactiveResolutionPacket {owner : Player} (who : Player) (event : graph.EventId)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (_checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : PlayerView graph) : Option (Payload graph) :=
  let disclose : Bool := cast (congrArg EventField.Action outputEq) action
  if who ∈ view.publicView.observation.defaulted then none else if disclose then
    match binding.get? view.observation.store with
    | some (.success value) => match view.publicView.accepted binding.field with
      | some handle => if handle.1 = who then some (.opening event handle ⟨payload, value⟩)
          else none
      | none => none
    | some .failure | none => none
  else none

/-- Request the owned opening witness carried by a disclosure. Other packets
supply no evidence; a false opening claim still fails certificate issuance. -/
def disclosureSubmission (packet : Payload graph) : WitnessedSubmission graph :=
  ⟨⟨packet, none⟩, match packet with
    | .opening _ candidate raw => .owned ⟨candidate, raw⟩
    | .commitment .. | .malformed .. => .none⟩

/-- Normalization retains the authentic certificate of an owned opening. -/
theorem disclosureSubmission_normalize_opening (who : Player) (view : PlayerView graph)
    (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L) (owned : candidate.1 = who)
    (verified : view.candidates candidate.2 = .openable raw) :
    (disclosureSubmission (.opening event candidate raw)).normalizeReactive who view [] =
      disclosureSubmission (.opening event candidate raw) := by
  simp only [disclosureSubmission, WitnessedSubmission.normalizeReactive,
    Submission.normalizeReactive_none, Submission.candidateAfter,
    EvidenceRequest.normalize_owned_nil,
    owned, verified, and_self, ↓reduceIte]

def reactiveDecision (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId)
    (action : graph.Action event) (view : PlayerView graph) :
    (runtime.reactiveApplication leaks).Action where
  transmission := if who ∈ view.publicView.observation.defaulted then none else
    match nodeView graph event with
    | .sample .. => none
    | .bind _owner payload outputEq _codeEq =>
        (cast (congrArg EventField.Action outputEq) action :
          Option (PublicationResult (L.Val payload))).bind fun result =>
          (reactiveFreshSlot view).map fun serial =>
            ⟨⟨.commitment event (who, .prepared serial),
              match result with
              | .failure => none
              | .success value => some ⟨payload, value⟩⟩, .none⟩
    | .resolve _owner payload binding checks outputEq _codeEq =>
        (reactiveResolutionPacket who event payload binding checks outputEq action view).map
          fun packet => (disclosureSubmission packet).normalizeReactive who view []

/-- The prescribed native decision with private response aliases normalized.
An omitted binding or withheld publication sends nothing and is settled by expiry. -/
def serviceDecision (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event) :
    (runtime.reactiveApplication leaks).Action :=
  (runtime.reactiveNormalization leaks).action who past view
    (runtime.reactiveDecision leaks who event choice view.application)

end Vegas.EventGraphRuntime
