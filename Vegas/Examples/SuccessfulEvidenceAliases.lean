/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeResponses
import Interaction.ReactiveNormalRecall

/-! # Successful certificate requests can have private aliases

An owner who already emitted an opening certificate can request the same
certificate by ownership or by forwarding its earlier packet. Both requests
produce identical application and network effects, while their private action
records differ. Certificate normalization identifies these successful requests.

This is an operational coverage regression, not an equilibrium counterexample.
The resulting common representative satisfies the existing submission
normalization interface and its sequential-equilibrium alias theorem.
-/

noncomputable section

namespace Vegas.Examples.SuccessfulEvidenceAliases

open Vegas Vegas.EventGraphRuntime Interaction
open MonitoredGuessing

def certificate : OpeningFact nativeGraph := ⟨aliceHandle, ⟨.bool, true⟩⟩

def call : Submission nativeGraph :=
  ⟨.opening alicePublication aliceHandle ⟨.bool, true⟩, none⟩

def owned : WitnessedSubmission nativeGraph := ⟨call, .owned certificate⟩

def forwarded : WitnessedSubmission nativeGraph := ⟨call, .forward (alice, 0)⟩

def ownedAction : nativeApp.Action := ⟨some (.submit owned)⟩

def forwardedAction : nativeApp.Action := ⟨some (.submit forwarded)⟩

/-- Possession comes from an actual earlier output by this same owner. -/
def afterFirst : nativeApp.Execution :=
  (ReactiveApplication.Execution.initial nativeApp (nativeInitial true)).respond
    nativeApp alice ownedAction

theorem known_certificate :
    (afterFirst.network.known alice).find? (fun message => message.id = (alice, 0)) =
      some ⟨(alice, 0), ⟨call.packet, some certificate, none⟩⟩ := by
  rfl

theorem same_submission_effect :
    nativeApp.submit afterFirst.application alice owned =
      nativeApp.submit afterFirst.application alice forwarded := rfl

theorem same_packet :
    nativeApp.packet (nativeApp.submit afterFirst.application alice owned) alice
        (afterFirst.network.known alice) owned =
      nativeApp.packet (nativeApp.submit afterFirst.application alice forwarded) alice
        (afterFirst.network.known alice) forwarded := by
  rfl

theorem requests_distinct : owned ≠ forwarded := by
  intro same
  have impossible := congrArg WitnessedSubmission.evidence same
  cases impossible

theorem actions_distinct : ownedAction ≠ forwardedAction := by
  intro same
  have impossible := congrArg ReactiveApplication.Action.transmission same
  exact requests_distinct (ReactiveApplication.Transmission.submit.inj (Option.some.inj impossible))

theorem known_packets : ReactiveApplication.ResponseMenu.knownPackets
    (afterFirst.recall alice) (afterFirst.observe nativeApp alice) =
      [⟨(alice, 0), ⟨call.packet, some certificate, none⟩⟩] := rfl

theorem canonical_packet : EvidenceRequest.forwardingPacket
    (ReactiveApplication.ResponseMenu.knownPackets (afterFirst.recall alice)
      (afterFirst.observe nativeApp alice)) certificate =
        some ⟨(alice, 0), ⟨call.packet, some certificate, none⟩⟩ := by
  rw [known_packets]
  simp [EvidenceRequest.forwardingPacket, EvidenceRequest.forwardedEvidence]

theorem owned_normalizes_to_forwarded :
    (nativeRuntime.reactiveNormalization nativeLeaks).action alice
        (afterFirst.recall alice) (afterFirst.observe nativeApp alice) ownedAction =
      forwardedAction := by
  have available : certificate.handle.1 = alice ∧
      (afterFirst.observe nativeApp alice).application.candidates certificate.handle.2 =
        .openable certificate.raw := ⟨rfl, rfl⟩
  have normal : (EvidenceRequest.owned certificate).normalize alice
      (afterFirst.observe nativeApp alice).application.candidates
      (ReactiveApplication.ResponseMenu.knownPackets (afterFirst.recall alice)
        (afterFirst.observe nativeApp alice)) = .forward (alice, 0) := by
    rw [EvidenceRequest.normalize, EvidenceRequest.resolve, ite_eq_left available,
      EvidenceRequest.canonical, canonical_packet]
  simpa only [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
    WitnessedSubmission.normalizeReactive, ownedAction, forwardedAction, owned, forwarded,
    call, Submission.normalizeReactive_none, Submission.candidateAfter_opening] using
      congrArg (fun request : EvidenceRequest nativeGraph =>
        (⟨some (.submit ⟨call, request⟩)⟩ : nativeApp.Action)) normal

theorem forwarded_is_normal :
    (nativeRuntime.reactiveNormalization nativeLeaks).action alice
        (afterFirst.recall alice) (afterFirst.observe nativeApp alice) forwardedAction =
      forwardedAction := by
  have resolved : EvidenceRequest.forwardedEvidence
      (ReactiveApplication.ResponseMenu.knownPackets (afterFirst.recall alice)
        (afterFirst.observe nativeApp alice)) (alice, 0) = some certificate := rfl
  have normal : (EvidenceRequest.forward (graph := nativeGraph) (alice, 0)).normalize alice
      (afterFirst.observe nativeApp alice).application.candidates
      (ReactiveApplication.ResponseMenu.knownPackets (afterFirst.recall alice)
        (afterFirst.observe nativeApp alice)) = .forward (alice, 0) := by
    rw [EvidenceRequest.normalize, EvidenceRequest.resolve, resolved,
      EvidenceRequest.canonical, canonical_packet]
  simpa only [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
    WitnessedSubmission.normalizeReactive, forwardedAction, forwarded,
    call, Submission.normalizeReactive_none, Submission.candidateAfter_opening] using
      congrArg (fun request : EvidenceRequest nativeGraph =>
        (⟨some (.submit ⟨call, request⟩)⟩ : nativeApp.Action)) normal

theorem same_normal_form :
    (nativeRuntime.reactiveNormalization nativeLeaks).action alice
        (afterFirst.recall alice) (afterFirst.observe nativeApp alice) ownedAction =
      (nativeRuntime.reactiveNormalization nativeLeaks).action alice
        (afterFirst.recall alice) (afterFirst.observe nativeApp alice) forwardedAction := by
  rw [owned_normalizes_to_forwarded, forwarded_is_normal]

theorem both_available :
    ownedAction ∈ nativeMenu.actions alice (afterFirst.recall alice)
        (afterFirst.observe nativeApp alice) ∧
      forwardedAction ∈ nativeMenu.actions alice (afterFirst.recall alice)
        (afterFirst.observe nativeApp alice) := by
  constructor
  · exact native_opening_available alice _ _ alicePublication aliceHandle trivial true
  · change forwardedAction ∈ (nativeBounds.rawMenu nativeRuntime nativeLeaks).actions alice _ _
    rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
    change forwarded ∈ _
    rw [MessageBounds.submissions_mem]
    refine ⟨⟨⟨trivial, ?_⟩, trivial⟩, ?_⟩
    · decide
    · have localFound : (ReactiveApplication.ResponseMenu.knownPackets
          (afterFirst.recall alice) (afterFirst.observe nativeApp alice)).find?
            (fun message => message.id = (alice, 0)) =
              some ⟨(alice, 0), ⟨call.packet, some certificate, none⟩⟩ := rfl
      exact ⟨_, List.mem_of_find?_eq_some localFound, rfl⟩

/-- Every effect other than the responding owner's recorded syntax agrees. -/
theorem same_effects :
    let first := afterFirst.respond nativeApp alice ownedAction
    let second := afterFirst.respond nativeApp alice forwardedAction
    first.application = second.application ∧ first.network = second.network ∧
      first.receipts = second.receipts ∧ first.environmentRecall = second.environmentRecall ∧
      ∀ observer, observer ≠ alice → first.recall observer = second.recall observer := by
  refine ⟨rfl, ?_, rfl, rfl, ?_⟩
  · change (afterFirst.network.submit alice
      (nativeApp.packet (nativeApp.submit afterFirst.application alice owned) alice
        (afterFirst.network.known alice) owned)).2 = _
    rw [same_packet]
    rfl
  · intro observer different
    rw [nativeApp.respond_recall_other _ _ _ different,
      nativeApp.respond_recall_other _ _ _ different]

theorem different_private_recall :
    (afterFirst.respond nativeApp alice ownedAction).recall alice ≠
      (afterFirst.respond nativeApp alice forwardedAction).recall alice := by
  intro same
  have actions := congrArg (List.map ReactiveApplication.PlayerEntry.action) same
  simp only [ReactiveApplication.Execution.respond, ownedAction, forwardedAction, ↓reduceIte,
    List.map_append, List.map_cons, List.map_nil, List.append_cancel_left_eq,
    List.cons.injEq, and_true] at actions
  exact actions_distinct actions

end Vegas.Examples.SuccessfulEvidenceAliases
