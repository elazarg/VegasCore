/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourcePrefix
import VegasTests.SelectiveAssociationSourceCertificateSymmetry

/-! # Guessers' observations under Alice's hidden-bit permutation

The proof projection below omits Alice's private action recall and source
state. It retains the entire message network, both guessers' complete recall,
the calendar position, and public receipts. The actual recording service still
has its full recall; its fixed calendar only consults the position and pending
messages. This is a proof device, not an alternative interaction semantics.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Vegas.SourceProgram Interaction GameTheory.Math.Probability

structure OutsideAlice (Claim : Type) where
  network : MessageNetwork Player (Packet Claim)
  receipts : List (MessageId Player × Bool)
  bobRecall : List (application Claim).PlayerEntry
  carolRecall : List (application Claim).PlayerEntry
  environmentCount : Nat

def outsideAlice {Claim : Type} (execution : (application Claim).Execution) : OutsideAlice Claim :=
  ⟨execution.network, execution.receipts, execution.recall bob, execution.recall carol,
    execution.environmentRecall.length⟩

theorem outsideAlice_effect {Claim : Type} (first second : (application Claim).Execution)
    (cmd : (application Claim).Command)
    (same : outsideAlice first = outsideAlice second) :
    outsideAlice (effect first cmd) = outsideAlice (effect second cmd) := by
  have network := congrArg OutsideAlice.network same
  have receipts := congrArg OutsideAlice.receipts same
  have bobRecall := congrArg OutsideAlice.bobRecall same
  have carolRecall := congrArg OutsideAlice.carolRecall same
  have environmentCount := congrArg OutsideAlice.environmentCount same
  change first.network = second.network at network
  change first.receipts = second.receipts at receipts
  change first.recall bob = second.recall bob at bobRecall
  change first.recall carol = second.recall carol at carolRecall
  change first.environmentRecall.length = second.environmentRecall.length at environmentCount
  cases cmd with
  | activate who =>
      simp only [outsideAlice, effect, recordEnvironment, List.length_append, List.length_singleton]
      rw [network, receipts, bobRecall, carolRecall, environmentCount]
  | application cmd =>
      simp only [outsideAlice, effect, recordEnvironment, List.length_append, List.length_singleton]
      rw [network, receipts, bobRecall, carolRecall, environmentCount]
  | wait =>
      simp only [outsideAlice, effect, recordEnvironment, List.length_append, List.length_singleton]
      rw [network, receipts, bobRecall, carolRecall, environmentCount]
  | «include» id =>
      simp only [effect, recordEnvironment, ReactiveApplication.Execution.includePending,
        MessageNetwork.includePending, application]
      rw [network]
      cases second.network.lookup id <;>
        simp only [outsideAlice, Option.isSome_some,
          List.length_append, List.length_singleton, receipts, bobRecall, carolRecall,
          environmentCount]

theorem outsideAlice_respond_submit {Claim : Type}
    (execution : (application Claim).Execution) (first second : Submission Claim)
    (packetSame : packet (submit execution.application alice first) alice
        (execution.network.known alice) first =
      packet (submit execution.application alice second) alice
        (execution.network.known alice) second) :
    outsideAlice (execution.respond (application Claim) alice ⟨some (.submit first)⟩) =
      outsideAlice (execution.respond (application Claim) alice ⟨some (.submit second)⟩) := by
  simp only [outsideAlice, ReactiveApplication.Execution.respond, application]
  change (⟨_, execution.receipts,
    if bob = alice then _ else execution.recall bob,
    if carol = alice then _ else execution.recall carol, execution.environmentRecall.length⟩ :
    OutsideAlice Claim) = _
  simp only [show bob ≠ alice by decide, show carol ≠ alice by decide, ↓reduceIte]
  rw [packetSame]

theorem outsideAlice_latest {Claim : Type} (first second : (application Claim).Execution)
    (same : outsideAlice first = outsideAlice second) (event : Event) :
    latest (first.observeEnvironment (application Claim)) event =
      latest (second.observeEnvironment (application Claim)) event := by
  have network := congrArg OutsideAlice.network same
  change first.network = second.network at network
  simp only [latest, ReactiveApplication.Execution.observeEnvironment,
    MessageNetwork.publicView]
  simp only [network]

theorem outsideAlice_remainingVisit {Claim : Type} (first second : (application Claim).Execution)
    (same : outsideAlice first = outsideAlice second) (event : Event) :
    outsideAlice (remainingVisit event first) = outsideAlice (remainingVisit event second) := by
  have ticks (count : Nat) (first second : (application Claim).Execution)
      (same : outsideAlice first = outsideAlice second) :
      outsideAlice ((List.replicate count ()).foldl
        (fun current _ => effect current (.application .tick)) first) =
      outsideAlice ((List.replicate count ()).foldl
        (fun current _ => effect current (.application .tick)) second) := by
    induction count generalizing first second with
    | zero => exact same
    | succ count ih =>
        simpa only [List.replicate_succ, List.foldl_cons] using
          ih _ _ (outsideAlice_effect first second (.application .tick) same)
  unfold remainingVisit
  apply outsideAlice_effect
  apply ticks
  rw [outsideAlice_latest first second same]
  exact outsideAlice_effect first second _ same

def bindingCertificates {Claim : Type} (first second binding : (application Claim).Action) :
    Finset NamedFact :=
  match binding.transmission with
  | some (.submit submission) =>
      certificates (submit (aliceInput first second).application alice submission)
        alice ((aliceInput first second).network.known alice) submission
  | _ => ∅

theorem outsideAlice_binding_flip {Claim : Type}
    (first second binding : (application Claim).Action)
    (uncertified : bindingCertificates first second binding = ∅) :
    outsideAlice ((aliceInput first second).respond
      (application Claim) alice (flipResponse binding)) =
      outsideAlice ((aliceInput first second).respond (application Claim) alice binding) := by
  rcases binding with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | replay => rfl
      | submit submission =>
          apply outsideAlice_respond_submit
          change certificates (submit (aliceInput first second).application alice submission)
            alice ((aliceInput first second).network.known alice) submission = ∅ at uncertified
          rw [aliceInput_application] at uncertified ⊢
          exact packet_post_flip_of_uncertified 0 _
            (aliceInput_known_empty first second alice) submission uncertified

theorem outsideAlice_carol_flip {Claim : Type}
    (first second binding : (application Claim).Action)
    (uncertified : bindingCertificates first second binding = ∅) :
    outsideAlice (carolInput first second (flipResponse binding)) =
      outsideAlice (carolInput first second binding) := by
  unfold carolInput
  apply outsideAlice_effect
  apply outsideAlice_effect
  apply outsideAlice_remainingVisit
  exact outsideAlice_binding_flip first second binding uncertified

theorem carolInput_view_flip {Claim : Type}
    (first second binding : (application Claim).Action)
    (uncertified : bindingCertificates first second binding = ∅) :
    (carolInput first second (flipResponse binding)).observe (application Claim) carol =
      (carolInput first second binding).observe (application Claim) carol := by
  have outside := outsideAlice_carol_flip first second binding uncertified
  have network := congrArg OutsideAlice.network outside
  have receipts := congrArg OutsideAlice.receipts outside
  change (⟨_, observe _ carol, _⟩ : (application Claim).PlayerView) = _
  change (carolInput first second (flipResponse binding)).network =
    (carolInput first second binding).network at network
  change (carolInput first second (flipResponse binding)).receipts =
    (carolInput first second binding).receipts at receipts
  rw [network, receipts]
  congr 1
  change observe (carolInput first second (flipResponse binding)).application carol =
    observe (carolInput first second binding).application carol
  unfold observe
  rw [carolInput_core, carolInput_core, carolInput_visit, carolInput_visit,
    carolInput_clock, carolInput_clock]
  rw [source_alice_hidden_from_carol (selectedBinding 0 (flipResponse binding))
    (selectedBinding 0 binding)]

theorem carolInput_information_flip {Claim : Type}
    (first second binding : (application Claim).Action)
    (uncertified : bindingCertificates first second binding = ∅) :
    ((carolInput first second (flipResponse binding)).recall carol,
      (carolInput first second (flipResponse binding)).observe (application Claim) carol) =
    ((carolInput first second binding).recall carol,
      (carolInput first second binding).observe (application Claim) carol) := by
  exact Prod.ext (congrArg OutsideAlice.carolRecall
    (outsideAlice_carol_flip first second binding uncertified))
    (carolInput_view_flip first second binding uncertified)

theorem selectedBinding_flip {Claim : Type} (event : Event) (action : (application Claim).Action) :
    selectedBinding event (flipResponse action) = flipBinding (selectedBinding event action) := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | replay => rfl
      | submit submission =>
          simp only [selectedBinding, flipResponse, flipSubmission]
          split <;> rfl

theorem outsideAlice_respond_carol {Claim : Type}
    (first second : (application Claim).Execution) (action : (application Claim).Action)
    (same : outsideAlice first = outsideAlice second)
    (viewed : first.observe (application Claim) carol = second.observe (application Claim) carol)
    (packets : ∀ submission, action.transmission = some (.submit submission) →
      packet (submit first.application carol submission) carol (first.network.known carol)
        submission =
      packet (submit second.application carol submission) carol (second.network.known carol)
        submission) :
    outsideAlice (first.respond (application Claim) carol action) =
      outsideAlice (second.respond (application Claim) carol action) := by
  have network := congrArg OutsideAlice.network same
  have receipts := congrArg OutsideAlice.receipts same
  have bobRecall := congrArg OutsideAlice.bobRecall same
  have carolRecall := congrArg OutsideAlice.carolRecall same
  have environmentCount := congrArg OutsideAlice.environmentCount same
  change first.network = second.network at network
  change first.receipts = second.receipts at receipts
  change first.recall bob = second.recall bob at bobRecall
  change first.recall carol = second.recall carol at carolRecall
  change first.environmentRecall.length = second.environmentRecall.length at environmentCount
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      simp only [outsideAlice, ReactiveApplication.Execution.respond,
        show bob ≠ carol by decide, ↓reduceIte]
      rw [network, receipts, bobRecall, carolRecall, viewed, environmentCount]
  | some transmission =>
      cases transmission with
      | submit submission =>
          have packetSame := packets submission rfl
          change (application Claim).packet ((application Claim).submit first.application
            carol submission) carol (first.network.known carol) submission =
              (application Claim).packet ((application Claim).submit second.application
                carol submission) carol (second.network.known carol) submission at packetSame
          simp only [outsideAlice, ReactiveApplication.Execution.respond,
            show bob ≠ carol by decide, ↓reduceIte]
          rw [packetSame, network, receipts, bobRecall, carolRecall, viewed, environmentCount]
      | replay id =>
          simp only [ReactiveApplication.Execution.respond, MessageNetwork.replay]
          rw [network]
          cases (second.network.known carol).find? (fun message => message.id = id) <;>
            simp only [outsideAlice, show bob ≠ carol by decide, ↓reduceIte,
              receipts, bobRecall, carolRecall, viewed, environmentCount]

theorem carolInput_application {Claim : Type} (first second binding : (application Claim).Action) :
    (carolInput first second binding).application =
      ⟨CorePath.alice (selectedBinding 0 binding), some 1, 1⟩ := by
  calc
    _ = (⟨(carolInput first second binding).application.core,
        (carolInput first second binding).application.visit,
        (carolInput first second binding).application.clock⟩ : State) := rfl
    _ = _ := by rw [carolInput_core, carolInput_visit, carolInput_clock]

theorem outsideAlice_bob_flip {Claim : Type}
    (first second binding guess : (application Claim).Action)
    (uncertified : bindingCertificates first second binding = ∅) :
    outsideAlice (bobInput first second (flipResponse binding) guess) =
      outsideAlice (bobInput first second binding guess) := by
  unfold bobInput
  apply outsideAlice_effect
  apply outsideAlice_effect
  apply outsideAlice_remainingVisit
  apply outsideAlice_respond_carol
  · exact outsideAlice_carol_flip first second binding uncertified
  · exact carolInput_view_flip first second binding uncertified
  · intro submission _
    have network := congrArg OutsideAlice.network
      (outsideAlice_carol_flip first second binding uncertified)
    change (carolInput first second (flipResponse binding)).network =
      (carolInput first second binding).network at network
    rw [carolInput_application, carolInput_application, network]
    exact packet_carol_independent _ _ 1 _ submission

theorem bobInput_view_flip {Claim : Type}
    (first second binding guess : (application Claim).Action)
    (uncertified : bindingCertificates first second binding = ∅) :
    (bobInput first second (flipResponse binding) guess).observe (application Claim) bob =
      (bobInput first second binding guess).observe (application Claim) bob := by
  have outside := outsideAlice_bob_flip first second binding guess uncertified
  have network := congrArg OutsideAlice.network outside
  have receipts := congrArg OutsideAlice.receipts outside
  change (⟨_, observe _ bob, _⟩ : (application Claim).PlayerView) = _
  change (bobInput first second (flipResponse binding) guess).network =
    (bobInput first second binding guess).network at network
  change (bobInput first second (flipResponse binding) guess).receipts =
    (bobInput first second binding guess).receipts at receipts
  rw [network, receipts]
  congr 1
  change observe (bobInput first second (flipResponse binding) guess).application bob =
    observe (bobInput first second binding guess).application bob
  unfold observe
  rw [bobInput_core, bobInput_core, bobInput_visit, bobInput_visit,
    bobInput_clock, bobInput_clock]
  rw [source_carol_hidden_from_bob (selectedBinding 0 (flipResponse binding))
    (selectedBinding 0 binding)]

theorem bobInput_information_flip {Claim : Type}
    (first second binding guess : (application Claim).Action)
    (uncertified : bindingCertificates first second binding = ∅) :
    ((bobInput first second (flipResponse binding) guess).recall bob,
      (bobInput first second (flipResponse binding) guess).observe (application Claim) bob) =
    ((bobInput first second binding guess).recall bob,
      (bobInput first second binding guess).observe (application Claim) bob) := by
  exact Prod.ext (congrArg OutsideAlice.bobRecall
    (outsideAlice_bob_flip first second binding guess uncertified))
    (bobInput_view_flip first second binding guess uncertified)

theorem bindingCertificates_flip_empty {Claim : Type}
    (first second binding : (application Claim).Action)
    (uncertified : bindingCertificates first second binding = ∅) :
    bindingCertificates first second (flipResponse binding) = ∅ := by
  rcases binding with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | replay => rfl
      | submit submission =>
          change certificates (submit (aliceInput first second).application alice submission)
            alice ((aliceInput first second).network.known alice) submission = ∅ at uncertified
          change certificates (submit (aliceInput first second).application alice
            (flipSubmission submission)) alice ((aliceInput first second).network.known alice)
              (flipSubmission submission) = ∅
          rw [aliceInput_application] at uncertified ⊢
          have same := packet_post_flip_of_uncertified 0 _
            (aliceInput_known_empty first second alice) submission uncertified
          exact (congrArg Packet.evidence same).trans uncertified

theorem bindingCertificates_flip_empty_iff {Claim : Type}
    (first second binding : (application Claim).Action) :
    bindingCertificates first second (flipResponse binding) = ∅ ↔
      bindingCertificates first second binding = ∅ := by
  constructor
  · intro empty
    have empty := bindingCertificates_flip_empty first second (flipResponse binding) empty
    rw [flipResponse_involutive binding] at empty
    exact empty
  · exact bindingCertificates_flip_empty first second binding

end VegasTests.SelectiveAssociation.NamedSource
