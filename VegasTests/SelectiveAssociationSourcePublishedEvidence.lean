/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourcePrefixSymmetry
import Interaction.ReactiveAllocation

/-! # A source binding certificate is public before either guess

No certificate exists during the ambient prelude. A certificate issued at
Alice's binding response therefore describes the newly accepted source name.
Its addressed fresh envelope is recorded before either guess, and remains on
the ledger. Arbitrary earlier responses and replay traffic are retained.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Vegas.SourceProgram Interaction GameTheory.Math.Probability

theorem effect_serials {Claim : Type} (execution : (application Claim).Execution)
    (cmd : (application Claim).Command) (serials : execution.network.SerialsBeforeNext) :
    (effect execution cmd).network.SerialsBeforeNext :=
  ((application Claim).serialsBeforeNextInvariant (fun _ _ => FinDist.pure cmd)).environment
    execution (effect execution cmd) cmd serials (FinDist.mem_support_pure.mpr rfl)
      (by rw [effect_law]; exact FinDist.mem_support_pure.mpr rfl)

theorem aliceInput_serials {Claim : Type} (first second : (application Claim).Action) :
    (aliceInput first second).network.SerialsBeforeNext := by
  apply effect_serials
  apply effect_serials
  apply ((application Claim).serialsBeforeNextInvariant (scheduler Claim)).respond
  apply effect_serials
  apply ((application Claim).serialsBeforeNextInvariant (scheduler Claim)).respond
  apply effect_serials
  exact MessageNetwork.SerialsBeforeNext.empty

theorem respond_ledger {Claim : Type} (execution : (application Claim).Execution)
    (who : Player) (action : (application Claim).Action) :
    (execution.respond (application Claim) who action).network.ledger =
      execution.network.ledger := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit => rfl
      | replay id =>
          cases found : (execution.network.known who).find? (fun message => message.id = id) <;>
            simp only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found]

theorem aliceInput_ledger {Claim : Type} (first second : (application Claim).Action) :
    (aliceInput first second).network.ledger = [] := by
  change (prelude first second).network.ledger = []
  rw [prelude, respond_ledger]
  change (firstResponse first).network.ledger = []
  rw [firstResponse, respond_ledger]
  rfl

theorem effect_ledger_mono {Claim : Type} (execution : (application Claim).Execution)
    (cmd : (application Claim).Command) :
    execution.network.ledger ⊆ (effect execution cmd).network.ledger := by
  cases cmd with
  | activate | application | wait => exact List.Subset.refl _
  | «include» id =>
      simp only [effect, recordEnvironment, ReactiveApplication.Execution.includePending,
        MessageNetwork.includePending, application]
      cases execution.network.lookup id
      · exact List.Subset.refl _
      · exact List.subset_append_left _ _

theorem remainingVisit_recorded_ledger {Claim : Type} (execution : (application Claim).Execution)
    (event : Event) :
    (effect execution
      (latest (execution.observeEnvironment (application Claim)) event)).network.ledger ⊆
        (remainingVisit event execution).network.ledger := by
  have ticks (count : Nat) (execution : (application Claim).Execution) :
      execution.network.ledger ⊆
        ((List.replicate count ()).foldl
          (fun current _ => effect current (.application .tick)) execution).network.ledger := by
    induction count generalizing execution with
    | zero => exact List.Subset.refl _
    | succ count ih =>
        rw [List.replicate_succ, List.foldl_cons]
        intro message member
        exact ih _ (effect_ledger_mono execution (.application .tick) member)
  intro message member
  exact effect_ledger_mono _ (.application (.settle event)) (ticks _ _ member)

theorem remainingVisit_ledger_mono {Claim : Type} (execution : (application Claim).Execution)
    (event : Event) :
    execution.network.ledger ⊆ (remainingVisit event execution).network.ledger := by
  intro message member
  exact remainingVisit_recorded_ledger execution event (effect_ledger_mono execution _ member)

theorem latest_alice_submission {Claim : Type} (execution : (application Claim).Execution)
    (submission : Submission Claim) (address : submission.address = some 0)
    (empty : execution.network.ledger = []) :
    latest (ReactiveApplication.Execution.observeEnvironment (application Claim)
        (execution.respond (application Claim) alice ⟨some (.submit submission)⟩)) 0 =
      .include (alice, execution.network.nextSerial alice) := by
  simp [latest, ReactiveApplication.Execution.respond,
    ReactiveApplication.Execution.observeEnvironment, application, MessageNetwork.submit,
    MessageNetwork.publicView, List.reverse_append, packet, Message.sender,
    address, empty, eventOwner, bindingOwner]

theorem binding_certificate_spec {Claim : Type} (first second : (application Claim).Action)
    (submission : Submission Claim) (fact : NamedFact)
    (certified : fact ∈ bindingCertificates first second ⟨some (.submit submission)⟩) :
    submission.address = some 0 ∧ submission.kind = .bind ∧ fact.1 = 0 ∧
      submission.binding = .success fact.2 := by
  change fact ∈ certificates (submit (aliceInput first second).application alice submission)
    alice ((aliceInput first second).network.known alice) submission at certified
  rw [aliceInput_application, submit_alice_shape] at certified
  by_cases accepted : submission.address = some 0 ∧ submission.kind = .bind
  · rw [ite_eq_left accepted] at certified
    have empty := aliceInput_known_empty first second alice
    simp only [certificates, accepted.2, reduceCtorEq, ↓reduceIte, Finset.union_empty,
      Finset.mem_filter] at certified
    have owned := (mayForward_of_no_certificates _ alice _ empty fact).mp certified.2
    exact ⟨accepted.1, accepted.2, (owns_alice _ _ _ _ _).mp owned |>.2⟩
  · rw [ite_eq_right accepted,
      certificates_of_initialCore _ rfl alice _ (aliceInput_known_empty first second alice)]
      at certified
    exact False.elim (Finset.notMem_empty fact certified)

def bindingEnvelope {Claim : Type} (execution : (application Claim).Execution)
    (submission : Submission Claim) : Message Player (Packet Claim) :=
  ⟨(alice, execution.network.nextSerial alice),
    packet (submit execution.application alice submission) alice
      (execution.network.known alice) submission⟩

theorem record_alice_submission {Claim : Type} (execution : (application Claim).Execution)
    (submission : Submission Claim) (address : submission.address = some 0)
    (empty : execution.network.ledger = []) (serials : execution.network.SerialsBeforeNext) :
    let sent := execution.respond (application Claim) alice ⟨some (.submit submission)⟩
    bindingEnvelope execution submission ∈
      (effect sent (latest (sent.observeEnvironment (application Claim)) 0)).network.ledger := by
  dsimp only
  rw [latest_alice_submission execution submission address empty]
  have found : (execution.respond (application Claim) alice
      ⟨some (.submit submission)⟩).network.lookup
      (alice, execution.network.nextSerial alice) =
        some (bindingEnvelope execution submission) :=
    serials.lookup_submit alice _
  simp only [effect, recordEnvironment, ReactiveApplication.Execution.includePending,
    MessageNetwork.includePending]
  rw [found]
  exact List.mem_append.mpr (Or.inr (List.mem_singleton_self _))

theorem carol_ledger_binding_certificate {Claim : Type}
    (first second binding : (application Claim).Action) (fact : NamedFact)
    (certified : fact ∈ bindingCertificates first second binding) :
    ∃ message ∈ (carolInput first second binding).network.ledger,
      fact ∈ message.payload.evidence ∧ fact.1 = 0 := by
  rcases binding with ⟨transmission⟩
  cases transmission with
  | none => exact False.elim (Finset.notMem_empty fact certified)
  | some transmission =>
      cases transmission with
      | replay => exact False.elim (Finset.notMem_empty fact certified)
      | submit submission =>
          have specification := binding_certificate_spec first second submission fact certified
          refine ⟨bindingEnvelope (aliceInput first second) submission, ?_, certified,
            specification.2.2.1⟩
          have recorded := record_alice_submission (aliceInput first second) submission
            specification.1 (aliceInput_ledger first second) (aliceInput_serials first second)
          have settled := remainingVisit_recorded_ledger _ 0 recorded
          exact effect_ledger_mono _ (.activate carol)
            (effect_ledger_mono _ (.application (.grant 1)) settled)

theorem bob_ledger_contains_carol {Claim : Type}
    (first second binding guess : (application Claim).Action) :
    (carolInput first second binding).network.ledger ⊆
      (bobInput first second binding guess).network.ledger := by
  intro message member
  have responded : message ∈
      ((carolInput first second binding).respond
        (application Claim) carol guess).network.ledger := by
    rwa [respond_ledger]
  exact effect_ledger_mono _ (.activate bob)
    (effect_ledger_mono _ (.application (.grant 2)) (remainingVisit_ledger_mono _ 1 responded))

theorem bob_ledger_binding_certificate {Claim : Type}
    (first second binding guess : (application Claim).Action) (fact : NamedFact)
    (certified : fact ∈ bindingCertificates first second binding) :
    ∃ message ∈ (bobInput first second binding guess).network.ledger,
      fact ∈ message.payload.evidence ∧ fact.1 = 0 := by
  obtain ⟨message, recorded, certified, named⟩ :=
    carol_ledger_binding_certificate first second binding fact certified
  exact ⟨message, bob_ledger_contains_carol first second binding guess recorded, certified, named⟩

def NoPublicAlice {Claim : Type} (view : (application Claim).PlayerView) : Prop :=
  ∀ message ∈ view.messages.ledger, ∀ fact ∈ message.payload.evidence, fact.1 ≠ 0

theorem carol_no_public_uncertified {Claim : Type}
    (first second binding : (application Claim).Action)
    (hidden : NoPublicAlice ((carolInput first second binding).observe (application Claim) carol)) :
    bindingCertificates first second binding = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro fact certified
  obtain ⟨message, recorded, carried, named⟩ :=
    carol_ledger_binding_certificate first second binding fact certified
  exact hidden message recorded fact carried named

theorem bob_no_public_uncertified {Claim : Type}
    (first second binding guess : (application Claim).Action)
    (hidden : NoPublicAlice
      ((bobInput first second binding guess).observe (application Claim) bob)) :
    bindingCertificates first second binding = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro fact certified
  obtain ⟨message, recorded, carried, named⟩ :=
    bob_ledger_binding_certificate first second binding guess fact certified
  exact hidden message recorded fact carried named

end VegasTests.SelectiveAssociation.NamedSource
