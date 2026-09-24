/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceGuessPayoffs
import VegasTests.SelectiveAssociationSourcePublishedEvidence

/-! # The prescribed guess does not change between the two binding visits

The ordinary guessing response carries no certificate. Recording its fresh
envelope therefore leaves the ledger's evidence list unchanged, including
when arbitrary earlier traffic remains pending.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory.Math.Probability

theorem ticks_network {Claim : Type} (execution : (application Claim).Execution) (count : Nat) :
    ((List.replicate count ()).foldl
      (fun current _ => effect current (.application .tick)) execution).network =
        execution.network := by
  induction count generalizing execution with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.foldl_cons, ih]
      rfl

theorem remainingVisit_network {Claim : Type} (event : Event)
    (execution : (application Claim).Execution) :
    (remainingVisit event execution).network =
      (effect execution
        (latest (execution.observeEnvironment (application Claim)) event)).network :=
  ticks_network _ _

theorem latest_submission {Claim : Type} (event : Event)
    (execution : (application Claim).Execution) (submission : Submission Claim)
    (address : submission.address = some event)
    (serials : execution.network.SerialsBeforeNext) :
    latest (ReactiveApplication.Execution.observeEnvironment (application Claim)
        (execution.respond (application Claim) (eventOwner event)
          ⟨some (.submit submission)⟩)) event =
      .include (eventOwner event, execution.network.nextSerial (eventOwner event)) := by
  have unpublished : ∀ message ∈ execution.network.ledger,
      message.id ≠ (eventOwner event, execution.network.nextSerial (eventOwner event)) := by
    intro message member same
    exact serials.next_unpublished (eventOwner event) (List.mem_map.mpr ⟨message, member, same⟩)
  simp only [application, latest, Message.sender, ReactiveApplication.Execution.observeEnvironment,
    MessageNetwork.publicView, ReactiveApplication.Execution.respond, MessageNetwork.submit, packet,
    address, List.any_eq_true, decide_eq_true_eq, not_exists, not_and, Bool.decide_and,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.find?_cons, decide_true, Bool.true_and]
  have fresh : decide (∀ message ∈ execution.network.ledger,
      ¬message.id = (eventOwner event, execution.network.nextSerial (eventOwner event))) = true :=
    decide_eq_true unpublished
  erw [fresh]

theorem remainingVisit_submission_ledger {Claim : Type} (event : Event)
    (execution : (application Claim).Execution) (submission : Submission Claim)
    (address : submission.address = some event)
    (serials : execution.network.SerialsBeforeNext) :
    (remainingVisit event (execution.respond (application Claim) (eventOwner event)
      ⟨some (.submit submission)⟩)).network.ledger = execution.network.ledger ++
        [⟨(eventOwner event, execution.network.nextSerial (eventOwner event)),
          packet (submit execution.application (eventOwner event) submission) (eventOwner event)
            (execution.network.known (eventOwner event)) submission⟩] := by
  rw [remainingVisit_network, latest_submission event execution submission address serials]
  have found := serials.lookup_submit (eventOwner event)
    (packet (submit execution.application (eventOwner event) submission) (eventOwner event)
      (execution.network.known (eventOwner event)) submission)
  change (execution.respond (application Claim) (eventOwner event)
    ⟨some (.submit submission)⟩).network.lookup
      (eventOwner event, execution.network.nextSerial (eventOwner event)) = _ at found
  simp only [effect, recordEnvironment, ReactiveApplication.Execution.includePending,
    MessageNetwork.includePending, found]
  rfl

theorem playing_binding_publicGuess {Claim : Type} (defaultClaim : Claim) (event : Event)
    (early : event.val < 3) (execution : (application Claim).Execution)
    (serials : execution.network.SerialsBeforeNext) (binding : PublicationResult Bool)
    (beforeWho afterWho : Player) :
    publicGuess ((remainingVisit event (execution.respond (application Claim) (eventOwner event)
      (playing Claim defaultClaim event binding))).observe (application Claim) afterWho) =
        publicGuess (execution.observe (application Claim) beforeWho) := by
  have recorded := remainingVisit_submission_ledger event execution
    ⟨some event, .bind, defaultClaim, binding, none⟩ rfl serials
  have playingEq : playing Claim defaultClaim event binding =
      ⟨some (.submit ⟨some event, .bind, defaultClaim, binding, none⟩)⟩ := by
    simp only [playing, early, ↓reduceIte]
  rw [playingEq]
  simp only [publicGuess, ReactiveApplication.Execution.observe, MessageNetwork.observe]
  rw [recorded]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    packet, certificates, Option.toFinset_none, Finset.filter_empty, reduceCtorEq,
    ↓reduceIte, Finset.union_self, Finset.toList_empty, List.append_nil]

theorem visitInput_publicGuess {Claim : Type} (event : Event)
    (execution : (application Claim).Execution) (beforeWho afterWho : Player) :
    publicGuess ((visitInput event execution).observe (application Claim) afterWho) =
      publicGuess (execution.observe (application Claim) beforeWho) := rfl

theorem carol_prescribed_publicGuess (Claim : Type) (defaultClaim : Claim)
    (execution : (application Claim).Execution)
    (serials : execution.network.SerialsBeforeNext)
    (visited : execution.application.visit = some 1) (response : (application Claim).Action)
    (supported : response ∈ (policy Claim defaultClaim carol (execution.recall carol)
      (execution.observe (application Claim) carol)).support) :
    publicGuess ((visitInput 2 (remainingVisit 1
      (execution.respond (application Claim) carol response))).observe (application Claim) bob) =
        publicGuess (execution.observe (application Claim) carol) := by
  change response ∈ (policy Claim defaultClaim (eventOwner 1) (execution.recall carol)
    (execution.observe (application Claim) carol)).support at supported
  simp only [policy, show (execution.observe (application Claim) carol).application.visit =
    some 1 from visited, ↓reduceIte, Fin.val_one, one_ne_zero,
    FinDist.mem_support_pure] at supported
  subst response
  rw [visitInput_publicGuess 2 _ carol bob]
  exact playing_binding_publicGuess defaultClaim 1 (by decide) execution serials _ carol carol

end VegasTests.SelectiveAssociation.NamedSource
