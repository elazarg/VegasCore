/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidateResolution
import GameTheoryExtensions.Math.Probability.SequentialDecisionObservation

/-! # Two decisions at the native candidate boundary

This finite experiment uses the actual candidate `MessageApplication`. An
owner first prepares a Boolean value. A fixed native segment accepts its
commitment, submits a competing unauthenticated opening, and exposes that
opening to the owner either pending or already included and rejected. The
owner's second response may submit a claimed opening or withhold. A fixed
continuation includes a submitted response and then advances the clock;
matching claims open normally, whereas mismatches and withholding resolve to
the runtime default.

The arbitrary second policy sees the actual owner view, auxiliary initial
metadata, and its recalled first action. It never receives the private
candidate catalog. The logical policy retains the first action and the
pending-versus-included disclosure reconstructed from that view. This is a
single-binding, fixed-segment policy law, not a service theorem or a
whole-program native/logical simulation.
-/

noncomputable section

namespace InteractionTests.LogicalCommitmentNative

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

def runtime : SealedResolution Bool (Option Bool) :=
  ⟨⟨[⟨.commit false, []⟩, ⟨.reveal false 0, [0]⟩]⟩, none, 1⟩

abbrev app := runtime.candidateApplication

def initial : app.State := State.initial app runtime.candidateInitial

def commitment : SealedProgram.Payload Bool (Option Bool) :=
  .commitment 0 (false, 0)

def competingOpening (claimed : Option Bool) :
    SealedProgram.Payload Bool (Option Bool) :=
  .opening 1 (false, 0) claimed

def ownerOpening (claimed : Bool) :
    SealedProgram.Payload Bool (Option Bool) :=
  .opening 1 (false, 0) (some claimed)

/-- An observable opening disclosure and whether the fixed segment also attempts
to include it. Inclusion is rejected because the competing sender is not the
commitment owner. -/
structure Disclosure where
  claimed : Option Bool
  included : Bool

private def registered (value : Bool) : app.State :=
  { initial with application :=
      app.privateStep initial.application false ⟨(0, some value)⟩ }

private def commitmentSubmitted (value : Bool) : app.State :=
  { registered value with
    pool := ((registered value).pool.submit false commitment).2 }

private def commitmentIncluded (value : Bool) : app.State :=
  app.includePending (commitmentSubmitted value) (false, 0)

private def competitorSubmitted (value : Bool) (disclosure : Disclosure) : app.State :=
  { commitmentIncluded value with
    pool := ((commitmentIncluded value).pool.submit true
      (competingOpening disclosure.claimed)).2 }

private def competitorDelivered (value : Bool) (disclosure : Disclosure) : app.State :=
  { competitorSubmitted value disclosure with
    pool := ((competitorSubmitted value disclosure).pool.deliver false (true, 0)).state }

def disclosedState (value : Bool) (disclosure : Disclosure) : app.State :=
  if disclosure.included then
    app.includePending (competitorDelivered value disclosure) (true, 0)
  else competitorDelivered value disclosure

private def firstSegment (value : Bool) (disclosure : Disclosure) : List app.Action :=
  [.privateCommand false ⟨(0, some value)⟩,
    .submit false commitment, .include (false, 0),
    .submit true (competingOpening disclosure.claimed),
    .deliver false (true, 0)] ++
      if disclosure.included then [.include (true, 0)] else []

/-- Every disclosure branch is produced by actual native application steps;
the branch choice is fixed independently of both owner policies. -/
theorem firstSegment_run (value : Bool) (disclosure : Disclosure) :
    app.run (firstSegment value disclosure) initial =
      FinDist.pure (disclosedState value disclosure) := by
  rcases disclosure with ⟨claimed, included⟩
  cases included <;>
    simp only [firstSegment, Bool.false_eq_true, ↓reduceIte, List.append_nil,
      List.cons_append, List.nil_append, MessageApplication.run, MessageApplication.step,
      FinDist.pure_bind] <;> rfl

/-- The information retained at the second decision. The outer option
distinguishes an absent opening from an opening whose claim is `none`. -/
structure OpeningObservation where
  inboxClaim : Option (Option Bool)
  ledgerClaim : Option (Option Bool)

private def firstOpeningClaim
    (messages : List (Message Bool (SealedProgram.Payload Bool (Option Bool)))) :
    Option (Option Bool) :=
  messages.findSome? fun message => match message.payload with
    | .opening _ _ claimed => some claimed
    | .commitment _ _ | .cleartext _ _ | .malformed => none

private def observePending (state : app.State) : OpeningObservation :=
  let view := State.observe app state false
  ⟨firstOpeningClaim view.messages.inbox,
    firstOpeningClaim view.messages.ledger⟩

private def disclosureObservation (disclosure : Disclosure) : OpeningObservation :=
  ⟨some disclosure.claimed,
    if disclosure.included then some disclosure.claimed else none⟩

/-- Pending and included disclosures are distinguished by the actual owner
view. Inclusion preserves the inbox copy and records the rejected opening in
the public ledger. -/
theorem disclosedState_observation (value : Bool) (disclosure : Disclosure) :
    observePending (disclosedState value disclosure) =
      disclosureObservation disclosure := by
  rcases disclosure with ⟨claimed, included⟩
  cases value <;> cases claimed with
  | none => cases included <;> rfl
  | some claimed => cases claimed <;> cases included <;> rfl

/-- Visibility and ledger inclusion do not grant authority: the competing
opening fails the actual candidate handler's sender authentication. -/
theorem competingOpening_rejected (value : Bool) (disclosure : Disclosure) :
    runtime.candidateHandle (disclosedState value disclosure).application
      ⟨(true, 0), competingOpening disclosure.claimed⟩ = none := by
  rcases disclosure with ⟨claimed, included⟩
  cases value <;> cases claimed with
  | none => cases included <;> decide
  | some claimed => cases claimed <;> cases included <;> decide

private def responseSubmitted (value : Bool) (disclosure : Disclosure)
    (claimed : Bool) : app.State :=
  { disclosedState value disclosure with
    pool := ((disclosedState value disclosure).pool.submit false
      (ownerOpening claimed)).2 }

private def responseIncluded (value : Bool) (disclosure : Disclosure)
    (claimed : Bool) : app.State :=
  app.includePending (responseSubmitted value disclosure claimed) (false, 1)

private def afterClock (state : app.State) : app.State :=
  { state with application := runtime.tick state.application }

private def settled (value : Bool) (disclosure : Disclosure) : Option Bool → app.State
  | none => afterClock (disclosedState value disclosure)
  | some claimed => afterClock (responseIncluded value disclosure claimed)

private def finishSegment : Option Bool → List app.Action
  | none => [.environment ⟨()⟩]
  | some claimed =>
      [.submit false (ownerOpening claimed), .include (false, 1), .environment ⟨()⟩]

private theorem responseStep_clock (state : app.State) :
    app.step state (.environment ⟨()⟩) = FinDist.pure (afterClock state) := by
  simp [app, runtime, SealedResolution.candidateApplication, SealedResolution.host,
    MessageApplication.step, afterClock]

private theorem finishSegment_run (value : Bool) (disclosure : Disclosure)
    (response : Option Bool) :
    app.run (finishSegment response) (disclosedState value disclosure) =
      FinDist.pure (settled value disclosure response) := by
  cases response with
  | none =>
      rw [show finishSegment none = [.environment ⟨()⟩] from rfl]
      rw [MessageApplication.run_cons, responseStep_clock, FinDist.pure_bind]
      rfl
  | some claimed =>
      rw [show finishSegment (some claimed) =
        [.submit false (ownerOpening claimed), .include (false, 1),
          .environment ⟨()⟩] from rfl]
      simp only [MessageApplication.run_cons, MessageApplication.step, FinDist.pure_bind]
      simp only [app, SealedResolution.candidateApplication, SealedResolution.host,
        FinDist.map_pure, FinDist.pure_bind]
      rfl

abbrev Outcome := Option (Option Bool) × Bool

def outcome (state : app.State) : Outcome :=
  (state.application.visible.published? 1,
    state.application.visible.timeouts.contains 1)

/-- Authentication and the fixed clock distinguish a matching recalled claim
from a mismatch or withholding, independently of the competing disclosure. -/
theorem settled_outcome (value : Bool) (disclosure : Disclosure)
    (response : Option Bool) :
    outcome (settled value disclosure response) =
      if response = some value then (some (some value), false)
      else (some none, true) := by
  rcases disclosure with ⟨disclosed, included⟩
  cases value <;> cases disclosed with
  | none =>
      cases included <;> cases response with
      | none => decide
      | some claimed => cases claimed <;> decide
  | some disclosed =>
      cases disclosed <;> cases included <;> cases response with
      | none => decide
      | some claimed => cases claimed <;> decide

private def nativeNext (disclosures : FinDist Disclosure)
    (_ : Fin 2) (value : Bool) : FinDist app.State :=
  disclosures.bind fun disclosure => app.run (firstSegment value disclosure) initial

def logicalNext (disclosures : FinDist Disclosure)
    (_ : Unit) (_ : Bool) : FinDist OpeningObservation :=
  disclosures.map disclosureObservation

private def nativeFinish
    (history : Fin 2 × Bool × app.State) (response : Option Bool) : FinDist Outcome :=
  (app.run (finishSegment response) history.2.2).map outcome

def logicalFinish
    (history : Unit × Bool × OpeningObservation) (response : Option Bool) : FinDist Outcome :=
  FinDist.pure (if response = some history.2.1 then
    (some (some history.2.1), false) else (some none, true))

private theorem nativeNext_factor
    (disclosures : FinDist Disclosure) (info : Fin 2) (value : Bool) :
    (nativeNext disclosures info value).map observePending =
      logicalNext disclosures () value := by
  rw [nativeNext, logicalNext, FinDist.map_bind, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro disclosure _
  rw [firstSegment_run, FinDist.map_pure, disclosedState_observation]

private theorem nativeFinish_factor
    (disclosures : FinDist Disclosure) (info : Fin 2) (value : Bool)
    (later : app.State) (hlater : later ∈ (nativeNext disclosures info value).support)
    (response : Option Bool) :
    nativeFinish (info, value, later) response =
      logicalFinish ((), value, observePending later) response := by
  simp only [nativeNext, FinDist.support_bind, Set.mem_iUnion] at hlater
  obtain ⟨disclosure, _hdisclosure, hlater⟩ := hlater
  rw [firstSegment_run, FinDist.mem_support_pure] at hlater
  subst later
  rw [nativeFinish, finishSegment_run, FinDist.map_pure, logicalFinish,
    settled_outcome]

/-- Arbitrary two-stage policies using auxiliary metadata and the actual owner
view have an exact policy on the recalled first action and owner-visible
pending versus publicly included claims. The disclosure law, native transition,
and settlement continuation are fixed independently of both policies. -/
theorem candidate_two_decision_policy_law
    (metadata : FinDist (Fin 2)) (disclosures : FinDist Disclosure)
    (first : Fin 2 → FinDist Bool)
    (second : Fin 2 × Bool × app.View → FinDist (Option Bool)) :
    ∃ logicalFirst : Unit → FinDist Bool,
      ∃ logicalSecond : Unit × Bool × OpeningObservation → FinDist (Option Bool),
        (metadata.bind fun info => (first info).bind fun value =>
          disclosures.bind fun disclosure =>
            (second (info, value, State.observe app (disclosedState value disclosure) false)).bind
              fun response => FinDist.pure (if response = some value then
                (some (some value), false) else (some none, true))) =
        ((metadata.map fun _ => ()).bind fun info =>
          (logicalFirst info).bind fun value =>
            (logicalNext disclosures info value).bind fun later =>
              (logicalSecond (info, value, later)).bind
                (logicalFinish (info, value, later))) := by
  have hlaw := FinDist.exists_two_decision_policy_law metadata (fun _ => ()) observePending
    (nativeNext disclosures) (logicalNext disclosures)
    (fun info _ value => nativeNext_factor disclosures info value) nativeFinish logicalFinish
    (fun info _ value later hlater response =>
      nativeFinish_factor disclosures info value later hlater response) first
    (fun history => second
      (history.1, history.2.1, State.observe app history.2.2 false))
  have hfinish (info : Fin 2) (value : Bool) (disclosure : Disclosure) :
      nativeFinish (info, value, disclosedState value disclosure) =
        fun response => FinDist.pure (if response = some value then
          (some (some value), false) else (some none, true)) := by
    funext response
    rw [nativeFinish, finishSegment_run, FinDist.map_pure, settled_outcome]
  simpa only [nativeNext, FinDist.bind_bind, firstSegment_run,
    FinDist.pure_bind, hfinish] using hlaw

end InteractionTests.LogicalCommitmentNative

/-- info: 'InteractionTests.LogicalCommitmentNative.candidate_two_decision_policy_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms InteractionTests.LogicalCommitmentNative.candidate_two_decision_policy_law
