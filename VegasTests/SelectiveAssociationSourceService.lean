/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceCore
import Interaction.ReactiveReplayMenu

/-! # Pending named evidence around the stage-local source game

This fixture uses the original source contract: game actions are stage-local.
An early request-shaped message remains a claim and creates no immutable hidden
pending source action. This differs deliberately from the native proposal
capability. The eventual separation concerns this complete source interface;
it is not a necessity theorem for every possible pending-request language.

Claims range over any declared finite nonempty alphabet. Every response permits
silence, transmission, and replay of every known envelope. Certificates name
already accepted source bindings; owned and received facts can be forwarded.
The first Alice envelope can be noticed by Bob while pending. Recording occurs
separately, and records rejected request-shaped traffic too. Core transitions
use the actual source step from `SelectiveAssociationSourceCore`.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Vegas.SourceProgram Interaction GameTheory.Math.Probability

abbrev Event := Fin 6
abbrev NamedFact := Fin 3 × Bool

def bindingOwner (binding : Fin 3) : Player :=
  if binding = 0 then alice else if binding = 1 then carol else bob

def eventOwner (event : Event) : Player := bindingOwner ⟨event.val % 3, Nat.mod_lt _ (by decide)⟩

def NamedFact.toSource (fact : NamedFact) : CommitmentEvidence Player simpleExpr :=
  ⟨bindingOwner fact.1, fact.1.val, .bool, fact.2⟩

inductive RequestKind where
  | bind
  | open
  | withhold
  | claim
  deriving DecidableEq, Fintype

structure Packet (Claim : Type) where
  address : Option Event
  kind : RequestKind
  claim : Claim
  evidence : Finset NamedFact
  deriving DecidableEq, Fintype

structure Submission (Claim : Type) where
  address : Option Event
  kind : RequestKind
  claim : Claim
  binding : PublicationResult Bool
  evidence : Option NamedFact
  deriving DecidableEq, Fintype

structure State where
  core : SourceCore
  visit : Option Event
  clock : Nat

def initial : State := ⟨initialCore, none, 0⟩

structure PlayerView where
  who : Player
  core : ProtocolView who sourceProgram
  visit : Option Event
  clock : Nat

def observe (state : State) (who : Player) : PlayerView :=
  ⟨who, ProtocolState.observe who sourceProgram state.core, state.visit, state.clock⟩

def publications : SourceCore → Player → Option (PublicationResult Bool)
  | .inl _, _ => none
  | .inr (.inl _), _ => none
  | .inr (.inr (.inl _)), _ => none
  | .inr (.inr (.inr (.inl _))), _ => none
  | .inr (.inr (.inr (.inr (.inl config)))), who =>
      if who = alice then some (config.state.get .here) else none
  | .inr (.inr (.inr (.inr (.inr (.inl config))))), who =>
      if who = alice then some (config.state.get (.there .here)) else
      if who = carol then some (config.state.get .here) else none
  | .inr (.inr (.inr (.inr (.inr (.inr config))))), who =>
      if who = alice then some (config.state.get (.there (.there .here))) else
      if who = carol then some (config.state.get (.there .here)) else
      some (config.state.get .here)

structure PublicView where
  stage : Fin 7
  publications : Player → Option (PublicationResult Bool)
  visit : Option Event
  clock : Nat

def publicView (state : State) : PublicView :=
  ⟨coreStage state.core, publications state.core, state.visit, state.clock⟩

def State.owns (state : State) (who : Player) (fact : NamedFact) : Prop :=
  ProtocolView.possessesEvidence who sourceProgram
    (ProtocolState.observe who sourceProgram state.core) fact.toSource

theorem owns_sound (state : State) (who : Player) (fact : NamedFact)
    (possessed : state.owns who fact) :
    state.core.evidenceHolds sourceProgram fact.toSource :=
  ProtocolView.possessesEvidence_sound who sourceProgram state.core fact.toSource possessed

def State.mayForward {Claim : Type} (state : State) (who : Player)
    (known : List (Message Player (Packet Claim))) (fact : NamedFact) : Prop :=
  state.owns who fact ∨ ∃ message ∈ known, fact ∈ message.payload.evidence

open Classical in
def certificates {Claim : Type} (state : State) (who : Player)
    (known : List (Message Player (Packet Claim))) (submission : Submission Claim) :
    Finset NamedFact :=
  submission.evidence.toFinset.filter (state.mayForward who known) ∪
    if submission.kind = .open then
      Finset.univ.filter fun fact => state.owns who fact ∧
        submission.address = some ⟨fact.1.val + 3, by omega⟩
    else ∅

/-- Ordinary disclosure supplies its owned named fact. A separate requested
certificate may accompany it, including evidence received from another player. -/
def packet {Claim : Type} (state : State) (who : Player)
    (known : List (Message Player (Packet Claim))) (submission : Submission Claim) :
    Packet Claim :=
  ⟨submission.address, submission.kind, submission.claim,
    certificates state who known submission⟩

open Classical in
def submit {Claim : Type} (state : State) (who : Player) (submission : Submission Claim) :
    State :=
  match state.visit, submission.address with
  | some event, some addressed =>
      if addressed = event ∧ who = eventOwner event ∧ (coreStage state.core).val = event.val then
        if event.val < 3 ∧ submission.kind = .bind then
          { state with core := coreAdvance state.core submission.binding false }
        else if 3 ≤ event.val ∧ submission.kind = .open then
          { state with core := coreAdvance state.core .failure true }
        else if 3 ≤ event.val ∧ submission.kind = .withhold then
          { state with core := coreAdvance state.core .failure false }
        else state
      else state
  | _, _ => state

inductive Command where
  | grant (event : Event)
  | tick
  | settle (event : Event)
  deriving DecidableEq

def command (state : State) : Command → State
  | .grant event => { state with visit := some event }
  | .tick => { state with clock := state.clock + 1 }
  | .settle event =>
      if (coreStage state.core).val = event.val then
        { state with core := coreAdvance state.core .failure false }
      else state

/-- The stateless leak rule reveals only Alice's first envelope to Bob. It
never reports which packet was read to the recording scheduler. -/
def leaks (Claim : Type) : MessageNetwork.ObservationRule Player (Packet Claim) :=
  fun who _ => FinDist.pure (if who = bob then {(alice, 0)} else ∅)

def application (Claim : Type) : ReactiveApplication Player where
  State := State
  Payload := Packet Claim
  Submission := Submission Claim
  EnvironmentCommand := Command
  LocalObservation := PlayerView
  PublicObservation := PublicView
  packet := packet
  submit := submit
  /- Recording acknowledges the envelope. The stage-local source action has
  already occurred at the protected response, or settlement will use its default. -/
  handle state _ := some state
  environment state cmd := FinDist.pure (command state cmd)
  observePlayer := observe
  observePublic := publicView
  observePending := leaks Claim

open Classical in
def baseMenu (Claim : Type) [Fintype Claim] : (application Claim).ResponseMenu where
  actions _ _ _ := {⟨none⟩} ∪
    (Finset.univ : Finset (Submission Claim)).image fun submission =>
      (⟨some (.submit submission)⟩ : (application Claim).Action)
  nonempty _ _ _ := ⟨⟨none⟩, by simp⟩

def menu (Claim : Type) [Fintype Claim] : (application Claim).ResponseMenu :=
  (baseMenu Claim).withKnownReplays

theorem every_submission (Claim : Type) [Fintype Claim] (who : Player)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (submission : Submission Claim) :
    (⟨some (.submit submission)⟩ : (application Claim).Action) ∈
      (menu Claim).actions who past view := by
  classical
  apply (baseMenu Claim).base_available
  change _ ∈ ({⟨none⟩} ∪ (Finset.univ : Finset (Submission Claim)).image
    (fun submission => (⟨some (.submit submission)⟩ : (application Claim).Action)))
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr
    ⟨submission, Finset.mem_univ (α := Submission Claim) submission, rfl⟩

theorem early_claim_core {Claim : Type} (state : State) (who : Player)
    (submission : Submission Claim) (early : state.visit = none) :
    (submit state who submission).core = state.core := by simp [submit, early]

theorem submit_evidence {Claim : Type} (state : State) (who : Player)
    (submission : Submission Claim) (fact : CommitmentEvidence Player simpleExpr)
    (known : state.core.evidenceHolds sourceProgram fact) :
    (submit state who submission).core.evidenceHolds sourceProgram fact := by
  unfold submit
  split
  · split
    · split
      · exact coreAdvance_evidence state.core _ _ fact known
      · split
        · exact coreAdvance_evidence state.core _ _ fact known
        · split
          · exact coreAdvance_evidence state.core _ _ fact known
          · exact known
    · exact known
  · exact known

theorem command_evidence (state : State) (cmd : Command)
    (fact : CommitmentEvidence Player simpleExpr)
    (known : state.core.evidenceHolds sourceProgram fact) :
    (command state cmd).core.evidenceHolds sourceProgram fact := by
  cases cmd with
  | grant | tick => exact known
  | settle event =>
      simp only [command]
      split
      · exact coreAdvance_evidence state.core _ _ fact known
      · exact known

end VegasTests.SelectiveAssociation.NamedSource
