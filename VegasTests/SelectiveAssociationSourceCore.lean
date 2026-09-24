/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationGame
import Vegas.Source.CommitmentEvidence

/-! # The actual source transitions underlying the selective-association service

The communication fixture uses the existing stage-local source contract.
Request-shaped early traffic is a claim; it does not create an immutable hidden
pending source action. Certificates concern bindings already in the source
context. Thus the intended separation concerns this whole named-evidence
interface, not every possible intermediate language of pending proposals.

This file only exposes the six deterministic transitions of the actual source
program. It adds neither a source executor nor a communication service.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.SourceProgram GameTheory.Math.Probability

abbrev SourceCore := ProtocolState sourceProgram

def initialCore : SourceCore :=
  ProtocolState.entry sourceProgram (sourceSetup.initialConfig (Env.empty _))

def coreStage : SourceCore → Fin 7
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr (.inl _))) => 3
  | .inr (.inr (.inr (.inr (.inl _)))) => 4
  | .inr (.inr (.inr (.inr (.inr (.inl _))))) => 5
  | .inr (.inr (.inr (.inr (.inr (.inr _))))) => 6

def coreChoice (core : SourceCore) (binding : PublicationResult Bool) (disclose : Bool) :
    Option (OwnAction Player simpleExpr) :=
  match core with
  | .inl _ => some (.commit alice 0 .bool binding)
  | .inr (.inl _) => some (.commit carol 1 .bool binding)
  | .inr (.inr (.inl _)) => some (.commit bob 2 .bool binding)
  | .inr (.inr (.inr (.inl _))) => some (.reveal alice 0 disclose)
  | .inr (.inr (.inr (.inr (.inl _)))) => some (.reveal carol 1 disclose)
  | .inr (.inr (.inr (.inr (.inr (.inl _))))) => some (.reveal bob 2 disclose)
  | .inr (.inr (.inr (.inr (.inr (.inr _))))) => none

/-- Every transition law is the original source law, which is deterministic in
this particular program. The definition selects its unique supported state. -/
def coreAdvance (core : SourceCore) (binding : PublicationResult Bool) (disclose : Bool) :
    SourceCore :=
  (ProtocolState.step sourceProgram core
    (fun _ => coreChoice core binding disclose)).support_nonempty.choose

theorem coreAdvance_supported (core : SourceCore) (binding : PublicationResult Bool)
    (disclose : Bool) : coreAdvance core binding disclose ∈
      (ProtocolState.step sourceProgram core (fun _ => coreChoice core binding disclose)).support :=
  (ProtocolState.step sourceProgram core
    (fun _ => coreChoice core binding disclose)).support_nonempty.choose_spec

theorem core_step_deterministic (core : SourceCore)
    (joint : Player → Option (OwnAction Player simpleExpr)) :
    ∃ after, ProtocolState.step sourceProgram core joint = FinDist.pure after := by
  rcases core with config | config | config | config | config | config | config
  all_goals simp [sourceProgram, ProtocolState.step, FinDist.map_pure]

theorem coreAdvance_law (core : SourceCore) (binding : PublicationResult Bool) (disclose : Bool) :
    ProtocolState.step sourceProgram core (fun _ => coreChoice core binding disclose) =
      FinDist.pure (coreAdvance core binding disclose) := by
  obtain ⟨after, same⟩ := core_step_deterministic core (fun _ => coreChoice core binding disclose)
  have reached := coreAdvance_supported core binding disclose
  rw [same, FinDist.mem_support_pure] at reached
  exact same.trans (congrArg FinDist.pure reached.symm)

theorem coreAdvance_eq_of_law (core : SourceCore) (binding : PublicationResult Bool)
    (disclose : Bool) (after : SourceCore)
    (same : ProtocolState.step sourceProgram core (fun _ => coreChoice core binding disclose) =
      FinDist.pure after) : coreAdvance core binding disclose = after := by
  have reached := coreAdvance_supported core binding disclose
  rwa [same, FinDist.mem_support_pure] at reached

theorem coreAdvance_evidence (core : SourceCore) (binding : PublicationResult Bool)
    (disclose : Bool) (fact : CommitmentEvidence Player simpleExpr)
    (known : core.evidenceHolds sourceProgram fact) :
    (coreAdvance core binding disclose).evidenceHolds sourceProgram fact :=
  ProtocolState.evidenceHolds_step sourceProgram core _ _
    (coreAdvance_supported core binding disclose) fact known

namespace CorePath

def start := sourceSetup.initialConfig (Env.empty _)
def aliceBound (a : PublicationResult Bool) := commitSuccessor 0 (acceptingGuard alice 0) start a
def carolBound (a c : PublicationResult Bool) :=
  commitSuccessor 1 (acceptingGuard carol 1) (aliceBound a) c
def bobBound (a c b : PublicationResult Bool) :=
  commitSuccessor 2 (acceptingGuard bob 2) (carolBound a c) b
def aliceOpened (a c b : PublicationResult Bool) (first : Bool) :=
  revealSuccessor 3 (.there (.there .here)) (bobBound a c b) first
def carolOpened (a c b : PublicationResult Bool) (first second : Bool) :=
  revealSuccessor 4 (.there (.there .here)) (aliceOpened a c b first) second
def bobOpened (a c b : PublicationResult Bool) (first second third : Bool) :=
  revealSuccessor 5 (.there (.there .here)) (carolOpened a c b first second) third

def alice (a : PublicationResult Bool) : SourceCore := .inr (.inl (aliceBound a))
def carol (a c : PublicationResult Bool) : SourceCore := .inr (.inr (.inl (carolBound a c)))
def bob (a c b : PublicationResult Bool) : SourceCore :=
  .inr (.inr (.inr (.inl (bobBound a c b))))
def openedAlice (a c b : PublicationResult Bool) (first : Bool) : SourceCore :=
  .inr (.inr (.inr (.inr (.inl (aliceOpened a c b first)))))
def openedCarol (a c b : PublicationResult Bool) (first second : Bool) : SourceCore :=
  .inr (.inr (.inr (.inr (.inr (.inl (carolOpened a c b first second))))))
def final (a c b : PublicationResult Bool) (first second third : Bool) : SourceCore :=
  .inr (.inr (.inr (.inr (.inr (.inr (bobOpened a c b first second third))))))

theorem initial_advance (a : PublicationResult Bool) (disclose : Bool) :
    coreAdvance initialCore a disclose = alice a := by
  apply coreAdvance_eq_of_law
  simp [initialCore, sourceProgram, ProtocolState.step, ProtocolState.entry,
    coreChoice, OwnAction.binding_commit, alice, aliceBound, start]

theorem alice_advance (a c : PublicationResult Bool) (disclose : Bool) :
    coreAdvance (alice a) c disclose = carol a c := by
  apply coreAdvance_eq_of_law
  simp [alice, sourceProgram, ProtocolState.step, ProtocolState.entry,
    coreChoice, OwnAction.binding_commit, carol, carolBound, FinDist.map_pure]

theorem carol_advance (a c b : PublicationResult Bool) (disclose : Bool) :
    coreAdvance (carol a c) b disclose = bob a c b := by
  apply coreAdvance_eq_of_law
  simp [carol, sourceProgram, ProtocolState.step, ProtocolState.entry,
    coreChoice, OwnAction.binding_commit, bob, bobBound, FinDist.map_pure]

theorem bob_advance (a c b unused : PublicationResult Bool) (first : Bool) :
    coreAdvance (bob a c b) unused first = openedAlice a c b first := by
  apply coreAdvance_eq_of_law
  simp [bob, sourceProgram, ProtocolState.step, ProtocolState.entry,
    coreChoice, OwnAction.disclosure, openedAlice, aliceOpened, FinDist.map_pure]

theorem aliceOpening_advance (a c b unused : PublicationResult Bool) (first second : Bool) :
    coreAdvance (openedAlice a c b first) unused second = openedCarol a c b first second := by
  apply coreAdvance_eq_of_law
  simp [openedAlice, sourceProgram, ProtocolState.step, ProtocolState.entry,
    coreChoice, OwnAction.disclosure, openedCarol, carolOpened, FinDist.map_pure]

theorem carolOpening_advance (a c b unused : PublicationResult Bool) (first second third : Bool) :
    coreAdvance (openedCarol a c b first second) unused third = final a c b first second third := by
  apply coreAdvance_eq_of_law
  simp [openedCarol, sourceProgram, ProtocolState.step, ProtocolState.entry,
    coreChoice, OwnAction.disclosure, final, bobOpened, FinDist.map_pure]

end CorePath

end VegasTests.SelectiveAssociation
