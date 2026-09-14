/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.LogicalCommitment
import Interaction.SealedCandidateResolution

/-! # Representative logical commitment traces

These tests concern the isolated logical machine, not a native refinement or
an equilibrium-preservation claim.
-/

namespace InteractionTests.LogicalCommitment

open Interaction Interaction.LogicalCommitment

/-- A finite instance used only to check representative logical traces. -/
def protocol : LogicalCommitment Bool Bool where
  owner := false
  handleOwner := fun _ => false

def earlyClaim : Claim Bool Bool Nat := .open false false 11

def earlyOpeningTrace : List (Action Bool Bool Nat) :=
  [.prepare false false 11,
    .submit false earlyClaim, .expose true earlyClaim, .include earlyClaim]

/-- A visible opening claim exposes its claimed value but does not resolve the
binding before a handle has been selected.  Its failed inclusion remains public. -/
theorem earlyOpening_stays_pending :
    let final := protocol.run State.empty earlyOpeningTrace
    final.result = .pending ∧
      final.inbox true = [earlyClaim] ∧
      final.ledger = [earlyClaim] ∧
      final.receipts = [(earlyClaim, false)] := by
  decide

def competingTrace : List (Action Bool Bool Nat) :=
  [.prepare false false 11,
    .prepare false true 22,
    .submit false (.select false true),
    .include (.select false true),
    .submit false (.select false false),
    .include (.select false false),
    .submit false (.open false false 11),
    .include (.open false false 11),
    .submit false (.open false true 22),
    .include (.open false true 22)]

/-- Of two prepared candidates, the first included selection remains binding;
the competing selection and its opening are rejected, while the selected
candidate opens with its immutable value. -/
theorem competing_first_selection_wins :
    let final := protocol.run State.empty competingTrace
    final.result = .opened 22 ∧
      final.selected = some true ∧
      final.ledger =
        [.select false true, .select false false,
          .open false false 11, .open false true 22] ∧
      final.receipts =
        [(.select false true, true), (.select false false, false),
          (.open false false 11, false), (.open false true 22, true)] := by
  decide

def unopenableTrace : List (Action Bool Bool Nat) :=
  [.submit false (.select false false),
    .include (.select false false),
    .prepare false false 11,
    .submit false (.malformed false),
    .include (.malformed false),
    .submit false (.open false false 11),
    .include (.open false false 11),
    .settleQuit false]

/-- Accepting an unprepared handle fixes it as unopenable. Later preparation
and opening cannot repair it; malformed traffic remains publicly rejected,
and an attributed fallback leaves the selected handle intact. -/
theorem unopenable_resolves_by_fallback :
    let final := protocol.run State.empty unopenableTrace
    final.result = .quit ∧
      final.selected = some false ∧
      final.meanings false = .unopenable ∧
      final.receipts =
        [(.select false false, true), (.malformed false, false),
          (.open false false 11, false)] := by
  decide

/-! ## Native prerequisite rejection versus the ungated logical kernel

This single transition is an operational projection counterexample.  It does
not rule out a coarser strategic simulation with additional admission gates or
certified native effects. -/

/-- Node `1` is an owner commitment whose sole prerequisite is the ordinary,
still-incomplete commitment at node `0`. -/
def nativePrerequisiteProgram : SealedProgram Bool :=
  ⟨[⟨.commit true, []⟩, ⟨.commit false, [0]⟩]⟩

def blockedNativeSelection : Message Bool (SealedProgram.Payload Bool Nat) :=
  ⟨(false, 0), .commitment 1 (false, 7)⟩

def projectedProtocol : LogicalCommitment Bool (CommitmentHandle Bool Nat) where
  owner := false
  handleOwner := Prod.fst

def projectedSelection : Claim Bool (CommitmentHandle Bool Nat) Nat :=
  .select false (false, 7)

/-- The actual candidate validator rejects selection at a commitment node with
an incomplete prerequisite.  The current ungated logical inclusion accepts
the corresponding owner-authored selection and records a positive receipt.
Thus this literal one-step operational projection does not preserve admission
or public receipts; the result makes no claim about strategic simulation. -/
theorem incomplete_prerequisite_breaks_literal_projection :
    nativePrerequisiteProgram.candidateMessage?
        (CommitmentCandidates.empty : CommitmentCandidates Bool Nat Nat)
        [] blockedNativeSelection = none ∧
      let logicalNext := (State.empty :
        LogicalCommitment.State Bool (CommitmentHandle Bool Nat) Nat).recordInclusion
          projectedProtocol projectedSelection
      logicalNext.selected = some (false, 7) ∧
        logicalNext.receipts = [(projectedSelection, true)] := by
  decide

end InteractionTests.LogicalCommitment

/-- info: 'InteractionTests.LogicalCommitment.incomplete_prerequisite_breaks_literal_projection'
depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms InteractionTests.LogicalCommitment.incomplete_prerequisite_breaks_literal_projection
