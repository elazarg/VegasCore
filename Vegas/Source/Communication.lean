/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitmentEvidence
import Vegas.Source.SetupProtocol
import Interaction.CommunicationKnowledge
import Interaction.CommunicationBounded

/-! # Source games with communication and opening evidence

The program and its publication results are unchanged. The communication
interface adds claims, transferable evidence of owned commitments, and public
evidence from a disclosure action. Guard rejection affects the publication
result but cannot retract the evidence that the action supplied.

The claim alphabet and communication roster are parameters of the analysis.
This module supplies no native sequential-equilibrium preservation theorem.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open Interaction Interaction.Communication

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

def evidenceValid (setup : Setup (Player := Player) (L := L))
    (state : setup.ProtocolState) (fact : CommitmentEvidence Player L) : Prop :=
  state.elim False (fun current =>
    SourceProgram.ProtocolState.evidenceHolds setup.program current fact)

def possessesEvidence (setup : Setup (Player := Player) (L := L))
    (who : Player) (view : setup.ProtocolView who) (fact : CommitmentEvidence Player L) : Prop :=
  view.elim False (fun current => SourceProgram.ProtocolView.possessesEvidence who
    setup.program current fact)

def disclosedEvidence (setup : Setup (Player := Player) (L := L))
    (state : setup.ProtocolState) (joint : Player → Option (OwnAction Player L)) :
    List (CommitmentEvidence Player L) :=
  state.elim [] (fun current =>
    SourceProgram.ProtocolState.disclosedEvidence setup.program current joint)

theorem possessesEvidence_sound (setup : Setup (Player := Player) (L := L))
    (who : Player) (state : setup.ProtocolState) (fact : CommitmentEvidence Player L)
    (known : setup.possessesEvidence who (setup.protocolObserve who state) fact) :
    setup.evidenceValid state fact := by
  cases state with
  | none => exact known
  | some current =>
      exact SourceProgram.ProtocolView.possessesEvidence_sound who setup.program current fact known

theorem evidenceValid_step (setup : Setup (Player := Player) (L := L))
    (before after : setup.ProtocolState) (joint : Player → Option (OwnAction Player L))
    (reached : after ∈ (setup.protocolStep before joint).support)
    (fact : CommitmentEvidence Player L) (known : setup.evidenceValid before fact) :
    setup.evidenceValid after fact := by
  cases before with
  | none => exact known.elim
  | some current =>
      obtain ⟨target, realized, rfl⟩ := FinDist.support_map .. ▸ reached
      exact SourceProgram.ProtocolState.evidenceHolds_step setup.program current target joint
        realized fact known

theorem disclosedEvidence_sound (setup : Setup (Player := Player) (L := L))
    (before after : setup.ProtocolState) (joint : Player → Option (OwnAction Player L))
    (reached : after ∈ (setup.protocolStep before joint).support)
    (fact : CommitmentEvidence Player L) (member : fact ∈ setup.disclosedEvidence before joint) :
    setup.evidenceValid after fact := by
  cases before with
  | none => exact False.elim (List.not_mem_nil member)
  | some current =>
      obtain ⟨target, realized, rfl⟩ := FinDist.support_map .. ▸ reached
      exact SourceProgram.ProtocolState.disclosedEvidence_sound setup.program current target joint
        realized fact member

/-- An ordinary commitment provides transferable evidence. Communication is
available at semantic service opportunities, without additional source opcodes. -/
def communicationInterface (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) (Claim : Type) :
    CommunicationInterface (setup.informationModel admission) where
  Claim := Claim
  Evidence := CommitmentEvidence Player L
  possesses := setup.possessesEvidence
  valid history := setup.evidenceValid history.state
  sound who history fact known := by
    change setup.possessesEvidence who
      ((setup.protocolSignals admission).infoOf who history.trace) fact at known
    rw [setup.protocol_info] at known
    exact setup.possessesEvidence_sound who history.state fact known
  persists history joint legal target realized fact known :=
    setup.evidenceValid_step history.state target joint realized fact known
  emissions event := (setup.disclosedEvidence event.source event.joint).map fun fact =>
    ⟨fact.owner, .broadcast, .evidence fact⟩
  emissions_sound history joint legal target realized message member fact same := by
    obtain ⟨disclosed, present, rfl⟩ := List.mem_map.mp member
    have equal : disclosed = fact := Communication.Content.evidence.inj same
    subst fact
    exact setup.disclosedEvidence_sound history.state target joint realized disclosed present

end Vegas.SourceProgram.Setup
