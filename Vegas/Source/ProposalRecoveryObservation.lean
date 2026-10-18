/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryAddress

/-! # Source-addressed truthful proposals from actual recovery transitions -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Source coordinates do not depend on physical packet identities or clocks. -/
structure ProposalRecoveryAddress where
  phase : Nat
  generation : Nat
  event : Nat
  deriving DecidableEq

def ProposalRecoveryAddress.key (address : ProposalRecoveryAddress) : Nat × Nat × Nat :=
  (address.phase, address.generation, address.event)

instance : Ord ProposalRecoveryAddress where
  compare left right := match compare left.phase right.phase with
    | .eq => match compare left.generation right.generation with
      | .eq => compare left.event right.event
      | result => result
    | result => result

/-- A proposal's type and value are recovered from a stored source binding. -/
structure ProposalRecoveryProposal (L : IExpr) where
  address : ProposalRecoveryAddress
  payload : L.Ty
  value : L.Val payload

instance : DecidableEq (ProposalRecoveryProposal L) := Classical.decEq _

namespace ProtocolState

/-- The current reveal's proposed value and absolute rank in this syntax.
Failed stored bindings and withheld reveals have no successful proposal. -/
def recoveryProposal : ∀ {Γ : SourceCtx Player L} {O : Finset VarId},
    (program : SourceProgram Player L Γ O) → ProtocolState program →
    (Player → Option (ProposalRecoveryMove Player L)) → Option (Nat × Sigma L.Val)
  | _, _, .ret _, _, _ => none
  | _, _, .sample _ _ _ next, state, joint => state.elim (fun _ => none)
      (fun later => (recoveryProposal next later joint).map fun pair => (pair.1 + 1, pair.2))
  | _, _, .commit _ _ _ _ next, state, joint => state.elim (fun _ => none)
      (fun later => (recoveryProposal next later joint).map fun pair => (pair.1 + 1, pair.2))
  | _, _, .reveal _ owner _ (payload := payload) _ source _ next, state, joint => state.elim
      (fun config => if ((joint owner).map (·.discloses)).getD false then
        match config.state.get source with
        | .failure => none
        | .success value => some (0, ⟨payload, value⟩)
      else none)
      (fun later => (recoveryProposal next later joint).map fun pair => (pair.1 + 1, pair.2))

end ProtocolState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- Excluded owners do not create proposals during automatic completion. -/
def proposalRecoveryProposalOf (state : setup.proposalRecoveryProtocol.State)
    (joint : Player → Option (ProposalRecoveryMove Player L)) :
    Option (ProposalRecoveryProposal L) :=
  state.bind fun current =>
    (ProtocolState.recoveryProposal setup.program current.point
      (fun who => if who ∈ current.excluded then none else joint who)).map fun pair =>
      ⟨⟨setup.program.publicationBlockLow pair.1,
        current.generation, pair.1⟩, pair.2.1, pair.2.2⟩

/-- Public control and the truthful proposal delta of one actual transition. -/
def proposalRecoveryPublic (event : setup.proposalRecoveryProtocol.StepEvent) :
    (Finset Player × Nat × Nat) × Option (ProposalRecoveryProposal L) :=
  (setup.commitRecoveryPublic event.target,
    setup.proposalRecoveryProposalOf event.source event.joint)

@[simp] theorem proposalRecoveryProposalOf_initial
    (joint : Player → Option (ProposalRecoveryMove Player L)) :
    setup.proposalRecoveryProposalOf none joint = none := rfl

@[simp] theorem proposalRecoveryPublic_control
    (event : setup.proposalRecoveryProtocol.StepEvent) :
    (setup.proposalRecoveryPublic event).1 = setup.commitRecoveryPublic event.target := rfl

end Setup
end Vegas.SourceProgram
