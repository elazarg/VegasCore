/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryObservation

/-! # Truthful proposal readback despite failed publication -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProposalRecoveryMove

/-- A failed delivery has the old withheld successor and a truthful proposal. -/
def failedDisclosure (owner : Player) (name : VarId) : ProposalRecoveryMove Player L :=
  ⟨⟨.reveal owner name false, false⟩, true⟩

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem failedDisclosure_valid (owner : Player) (name : VarId) :
    (failedDisclosure (L := L) owner name).Valid := by
  intro _
  exact ⟨owner, name, rfl⟩

omit [DecidableEq Player] [IExpr.ResultTypes L] in
@[simp] theorem failedDisclosure_discloses (owner : Player) (name : VarId) :
    (failedDisclosure (L := L) owner name).discloses = true := rfl

end ProposalRecoveryMove

namespace ProtocolState

variable {Γ : SourceCtx Player L} {O : Finset VarId}
  {published name : VarId} {owner : Player} {payload : L.Ty}
  (fresh : published ∉ Γ.map Prod.fst)
  (source : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
  (next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
  (config : Config Player L Γ)
  (joint : Player → Option (ProposalRecoveryMove Player L))

theorem recoveryProposal_reveal_success
    (exposed : ((joint owner).map (·.discloses)).getD false = true)
    (value : L.Val payload) (stored : config.state.get source = .success value) :
    recoveryProposal (.reveal published owner name fresh source unresolved next)
        (Sum.inl config) joint = some (0, ⟨payload, value⟩) := by
  simp [recoveryProposal, exposed, stored]

theorem recoveryProposal_reveal_failure (stored : config.state.get source = .failure) :
    recoveryProposal (.reveal published owner name fresh source unresolved next)
        (Sum.inl config) joint = none := by
  simp only [recoveryProposal, Sum.elim_inl, stored]
  split <;> rfl

theorem recoveryProposal_reveal_withheld
    (hidden : ((joint owner).map (·.discloses)).getD false = false) :
    recoveryProposal (.reveal published owner name fresh source unresolved next)
        (Sum.inl config) joint = none := by
  simp only [recoveryProposal, Sum.elim_inl, hidden, Bool.false_eq_true, ite_false]

end ProtocolState
end Vegas.SourceProgram
