/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryObservation
import Vegas.Source.ObservationRecall

/-! # Successful source proposals read from the original public result cells -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolView

/-- Completed successful reveals, in source order, read from their permanent
public result cells. The original view retains those cells through later
suffixes; private stored commitments are never consulted by this function. -/
def successfulProposalWord (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolView who program →
      List (Nat × Sigma L.Val)
  | _, _, .ret _, _ => []
  | _, _, .sample _ _ _ next, view => view.elim (fun _ => [])
      (fun later => (successfulProposalWord who next later).map fun pair => (pair.1 + 1, pair.2))
  | _, _, .commit _ _ _ _ next, view => view.elim (fun _ => [])
      (fun later => (successfulProposalWord who next later).map fun pair => (pair.1 + 1, pair.2))
  | _, _, .reveal (payload := payload) _ _ _ _ _ _ next, view => view.elim (fun _ => [])
      (fun later =>
        (match (entryView who next later).1.cells.get .here with
          | .failure => []
          | .success value => [(0, (⟨payload, value⟩ : Sigma L.Val))]) ++
        (successfulProposalWord who next later).map fun pair => (pair.1 + 1, pair.2))

@[simp] theorem successfulProposalWord_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (who : Player) (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    successfulProposalWord who program
      (ProtocolState.observe who program (ProtocolState.entry program config)) = [] := by
  cases program <;> rfl

end ProtocolView

omit [IExpr.ResultTypes L] in
/-- A successful publication identifies both its truthful intention and the
same typed pre-step binding, even with general source guards. -/
theorem revealSuccessor_binding_of_success
    {Γ : SourceCtx Player L} {owner : Player} {name published : VarId} {payload : L.Ty}
    (source : HasVar Γ name (.commitment owner payload))
    (config : Config Player L Γ) (disclose : Bool) (value : L.Val payload)
    (success : (revealSuccessor published source config disclose).state.get .here =
      .success value) :
    disclose = true ∧ config.state.get source = .success value := by
  cases disclose with
  | false => simp [revealSuccessor] at success
  | true =>
      simp only [revealSuccessor, Env.cons_get_here, ite_true] at success
      split at success
      · exact ⟨rfl, success⟩
      · cases success

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- Canonical generation-zero addresses of the successful proposal values
that can be read from an original source observation. -/
def proposalRecoverySuccessfulArchive (who : Player) (view : setup.ProtocolView who) :
    Finset (ProposalRecoveryProposal L) := by
  classical
  exact (view.toList.flatMap fun current =>
    (ProtocolView.successfulProposalWord who setup.program current).map fun pair =>
      (⟨⟨setup.program.publicationBlockLow pair.1, 0, pair.1⟩, pair.2.1, pair.2.2⟩ :
        ProposalRecoveryProposal L)).toFinset

end Setup
end Vegas.SourceProgram
