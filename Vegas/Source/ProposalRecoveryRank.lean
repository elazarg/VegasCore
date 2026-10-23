/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryObservation

/-! # Source ranks of actual truthful proposals -/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The proposal decoder retains the actual current source instruction rank. -/
theorem recoveryProposal_rank :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (point : ProtocolState program) (joint : Player → Option (ProposalRecoveryMove Player L))
    (rank : Nat) (value : Sigma L.Val),
    ProtocolState.recoveryProposal program point joint = some (rank, value) →
      rank = instructionCount program - ProtocolState.remaining program point := by
  intro Γ O program
  induction program with
  | ret => intro point joint rank value decoded; cases decoded
  | sample name fresh law next ih =>
      intro point joint rank value decoded
      cases point with
      | inl config => cases decoded
      | inr point =>
          obtain ⟨pair, original, same⟩ := Option.map_eq_some_iff.mp decoded
          have ranked := ih point joint pair.1 pair.2 original
          have bounded := ProtocolState.remaining_le_instructionCount next point
          have increased : pair.1 + 1 = rank := congrArg Prod.fst same
          simp only [instructionCount, ProtocolState.remaining, Sum.elim_inr]
          omega
  | commit name owner fresh guard next ih =>
      intro point joint rank value decoded
      cases point with
      | inl config => cases decoded
      | inr point =>
          obtain ⟨pair, original, same⟩ := Option.map_eq_some_iff.mp decoded
          have ranked := ih point joint pair.1 pair.2 original
          have bounded := ProtocolState.remaining_le_instructionCount next point
          have increased : pair.1 + 1 = rank := congrArg Prod.fst same
          simp only [instructionCount, ProtocolState.remaining, Sum.elim_inr]
          omega
  | reveal published owner name fresh source unresolved next ih =>
      intro point joint rank value decoded
      cases point with
      | inl config =>
          simp only [ProtocolState.recoveryProposal, Sum.elim_inl] at decoded
          split at decoded
          · cases stored : config.state.get source with
            | failure => simp only [stored] at decoded; cases decoded
            | success value =>
                simp only [stored] at decoded
                have ranked := congrArg Prod.fst (Option.some.inj decoded)
                simpa only [instructionCount, ProtocolState.remaining, Sum.elim_inl,
                  Nat.sub_self] using ranked.symm
          · cases decoded
      | inr point =>
          obtain ⟨pair, original, same⟩ := Option.map_eq_some_iff.mp decoded
          have ranked := ih point joint pair.1 pair.2 original
          have bounded := ProtocolState.remaining_le_instructionCount next point
          have increased : pair.1 + 1 = rank := congrArg Prod.fst same
          simp only [instructionCount, ProtocolState.remaining, Sum.elim_inr]
          omega

end Vegas.SourceProgram.ProtocolState
